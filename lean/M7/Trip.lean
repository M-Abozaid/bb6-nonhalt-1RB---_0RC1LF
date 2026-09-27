import M7.Micro
namespace M7
open List

/-! # Trips: one left-end-to-left-end round trip of the head. -/

/-- `c` reaches `c'` in a positive number of steps -/
def Reach (c c' : Cfg) : Prop := ∃ n, 0 < n ∧ run n c = c'

theorem Reach.trans {c1 c2 c3 : Cfg} (h1 : Reach c1 c2) (h2 : Reach c2 c3) : Reach c1 c3 := by
  obtain ⟨n1, p1, e1⟩ := h1
  obtain ⟨n2, p2, e2⟩ := h2
  exact ⟨n1 + n2, by omega, by rw [run_add, e1, e2]⟩

def z4 : List Bool := [false, false, false, false]

/-- the stack of finished carry trips: tape `(101)^j` -/
def stk : Nat → List Bool
  | 0 => []
  | j + 1 => [true, false, true] ++ stk j

theorem one_stk (j : Nat) (T : List Bool) :
    true :: (stk j ++ T) = (List.flatten (replicate j [true, true, false])) ++ true :: T := by
  induction j with
  | zero => simp [stk]
  | succ j ih => simp [stk, replicate_succ, ih]

theorem rsw_bs (j : Nat) (L : List Bool) :
    rsw (replicate j Tok.b) L = List.flatten (replicate j [true, true, false]) ++ L := by
  induction j generalizing L with
  | zero => rfl
  | succ j ih =>
    rw [replicate_succ, rsw, ih]
    simp [rr]
    induction j with
    | zero => simp
    | succ k _ => simp [replicate_succ']

/-- the left-end remains of the final trip, read as remnants: `0 (101)^j 10101` =
remnants of `a b^j a a` (the leading `0` is blank tape) -/
theorem le0_rems (j : Nat) :
    [true, false, true, false, true] ++ stk j = rsw (replicate j Tok.b ++ [Tok.a, Tok.a]) [true] := by
  rw [rsw_append, rsw_bs]
  simp only [rsw, rr]
  have := one_stk j []
  simp at this
  simp [this]

theorem ls_a_blank (R : List Bool) :
    run 12 (lsc [true] R) = lsc [] (em .a ++ R) := by
  have h := frame (n := 10) (s := .D) (s' := .F) (L := []) (h := true)
    (R := [false, false, false, false]) (L' := []) (h' := true)
    (R' := [false, false, true, false]) [] R (by decide)
  rw [show 12 = 10 + 2 from rfl, run_add]
  simp only [lsc, List.nil_append, List.tail_cons, List.headD_cons] at h ⊢
  rw [h]; rfl

/-! ## trip lemmas -/

theorem le1' (L Y : List Bool) (hY : Y = true :: Y.tail) :
    run 12 ⟨.D, L, false, z4 ++ tk .a ++ Y⟩
      = ⟨.D, [false, true, false, true] ++ L, true, [false, false] ++ Y⟩ := by
  rw [hY]; exact le1 L Y.tail

theorem enc_snoc_true (ys : List Tok) (t : Tok) (Y : List Bool) :
    enc (ys ++ [t]) ++ Y = true :: (enc (ys ++ [t]) ++ Y).tail := by
  cases ys with
  | nil => cases t <;> simp [tk]
  | cons u us => cases u <;> simp [tk]

theorem enc_cons_true (ys : List Tok) (Y : List Bool) (hY : Y = true :: Y.tail) :
    enc ys ++ Y = true :: (enc ys ++ Y).tail := by
  cases ys with
  | nil => simpa using hY
  | cons u us => cases u <;> simp [tk]

/-- carry trip, growth: first token `a` removed, `101` pushed; right end: `11` -> `b` -/
theorem trip1G (L : List Bool) (ys : List Tok) (X : List Bool) :
    Reach ⟨.D, L, false, z4 ++ enc (Tok.a :: ys) ++ true :: true :: X⟩
      ⟨.D, [true, false, true] ++ L, false, z4 ++ ems ys ++ false :: X⟩ := by
  refine ⟨12 + rsNs ys + 11 + lsNs ys, by omega, ?_⟩
  rw [run_add, run_add, run_add]
  have e1 : z4 ++ enc (Tok.a :: ys) ++ true :: true :: X = z4 ++ tk .a ++ (enc ys ++ true :: true :: X) := by
    simp
  rw [e1, le1' _ _ (enc_cons_true ys _ rfl)]
  rw [show [false, false] ++ (enc ys ++ true :: true :: X) = [false, false] ++ enc ys ++ true :: true :: X by simp,
    rsweep, show [false, false] ++ true :: true :: X = [false, false, true, true] ++ X from rfl, evG, lsweep]
  rfl

/-- carry trip, translate: body ends in `b`, right end `0` -> `01` -/
theorem trip1T (L : List Bool) (ys : List Tok) (X : List Bool) :
    Reach ⟨.D, L, false, z4 ++ enc (Tok.a :: ys ++ [Tok.b]) ++ false :: X⟩
      ⟨.D, [true, false, true] ++ L, false, z4 ++ ems ys ++ [false, false, true] ++ X⟩ := by
  refine ⟨12 + (rsNs ys + 7) + 14 + lsNs ys, by omega, ?_⟩
  rw [run_add, run_add, run_add]
  have e1 : z4 ++ enc (Tok.a :: ys ++ [Tok.b]) ++ false :: X
      = z4 ++ tk .a ++ (enc (ys ++ [Tok.b]) ++ false :: X) := by simp
  rw [e1, le1' _ _ (enc_snoc_true ys Tok.b _)]
  rw [show [false, false] ++ (enc (ys ++ [Tok.b]) ++ false :: X)
      = [false, false] ++ enc (ys ++ [Tok.b]) ++ false :: X by simp, rsweep_b,
    show [false, false] ++ false :: X = [false, false, false] ++ X from rfl, evT, lsweep]
  simp [lsc, z4]

/-- final trip of an increment, growth: first token `b` removed; `(101)^j` becomes `b^j a a` -/
theorem trip0G (j : Nat) (ys : List Tok) (X : List Bool) :
    Reach ⟨.D, stk j, false, z4 ++ enc (Tok.b :: ys) ++ true :: true :: X⟩
      ⟨.D, [], false, z4 ++ ems (Tok.a :: (replicate j Tok.b ++ [Tok.a, Tok.a] ++ ys)) ++ false :: X⟩ := by
  refine ⟨7 + rsNs ys + 11 + lsNs ys + lsNs (replicate j Tok.b ++ [Tok.a, Tok.a]) + 12, by omega, ?_⟩
  rw [run_add, run_add, run_add, run_add, run_add]
  have e1 : z4 ++ enc (Tok.b :: ys) ++ true :: true :: X = z4 ++ tk .b ++ (enc ys ++ true :: true :: X) := by
    simp
  unfold z4 at e1 ⊢
  rw [e1, le0, show [false, false] ++ (enc ys ++ true :: true :: X) = [false, false] ++ enc ys ++ true :: true :: X by simp,
    rsweep, show [false, false] ++ true :: true :: X = [false, false, true, true] ++ X from rfl, evG, lsweep,
    le0_rems, lsweep, ls_a_blank]
  simp [lsc, z4]

/-- final trip of an increment, translate -/
theorem trip0T (j : Nat) (ys : List Tok) (X : List Bool) :
    Reach ⟨.D, stk j, false, z4 ++ enc (Tok.b :: ys ++ [Tok.b]) ++ false :: X⟩
      ⟨.D, [], false, z4 ++ ems (Tok.a :: (replicate j Tok.b ++ [Tok.a, Tok.a] ++ ys)) ++ [false, false, true] ++ X⟩ := by
  refine ⟨7 + (rsNs ys + 7) + 14 + lsNs ys + lsNs (replicate j Tok.b ++ [Tok.a, Tok.a]) + 12, by omega, ?_⟩
  rw [run_add, run_add, run_add, run_add, run_add]
  have e1 : z4 ++ enc (Tok.b :: ys ++ [Tok.b]) ++ false :: X
      = z4 ++ tk .b ++ (enc (ys ++ [Tok.b]) ++ false :: X) := by simp
  unfold z4 at e1 ⊢
  rw [e1, le0, show [false, false] ++ (enc (ys ++ [Tok.b]) ++ false :: X)
      = [false, false] ++ enc (ys ++ [Tok.b]) ++ false :: X by simp, rsweep_b,
    show [false, false] ++ false :: X = [false, false, false] ++ X from rfl, evT, lsweep,
    le0_rems, lsweep, ls_a_blank]
  simp [lsc, z4]

end M7
