import M7.OvMicro
namespace M7
open List

set_option linter.unusedSimpArgs false

/-! # Overflow transitions -/

theorem ems_a' (ys : List Tok) : ems (Tok.a :: ys) = enc (ys ++ [Tok.a]) := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    cases y
    · simp only [ems_cons, em, enc_cons, tk] at ih ⊢
      simp only [cons_append, nil_append] at ih ⊢
      simp [ih, tk]
    · simp only [ems_cons, em, enc_cons, tk] at ih ⊢
      simp only [cons_append, nil_append] at ih ⊢
      simp [ih, tk]

theorem ems_b' (ys : List Tok) : ems (Tok.b :: ys) = false :: enc (ys ++ [Tok.a]) := by
  rw [← ems_a']; simp [em]

/-- the final left sweep through a stack of remnants down to the blank left end -/
theorem finalLS (ts : List Tok) (R : List Bool) :
    ReachE (lsc (rsw ts [true]) R) ⟨.D, [], false, z4 ++ enc (ts ++ [Tok.a]) ++ R⟩ := by
  refine ⟨lsNs ts + 12, ?_⟩
  rw [run_add, lsweep, ls_a_blank]
  have : em .a ++ (ems ts ++ R) = enc (ts ++ [Tok.a]) ++ R := by
    rw [← List.append_assoc, show em .a ++ ems ts = ems (Tok.a :: ts) from rfl, ems_a']
  simp [lsc, this, z4]

theorem Ev.inv {B M B' M'} (h : Ev B M B' M') :
    (∃ X, M = true :: true :: X ∧ B' = B ++ [Tok.b] ∧ M' = X) ∨
    (∃ B0 X, B = B0 ++ [Tok.b] ∧ M = false :: X ∧ B' = B ∧ M' = false :: true :: X) := by
  cases h
  · left; exact ⟨_, rfl, rfl, rfl⟩
  · right; exact ⟨_, _, rfl, rfl, rfl, rfl⟩

theorem Ev.head_b {W M B' M'} (h : Ev (Tok.b :: W) M B' M') : ∃ W', B' = Tok.b :: W' := by
  rcases h.inv with ⟨X, _, hB', _⟩ | ⟨B0, X, hB0, _, hB', _⟩
  · exact ⟨W ++ [Tok.b], by rw [hB']; rfl⟩
  · exact ⟨W, hB'⟩

/-- the top trip of an overflow: first token `a` (top bit) followed by the separator token `b` -/
theorem trip1top {B M B' M'} (W : List Tok) (L : List Bool) (hB : B = Tok.b :: W) (h : Ev B M B' M') :
    Reach ⟨.D, L, false, z4 ++ enc (Tok.a :: B) ++ M⟩
      ⟨.D, [true, false, true] ++ L, false, z4 ++ false :: (enc B'.tail ++ M')⟩ := by
  subst hB
  rcases h.inv with ⟨X, hM, hB', hM'⟩ | ⟨B0, X, hB0, hM, hB', hM'⟩
  · rw [hM, hB', hM']
    have := trip1G L (Tok.b :: W) X
    simp only [List.append_assoc] at this
    rw [ems_b'] at this
    simpa [tk] using this
  · rw [hM, hB', hM', hB0]
    rcases B0 with _ | ⟨b0, B1⟩
    · have := trip1T L [] X
      simpa using this
    · simp at hB0
      obtain ⟨rfl, rfl⟩ := hB0
      have := trip1T L (Tok.b :: B1) X
      simp only [List.append_assoc] at this
      rw [ems_b'] at this
      simpa [tk] using this

/-- entering an overflow: all `t` low bits are 1, then the top bit; ends in `OV` -/
theorem ovEntry (t : Nat) : ∀ (j : Nat) (W : List Tok) {M B' M'}, EvN (t + 1) (Tok.b :: W) M B' M' →
    Reach ⟨.D, stk j, false, z4 ++ enc (cnt (replicate t true) ++ Tok.a :: Tok.b :: W) ++ M⟩
      (OV (j + t + 1) B'.tail M') := by
  induction t with
  | zero =>
    intro j W M B' M' h
    obtain ⟨B1, M1, h1, h2, h3⟩ := h
    subst h2 h3
    have := trip1top W (stk j) rfl h1
    simpa [OV, stk] using this
  | succ t ih =>
    intro j W M B' M' h
    obtain ⟨B1, M1, h1, h2⟩ := h
    obtain ⟨W1, rfl⟩ := h1.head_b
    have t1 := trip1 (stk j) (h1.pre (cnt (replicate t true) ++ [Tok.a]))
    have t2 := ih (j + 1) W1 h2
    rw [show [true, false, true] ++ stk j = stk (j + 1) from rfl] at t1
    rw [show j + 1 + t + 1 = j + (t + 1) + 1 by omega] at t2
    refine Reach.trans ?_ t2
    simpa [replicate_succ] using t1

theorem ovEntry_ck (w : Nat) (W : List Tok) {M B' M'} (h : EvN (w + 1) (Tok.b :: W) M B' M') :
    Reach (ck (replicate w true) (Tok.a :: Tok.b :: W) M) (OV (w + 1) B'.tail M') := by
  have := ovEntry w 0 W h
  simpa [ck, stk] using this

/-! ## O1: Z-trips -/

theorem ztrip (L : List Bool) (V : List Tok) (X : List Bool) (hV : V = [] ∨ ∃ V0, V = V0 ++ [Tok.b]) :
    Reach ⟨.D, L, false, z4 ++ false :: (enc (Tok.b :: Tok.b :: V) ++ false :: X)⟩
      ⟨.D, [true, false, true, false, true] ++ L, false, z4 ++ false :: (enc V ++ false :: true :: X)⟩ := by
  obtain ⟨ys, hys, hres⟩ : ∃ ys : List Tok, Tok.b :: V = ys ++ [Tok.b] ∧
      ems ys ++ [false, false, true] ++ X = false :: (enc V ++ false :: true :: X) := by
    rcases hV with rfl | ⟨V0, rfl⟩
    · exact ⟨[], rfl, rfl⟩
    · refine ⟨Tok.b :: V0, rfl, ?_⟩
      rw [ems_b']; simp [tk]
  refine ⟨6 + (rsNs ys + 7) + 14 + lsNs ys, by omega, ?_⟩
  rw [run_add, run_add, run_add]
  have e1 : z4 ++ false :: (enc (Tok.b :: Tok.b :: V) ++ false :: X)
      = z4 ++ false :: (tk .b ++ (enc (ys ++ [Tok.b]) ++ false :: X)) := by
    rw [← hys]; simp
  rw [e1, lez, show [false, false] ++ (enc (ys ++ [Tok.b]) ++ false :: X)
      = [false, false] ++ enc (ys ++ [Tok.b]) ++ false :: X by simp, rsweep_b,
    show [false, false] ++ false :: X = [false, false, false] ++ X from rfl, evT, lsweep]
  have hres' : ems ys ++ false :: false :: true :: X = false :: (enc V ++ false :: true :: X) := by
    simpa using hres
  simp only [lsc, List.cons_append, List.nil_append, List.tail_cons, List.headD_cons]
  rw [hres']; simp [z4]

def s5 (k : Nat) : List Bool := (replicate k [true, false, true, false, true]).flatten

theorem ztrips (k : Nat) : ∀ (L : List Bool) (p : Nat) (X : List Bool),
    ReachE ⟨.D, L, false, z4 ++ false :: (enc (replicate (2 * k) Tok.b) ++ false :: (ones p ++ X))⟩
      ⟨.D, s5 k ++ L, false, z4 ++ false :: (false :: (ones (p + k) ++ X))⟩ := by
  induction k with
  | zero => intro L p X; simpa [s5] using ReachE.refl _
  | succ k ih =>
    intro L p X
    have h1 := ztrip L (replicate (2 * k) Tok.b) (ones p ++ X) (by
      rcases k with _ | k
      · left; rfl
      · right; exact ⟨replicate (2 * k + 1) Tok.b, by rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, replicate_succ']⟩)
    have h2 := ih ([true, false, true, false, true] ++ L) (p + 1) X
    rw [show p + 1 + k = p + (k + 1) by omega] at h2
    have e : enc (replicate (2 * (k + 1)) Tok.b) = enc (Tok.b :: Tok.b :: replicate (2 * k) Tok.b) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by omega]; simp [replicate_succ]
    rw [e]
    refine h1.toE.trans ?_
    have e2 : s5 (k + 1) ++ L = s5 k ++ ([true, false, true, false, true] ++ L) := by
      simp [s5, replicate_succ']
    rw [e2]
    simpa [ones, replicate_succ] using h2

/-- the end of O0/O1: skip the double zero, left-end growth, final sweep -/
theorem oend (ts : List Tok) (L : List Bool) (hL : [true, false, true, false, true] ++ L = rsw ts [true])
    (Y : List Bool) :
    Reach ⟨.D, L, false, z4 ++ false :: false :: true :: true :: Y⟩
      ⟨.D, [], false, z4 ++ enc (ts ++ [Tok.a]) ++ Y⟩ := by
  have h1 : Reach ⟨.D, L, false, z4 ++ false :: false :: true :: true :: Y⟩
      (lsc ([true, false, true, false, true] ++ L) Y) := by
    refine ⟨2 + 10, by omega, ?_⟩
    rw [run_add, skip, leg]; rfl
  rw [hL] at h1
  exact h1.transE (finalLS ts Y)


/-! ## stacks read as remnants -/

def abk (k : Nat) : List Tok := (replicate k [Tok.a, Tok.b]).flatten

theorem rsw_one_stk (j : Nat) : rsw (replicate j Tok.b) [true] = true :: stk j := by
  rw [rsw_bs]; have := one_stk j []; simp at this; simp [this]

theorem rsw_abk (k : Nat) (T : List Bool) :
    rsw (abk k) (true :: T) = true :: (s5 k ++ T) := by
  induction k generalizing T with
  | zero => simp [abk, s5, rsw]
  | succ k ih =>
    have e : abk (k + 1) = abk k ++ [Tok.a, Tok.b] := by simp [abk, replicate_succ']
    have e2 : s5 (k + 1) = [true, false, true, false, true] ++ s5 k := by simp [s5, replicate_succ]
    rw [e, rsw_append, ih, e2]
    simp [rsw, rr]

theorem stack_o1 (j k : Nat) :
    [true, false, true, false, true] ++ (s5 k ++ stk j)
      = rsw (replicate j Tok.b ++ abk k ++ [Tok.a, Tok.a]) [true] := by
  rw [rsw_append, rsw_append, rsw_one_stk, rsw_abk]
  simp [rsw, rr]

/-! ## O0 and O1 -/

/-- O1: overflow with `W = b^(2k)` in translate mode -/
theorem o1 (j k p : Nat) (X : List Bool) (hk : 1 ≤ k) (hp : 2 ≤ p + k) :
    Reach (OV j (replicate (2 * k) Tok.b) (false :: (ones p ++ X)))
      (ck (replicate j false) (Tok.a :: Tok.b :: abk (k - 1) ++ [Tok.a, Tok.a, Tok.a]) (ones (p + k - 2) ++ X)) := by
  have h1 := ztrips k (stk j) p X
  have e : ones (p + k) ++ X = true :: true :: (ones (p + k - 2) ++ X) := by
    obtain ⟨q, hq⟩ : ∃ q, p + k = q + 2 := ⟨p + k - 2, by omega⟩
    rw [hq]; simp [ones, replicate_succ]
  rw [e] at h1
  have h2 := oend (replicate j Tok.b ++ abk k ++ [Tok.a, Tok.a]) (s5 k ++ stk j) (stack_o1 j k)
    (ones (p + k - 2) ++ X)
  have := h1.transR h2
  have ek : abk k = [Tok.a, Tok.b] ++ abk (k - 1) := by
    obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
    simp [abk, replicate_succ]
  simpa [OV, ck, cnt_zeros, ek] using this

/-- O0: overflow with empty `W` in translate mode: the PEND checkpoint -/
theorem o0 (j p : Nat) (X : List Bool) (hp : 2 ≤ p) :
    Reach (OV j [] (false :: (ones p ++ X)))
      (ck (replicate j false ++ [true]) [Tok.a] (ones (p - 2) ++ X)) := by
  have e : ones p ++ X = true :: true :: (ones (p - 2) ++ X) := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
    simp [ones, replicate_succ]
  have h2 := oend (replicate j Tok.b ++ abk 0 ++ [Tok.a, Tok.a]) (s5 0 ++ stk j) (stack_o1 j 0)
    (ones (p - 2) ++ X)
  simp only [OV, enc_nil, nil_append, e]
  simpa [ck, cnt_zeros, abk, s5] using h2

/-! ## O2 and O3 -/

/-- the O2 pass on `W = a b V0 b` (translate mode), up to the final left sweep -/
theorem o2pass (L : List Bool) (V0 : List Tok) (X : List Bool) :
    Reach ⟨.D, L, false, z4 ++ false :: (enc (Tok.a :: Tok.b :: V0 ++ [Tok.b]) ++ false :: X)⟩
      (lsc (rsw V0 ([true, false, true, true, false, true, false, true] ++ L)) ([false, false, true] ++ X)) := by
  refine ⟨11 + (5 + ((rsNs V0 + 7) + 14)), by omega, ?_⟩
  have e1 : z4 ++ false :: (enc (Tok.a :: Tok.b :: V0 ++ [Tok.b]) ++ false :: X)
      = z4 ++ false :: (tk .a ++ true :: (enc (Tok.b :: V0 ++ [Tok.b]) ++ false :: X).tail) := by
    simp [tk]
  rw [e1, run_add, leo2a]
  have e2 : [false, false] ++ true :: (enc (Tok.b :: V0 ++ [Tok.b]) ++ false :: X).tail
      = [false, false] ++ tk .b ++ (enc (V0 ++ [Tok.b]) ++ false :: X) := by simp [tk]
  rw [e2, run_add, leo2b, run_add]
  rw [show [false, false] ++ (enc (V0 ++ [Tok.b]) ++ false :: X)
      = [false, false] ++ enc (V0 ++ [Tok.b]) ++ false :: X by simp, rsweep_b,
    show [false, false] ++ false :: X = [false, false, false] ++ X from rfl, evT]
  rfl

theorem stack_o2 (j : Nat) :
    [true, false, true, true, false, true, false, true] ++ stk j
      = rsw (replicate j Tok.b ++ [Tok.a, Tok.b, Tok.a]) [true] := by
  rw [rsw_append, rsw_one_stk]; simp [rsw, rr]

/-- O2: `W = a b V0 b` -> `a V0 b` (the first `b` is deleted), translate mode kept -/
theorem o2 (j : Nat) (V0 : List Tok) (X : List Bool) :
    Reach (OV j (Tok.a :: Tok.b :: V0 ++ [Tok.b]) (false :: X))
      (ck (replicate j false) (Tok.a :: Tok.b :: Tok.a :: V0 ++ [Tok.b]) (false :: true :: X)) := by
  have h1 := o2pass (stk j) V0 X
  rw [stack_o2, ← rsw_append] at h1
  have h3 := h1.transE (finalLS _ ([false, false, true] ++ X))
  simpa [ck, cnt_zeros, tk, OV] using h3

/-- O3 phase 1: `W = a a b Z0 b` -> the stack gains `011011`, `W = Z0 b` -/
theorem o3pass (L : List Bool) (Z0 : List Tok) (X : List Bool) :
    Reach ⟨.D, L, false, z4 ++ false :: (enc (Tok.a :: Tok.a :: Tok.b :: Z0 ++ [Tok.b]) ++ false :: X)⟩
      ⟨.D, [true, true, false, true, false, true] ++ L, false,
        z4 ++ false :: (enc (Z0 ++ [Tok.b]) ++ false :: true :: X)⟩ := by
  refine ⟨11 + (10 + ((rsNs (Tok.b :: Z0) + 7) + (14 + lsNs (Tok.b :: Z0)))), by omega, ?_⟩
  have e1 : z4 ++ false :: (enc (Tok.a :: Tok.a :: Tok.b :: Z0 ++ [Tok.b]) ++ false :: X)
      = z4 ++ false :: (tk .a ++ true :: (enc (Tok.a :: Tok.b :: Z0 ++ [Tok.b]) ++ false :: X).tail) := by
    simp [tk]
  rw [e1, run_add, leo2a]
  have e2 : [false, false] ++ true :: (enc (Tok.a :: Tok.b :: Z0 ++ [Tok.b]) ++ false :: X).tail
      = [false, false] ++ tk .a ++ true :: (enc (Tok.b :: Z0 ++ [Tok.b]) ++ false :: X).tail := by simp [tk]
  rw [e2, run_add, leo3b, run_add, run_add]
  have e3 : [false, false, true] ++ (enc (Tok.b :: Z0 ++ [Tok.b]) ++ false :: X).tail
      = [false, false] ++ enc ((Tok.b :: Z0) ++ [Tok.b]) ++ false :: X := by simp [tk]
  rw [e3, rsweep_b, show [false, false] ++ false :: X = [false, false, false] ++ X from rfl, evT, lsweep]
  simp only [lsc, List.cons_append, List.nil_append, List.tail_cons, List.headD_cons]
  rw [ems_b']
  simp [z4, tk]

def rr3 : List Bool := [true, true, true, false]

theorem stack_o3 (j : Nat) :
    [true, false, true, true, false, true, false, true] ++ ([true, true, false, true, false, true] ++ stk j)
      = rsw [Tok.a, Tok.b, Tok.a] (rr3 ++ rsw (replicate j Tok.b ++ [Tok.a]) [true]) := by
  rw [rsw_append, rsw_one_stk]; simp [rsw, rr, rr3]

/-- O3: `W = a a b a b V0 b` detaches: `W` becomes empty and the medium starts with the new fossil
`0 a b a V0 b` (translate mode) -/
theorem o3 (j : Nat) (V0 : List Tok) (X : List Bool) :
    Reach (OV j (Tok.a :: Tok.a :: Tok.b :: Tok.a :: Tok.b :: V0 ++ [Tok.b]) (false :: X))
      (ck (replicate j false) [Tok.a, Tok.b]
        (false :: (enc (Tok.a :: Tok.b :: Tok.a :: V0 ++ [Tok.b]) ++ false :: true :: true :: X))) := by
  have h1 := o3pass (stk j) (Tok.a :: Tok.b :: V0) X
  have h2 := o2pass ([true, true, false, true, false, true] ++ stk j) V0 (true :: X)
  rw [stack_o3, ← rsw_append] at h2
  have h3 := lsweep ([Tok.a, Tok.b, Tok.a] ++ V0) (rr3 ++ rsw (replicate j Tok.b ++ [Tok.a]) [true])
    ([false, false, true] ++ true :: X)
  have h4 := ls3 (rsw (replicate j Tok.b ++ [Tok.a]) [true])
    (ems ([Tok.a, Tok.b, Tok.a] ++ V0) ++ ([false, false, true] ++ true :: X))
  have h5 := finalLS (replicate j Tok.b ++ [Tok.a])
    ([false, false, true, false] ++ (ems ([Tok.a, Tok.b, Tok.a] ++ V0) ++ ([false, false, true] ++ true :: X)))
  have h1' : Reach (OV j (Tok.a :: Tok.a :: Tok.b :: Tok.a :: Tok.b :: V0 ++ [Tok.b]) (false :: X))
      ⟨.D, [true, true, false, true, false, true] ++ stk j, false,
        z4 ++ false :: (enc (Tok.a :: Tok.b :: V0 ++ [Tok.b]) ++ false :: true :: X)⟩ := by
    simpa [OV] using h1
  have h345 : ReachE (lsc (rsw ([Tok.a, Tok.b, Tok.a] ++ V0) (rr3 ++ rsw (replicate j Tok.b ++ [Tok.a]) [true]))
      ([false, false, true] ++ true :: X)) _ :=
    ReachE.trans ⟨_, h3⟩ (ReachE.trans ⟨_, h4⟩ h5)
  have := h1'.transE (h2.toE.trans h345)
  refine (by simpa using this : Reach _ _) |> fun h => ?_
  have hfin : z4 ++ enc (replicate j Tok.b ++ [Tok.a] ++ [Tok.a]) ++
      ([false, false, true, false] ++ (ems ([Tok.a, Tok.b, Tok.a] ++ V0) ++ ([false, false, true] ++ true :: X)))
      = z4 ++ enc (cnt (replicate j false) ++ [Tok.a, Tok.b]) ++
        false :: (enc (Tok.a :: Tok.b :: Tok.a :: V0 ++ [Tok.b]) ++ false :: true :: true :: X) := by
    have e : ems ([Tok.a, Tok.b, Tok.a] ++ V0) ++ ([false, false, true] ++ true :: X)
        = enc ([Tok.b, Tok.a] ++ V0 ++ [Tok.b]) ++ false :: true :: true :: X := by
      rw [show [Tok.a, Tok.b, Tok.a] ++ V0 = Tok.a :: ([Tok.b, Tok.a] ++ V0) from rfl, ems_a']
      simp [tk]
    rw [e, cnt_zeros]; simp [tk, z4]
  unfold ck; rw [← hfin]
  simpa using this

end M7
