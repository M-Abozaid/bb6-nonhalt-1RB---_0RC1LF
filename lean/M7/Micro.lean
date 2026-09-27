import M7.Machine
import M7.Frame
namespace M7
open List

/-! # Micro layer: tokens, sweeps, end events. -/

inductive Tok | a | b
  deriving DecidableEq, Repr

/-- tape encoding of a token: a = 10, b = 100 -/
def tk : Tok → List Bool
  | .a => [true, false]
  | .b => [true, false, false]

def enc (ts : List Tok) : List Bool := ts.flatMap tk

@[simp] theorem enc_nil : enc [] = [] := rfl
@[simp] theorem enc_cons (t : Tok) (ts : List Tok) : enc (t :: ts) = tk t ++ enc ts := by
  simp [enc]
@[simp] theorem enc_append (s t : List Tok) : enc (s ++ t) = enc s ++ enc t := by
  simp [enc]

/-- remnant left behind by the right sweep (nearest cell first): a -> tape 01, b -> tape 011 -/
def rr : Tok → List Bool
  | .a => [true, false]
  | .b => [true, true, false]

/-- emission of the left sweep (tape order): a -> 10, b -> 010 -/
def em : Tok → List Bool
  | .a => [true, false]
  | .b => [false, true, false]

def ems (ts : List Tok) : List Bool := ts.flatMap em

@[simp] theorem ems_nil : ems [] = [] := rfl
@[simp] theorem ems_cons (t : Tok) (ts : List Tok) : ems (t :: ts) = em t ++ ems ts := by
  simp [ems]
@[simp] theorem ems_append (s t : List Tok) : ems (s ++ t) = ems s ++ ems t := by
  simp [ems]

/-- left list after the right sweep over `ts` -/
def rsw : List Tok → List Bool → List Bool
  | [], L => L
  | t :: ts, L => rsw ts (rr t ++ L)

theorem rsw_append (s t : List Tok) (L : List Bool) : rsw (s ++ t) L = rsw t (rsw s L) := by
  induction s generalizing L with
  | nil => rfl
  | cons x s ih => simp [rsw, ih]

/-- steps of the right sweep -/
def rsN : Tok → Nat
  | .a => 12
  | .b => 7

def rsNs (ts : List Tok) : Nat := (ts.map rsN).sum

def lsN : Tok → Nat
  | .a => 12
  | .b => 13

def lsNs (ts : List Tok) : Nat := (ts.map lsN).sum

/-- left-sweep configuration: head on the first cell of `LH`, then `0000 ++ R` -/
def lsc (LH R : List Bool) : Cfg := ⟨.D, LH.tail, LH.headD false, [false, false, false, false] ++ R⟩

/-- key regrouping identity: the left sweep's output re-read as tokens -/
theorem ems_a (xs : List Tok) (Y : List Bool) :
    ems (Tok.a :: xs) ++ false :: Y = enc (xs ++ [Tok.b]) ++ Y := by
  induction xs with
  | nil => simp [em, tk]
  | cons x xs ih =>
    cases x
    · simp only [ems_cons, em, enc_cons, cons_append, tk] at ih ⊢
      simp only [nil_append, cons.injEq, true_and] at ih ⊢
      simp [ih]
    · simp only [ems_cons, em, enc_cons, cons_append, tk] at ih ⊢
      simp only [nil_append, cons.injEq, true_and] at ih ⊢
      simp [ih]

/-! ## single-token sweep steps (kernel-checked windows, arbitrary surroundings) -/

theorem rs_a (L R : List Bool) :
    run 12 ⟨.D, L, true, [false, false] ++ tk .a ++ true :: R⟩
      = ⟨.D, rr .a ++ L, true, [false, false] ++ true :: R⟩ := by
  have h := frame (n := 12) (s := .D) (s' := .D) (L := []) (h := true)
    (R := [false, false, true, false, true]) (L' := [true, false]) (h' := true)
    (R' := [false, false, true]) L R (by decide)
  simpa [tk, rr] using h

theorem rs_b (L R : List Bool) :
    run 7 ⟨.D, L, true, [false, false] ++ tk .b ++ R⟩
      = ⟨.D, rr .b ++ L, true, [false, false] ++ R⟩ := by
  have h := frame (n := 7) (s := .D) (s' := .D) (L := []) (h := true)
    (R := [false, false, true, false, false]) (L' := [true, true, false]) (h' := true)
    (R' := [false, false]) L R (by decide)
  simpa [tk, rr] using h

/-- final step of every leftward walk: `F` on `0` moves left into `D`, whatever is there -/
theorem fstep (L R : List Bool) : run 1 ⟨.F, L, false, R⟩ = ⟨.D, L.tail, L.headD false, false :: R⟩ := rfl

theorem ls_a (L R : List Bool) : run 12 (lsc (rr .a ++ L) R) = lsc L (em .a ++ R) := by
  have h := frame (n := 11) (s := .D) (s' := .F) (L := [false]) (h := true)
    (R := [false, false, false, false]) (L' := []) (h' := false)
    (R' := [false, false, false, true, false]) L R (by decide)
  rw [show 12 = 11 + 1 from rfl, run_add]
  simp only [lsc, rr, em, List.cons_append, List.nil_append, List.tail_cons, List.headD_cons] at h ⊢
  rw [h, fstep]

theorem ls_b (L R : List Bool) : run 13 (lsc (rr .b ++ L) R) = lsc L (em .b ++ R) := by
  have h := frame (n := 12) (s := .D) (s' := .F) (L := [true, false]) (h := true)
    (R := [false, false, false, false]) (L' := []) (h' := false)
    (R' := [false, false, false, false, true, false]) L R (by decide)
  rw [show 13 = 12 + 1 from rfl, run_add]
  simp only [lsc, rr, em, List.cons_append, List.nil_append, List.tail_cons, List.headD_cons] at h ⊢
  rw [h, fstep]

/-! ## left-end starts and right-end events -/

/-- trip start on token `a`: the head cell and `0000` absorb the `a` and become `1010` + cursor -/
theorem le1 (L R : List Bool) :
    run 12 ⟨.D, L, false, [false, false, false, false] ++ tk .a ++ true :: R⟩
      = ⟨.D, [false, true, false, true] ++ L, true, [false, false, true] ++ R⟩ := by
  have h := frame (n := 12) (s := .D) (s' := .D) (L := []) (h := false)
    (R := [false, false, false, false, true, false, true]) (L' := [false, true, false, true]) (h' := true)
    (R' := [false, false, true]) L R (by decide)
  simpa [tk] using h

/-- trip start on token `b`: becomes `10101` + cursor -/
theorem le0 (L R : List Bool) :
    run 7 ⟨.D, L, false, [false, false, false, false] ++ tk .b ++ R⟩
      = ⟨.D, [true, false, true, false, true] ++ L, true, [false, false] ++ R⟩ := by
  have h := frame (n := 7) (s := .D) (s' := .D) (L := []) (h := false)
    (R := [false, false, false, false, true, false, false]) (L' := [true, false, true, false, true]) (h' := true)
    (R' := [false, false]) L R (by decide)
  simpa [tk] using h

/-- growth event: cursor meets `11`; the `11` become the cursor's `b`, left sweep begins -/
theorem evG (L X : List Bool) :
    run 11 ⟨.D, L, true, [false, false, true, true] ++ X⟩ = lsc L (false :: X) := by
  have h := frame (n := 10) (s := .D) (s' := .F) (L := []) (h := true)
    (R := [false, false, true, true]) (L' := []) (h' := false)
    (R' := [false, false, false, false]) L X (by decide)
  rw [show 11 = 10 + 1 from rfl, run_add]
  simp only [List.nil_append] at h
  rw [h, fstep]; rfl

/-- translate event: the last token `b` (remnant `011`) and the cursor meet `0`: a `1` is inserted -/
theorem evT (L X : List Bool) :
    run 14 ⟨.D, rr .b ++ L, true, [false, false, false] ++ X⟩
      = lsc L ([false, false, true] ++ X) := by
  have h := frame (n := 13) (s := .D) (s' := .F) (L := [true, true, false]) (h := true)
    (R := [false, false, false]) (L' := []) (h' := false)
    (R' := [false, false, false, false, false, true]) L X (by decide)
  rw [show 14 = 13 + 1 from rfl, run_add]
  simp only [rr, List.cons_append, List.nil_append] at h ⊢
  rw [h, fstep]; rfl

/-! ## sweeps -/

/-- right sweep over any token list, provided the cell after it is `1` -/
theorem rsweep (ts : List Tok) (L R : List Bool) :
    run (rsNs ts) ⟨.D, L, true, [false, false] ++ enc ts ++ true :: R⟩
      = ⟨.D, rsw ts L, true, [false, false] ++ true :: R⟩ := by
  induction ts generalizing L with
  | nil => rfl
  | cons t ts ih =>
    simp only [rsNs, List.map_cons, List.sum_cons, rsN] at ih ⊢
    rw [run_add]
    cases t
    · have e : [false, false] ++ enc (Tok.a :: ts) ++ true :: R
          = [false, false] ++ tk .a ++ (enc ts ++ true :: R) := by simp
      rcases ts with _ | ⟨u, us⟩
      · simp only [enc_nil, List.nil_append] at e ⊢
        rw [show [false, false] ++ enc [Tok.a] ++ true :: R = [false, false] ++ tk .a ++ true :: R by simp [tk]]
        rw [rs_a]; rfl
      · have hu : enc (u :: us) ++ true :: R = true :: (enc (u :: us) ++ true :: R).tail := by
          cases u <;> simp [tk]
        rw [e, hu, rs_a, ← hu]
        exact ih _
    · have e : [false, false] ++ enc (Tok.b :: ts) ++ true :: R
          = [false, false] ++ tk .b ++ (enc ts ++ true :: R) := by simp
      rw [e, rs_b]
      simpa [rsw] using ih (rr .b ++ L)

/-- right sweep over a list ending in `b`: no condition on what follows -/
theorem rsweep_b (ts : List Tok) (L R : List Bool) :
    run (rsNs ts + 7) ⟨.D, L, true, [false, false] ++ enc (ts ++ [Tok.b]) ++ R⟩
      = ⟨.D, rr .b ++ rsw ts L, true, [false, false] ++ R⟩ := by
  rw [run_add]
  have e : [false, false] ++ enc (ts ++ [Tok.b]) ++ R
      = [false, false] ++ enc ts ++ true :: ([false, false] ++ R) := by simp [tk]
  rw [e, rsweep]
  have e2 : [false, false] ++ true :: ([false, false] ++ R) = [false, false] ++ tk .b ++ R := by simp [tk]
  rw [e2, rs_b]

/-- left sweep over the remnants of any token list -/
theorem lsweep (ts : List Tok) (L R : List Bool) :
    run (lsNs ts) (lsc (rsw ts L) R) = lsc L (ems ts ++ R) := by
  induction ts generalizing L R with
  | nil => rfl
  | cons t ts ih =>
    simp only [lsNs, List.map_cons, List.sum_cons, rsw, lsN] at ih ⊢
    rw [Nat.add_comm, run_add, ih]
    cases t
    · rw [ls_a]; simp
    · rw [ls_b]; simp

end M7
