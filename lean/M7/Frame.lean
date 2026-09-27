import M7.Machine

namespace M7

/-! ## Bounded runs with arbitrary far tape (`runB` / `runB_frame`), as in m23/M4.
`runB` runs on explicit finite lists and fails (`none`) if the head would leave them;
a successful `runB` run holds for every extension of the lists. -/

/-- direction of the move taken from `(s, x)`: `some true` right, `some false` left,
`none` no move (halt). -/
def mvDir : St → Bool → Option Bool
  | .A, false => some true
  | .A, true => none
  | .B, false => some true
  | .B, true => some false
  | .C, _ => some false
  | .D, _ => some true
  | .E, _ => some true
  | .F, _ => some false
  | .H, _ => none

def stepB (c : Cfg) : Option Cfg :=
  match mvDir c.st c.h with
  | some true => if c.R.isEmpty then none else some (step c)
  | some false => if c.L.isEmpty then none else some (step c)
  | none => some (step c)

def runB : Nat → Cfg → Option Cfg
  | 0, c => some c
  | n + 1, c => (stepB c).bind (runB n)

def ext (c : Cfg) (Lt Rt : List Bool) : Cfg := ⟨c.st, c.L ++ Lt, c.h, c.R ++ Rt⟩

theorem stepB_frame {c c' : Cfg} (Lt Rt : List Bool) (h : stepB c = some c') :
    step (ext c Lt Rt) = ext c' Lt Rt := by
  obtain ⟨s, L, x, R⟩ := c
  cases s <;> cases x <;> simp only [stepB, mvDir] at h <;>
    first
    | (cases R with
        | nil => simp at h
        | cons r rs => simp at h; subst h; simp [ext, step, mR])
    | (cases L with
        | nil => simp at h
        | cons l ls => simp at h; subst h; simp [ext, step, mL])
    | (simp at h; subst h; simp [ext, step])

theorem runB_frame (n : Nat) (Lt Rt : List Bool) :
    ∀ {c c' : Cfg}, runB n c = some c' → run n (ext c Lt Rt) = ext c' Lt Rt := by
  induction n with
  | zero => intro c c' h; simp [runB] at h; subst h; rfl
  | succ n ih =>
    intro c c' h
    simp only [runB, Option.bind_eq_some_iff] at h
    obtain ⟨c1, h1, h2⟩ := h
    show run n (step (ext c Lt Rt)) = _
    rw [stepB_frame Lt Rt h1]
    exact ih h2

/-- convenience: a concrete window run, extended by arbitrary left/right tapes -/
theorem frame {n : Nat} {s s' : St} {L h R L' h' R'} (Lt Rt : List Bool)
    (hb : runB n ⟨s, L, h, R⟩ = some ⟨s', L', h', R'⟩) :
    run n ⟨s, L ++ Lt, h, R ++ Rt⟩ = ⟨s', L' ++ Lt, h', R' ++ Rt⟩ :=
  runB_frame n Lt Rt hb

end M7
