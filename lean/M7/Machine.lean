/-! Machine M7 = 1RB---_0RC1LF_1LC1LD_1RE0RA_0RD1RF_0LD0LF, exact semantics.
Tape: `L` = cells left of the head (nearest first), `h` = scanned cell,
`R` = cells right of the head (nearest first); missing cells are blank (`false`). -/
namespace M7

inductive St | A | B | C | D | E | F | H
  deriving DecidableEq, Repr

structure Cfg where
  st : St
  L : List Bool
  h : Bool
  R : List Bool
  deriving DecidableEq, Repr

/-- write `w`, move right, enter `s` -/
def mR (s : St) (w : Bool) (c : Cfg) : Cfg := ⟨s, w :: c.L, c.R.headD false, c.R.tail⟩
/-- write `w`, move left, enter `s` -/
def mL (s : St) (w : Bool) (c : Cfg) : Cfg := ⟨s, c.L.tail, c.L.headD false, w :: c.R⟩

/-- One step. `A` scanning `1` is the undefined transition: enter `H` (halted). -/
def step (c : Cfg) : Cfg :=
  match c.st, c.h with
  | .A, false => mR .B true c
  | .A, true  => { c with st := .H }
  | .B, false => mR .C false c
  | .B, true  => mL .F true c
  | .C, false => mL .C true c
  | .C, true  => mL .D true c
  | .D, false => mR .E true c
  | .D, true  => mR .A false c
  | .E, false => mR .D false c
  | .E, true  => mR .F true c
  | .F, false => mL .D false c
  | .F, true  => mL .F false c
  | .H, _     => c

def run : Nat → Cfg → Cfg
  | 0, c => c
  | n + 1, c => run n (step c)

theorem run_add (m n : Nat) (c : Cfg) : run (m + n) c = run n (run m c) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [run]
    exact ih (step c)

def halted (c : Cfg) : Prop := c.st = .H

/-- initial configuration: blank tape, state A -/
def init : Cfg := ⟨.A, [], false, []⟩

theorem run_H (n : Nat) (c : Cfg) (h : c.st = .H) : run n c = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run]
    have : step c = c := by
      obtain ⟨s, L, x, R⟩ := c
      simp at h; subst h; cases x <;> rfl
    rw [this, ih]

end M7
