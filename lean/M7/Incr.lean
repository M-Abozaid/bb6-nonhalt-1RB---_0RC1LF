import M7.Trip
import M7.Counter
namespace M7
open List

set_option linter.unusedSimpArgs false

/-! # Increments and epochs -/

/-- reachability in zero or more steps -/
def ReachE (c c' : Cfg) : Prop := ∃ n, run n c = c'

theorem ReachE.refl (c : Cfg) : ReachE c c := ⟨0, rfl⟩
theorem ReachE.trans {c1 c2 c3 : Cfg} (h1 : ReachE c1 c2) (h2 : ReachE c2 c3) : ReachE c1 c3 := by
  obtain ⟨n1, e1⟩ := h1; obtain ⟨n2, e2⟩ := h2
  exact ⟨n1 + n2, by rw [run_add, e1, e2]⟩
theorem Reach.toE {c1 c2 : Cfg} (h : Reach c1 c2) : ReachE c1 c2 := by
  obtain ⟨n, _, e⟩ := h; exact ⟨n, e⟩
theorem Reach.transE {c1 c2 c3 : Cfg} (h1 : Reach c1 c2) (h2 : ReachE c2 c3) : Reach c1 c3 := by
  obtain ⟨n1, p1, e1⟩ := h1; obtain ⟨n2, e2⟩ := h2
  exact ⟨n1 + n2, by omega, by rw [run_add, e1, e2]⟩
theorem ReachE.transR {c1 c2 c3 : Cfg} (h1 : ReachE c1 c2) (h2 : Reach c2 c3) : Reach c1 c3 := by
  obtain ⟨n1, e1⟩ := h1; obtain ⟨n2, p2, e2⟩ := h2
  exact ⟨n1 + n2, by omega, by rw [run_add, e1, e2]⟩

/-- right-end event of one trip, on the token list `B` after the removed first token -/
inductive Ev : List Tok → List Bool → List Tok → List Bool → Prop
  | g (B : List Tok) (X : List Bool) : Ev B (true :: true :: X) (B ++ [Tok.b]) X
  | t (B : List Tok) (X : List Bool) : Ev (B ++ [Tok.b]) (false :: X) (B ++ [Tok.b]) (false :: true :: X)

theorem Ev.pre {B M B' M'} (P : List Tok) (h : Ev B M B' M') : Ev (P ++ B) M (P ++ B') M' := by
  match h with
  | .g B0 X0 => simpa using Ev.g (P ++ B0) X0
  | .t B0 X0 => simpa using Ev.t (P ++ B0) X0

/-- `n` consecutive events -/
def EvN : Nat → List Tok → List Bool → List Tok → List Bool → Prop
  | 0, B, M, B', M' => B' = B ∧ M' = M
  | n + 1, B, M, B'', M'' => ∃ B' M', Ev B M B' M' ∧ EvN n B' M' B'' M''

theorem EvN.pre (n : Nat) (P : List Tok) : ∀ {B M B' M'}, EvN n B M B' M' → EvN n (P ++ B) M (P ++ B') M' := by
  induction n with
  | zero => intro B M B' M' h; obtain ⟨h1, h2⟩ := h; subst h1 h2; exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro B M B' M' h
    obtain ⟨B1, M1, h1, h2⟩ := h
    exact ⟨P ++ B1, M1, h1.pre P, ih h2⟩

theorem ems_b (xs : List Tok) (Y : List Bool) :
    ems (Tok.b :: xs) ++ false :: Y = false :: (enc (xs ++ [Tok.b]) ++ Y) := by
  rw [← ems_a]; simp [em]

theorem trip1 {B M B' M'} (L : List Bool) (h : Ev B M B' M') :
    Reach ⟨.D, L, false, z4 ++ enc (Tok.a :: Tok.a :: B) ++ M⟩
      ⟨.D, [true, false, true] ++ L, false, z4 ++ enc B' ++ M'⟩ := by
  match h with
  | .g B X =>
    have := trip1G L (Tok.a :: B) X
    simp only [List.append_assoc] at this
    rw [ems_a] at this
    simpa using this
  | .t B X =>
    have := trip1T L (Tok.a :: B) X
    simp only [List.append_assoc, List.cons_append, List.nil_append] at this
    rw [ems_a] at this
    simpa using this

theorem trip0 {B M B' M'} (j : Nat) (h : Ev B M B' M') :
    Reach ⟨.D, stk j, false, z4 ++ enc (Tok.b :: B) ++ M⟩
      ⟨.D, [], false, z4 ++ enc (replicate j Tok.b ++ [Tok.a, Tok.a] ++ B') ++ M'⟩ := by
  match h with
  | .g B X =>
    have := trip0G j B X
    simp only [List.append_assoc] at this
    rw [ems_a] at this
    simpa using this
  | .t B X =>
    have := trip0T j B X
    simp only [List.append_assoc, List.cons_append, List.nil_append] at this
    rw [ems_a] at this
    simpa using this

/-- counter tokens of the low bits: 1 -> aa, 0 -> b -/
def cnt (C : List Bool) : List Tok := C.flatMap (fun x => if x then [Tok.a, Tok.a] else [Tok.b])

@[simp] theorem cnt_nil : cnt [] = [] := rfl
@[simp] theorem cnt_cons (x : Bool) (C : List Bool) :
    cnt (x :: C) = (if x then [Tok.a, Tok.a] else [Tok.b]) ++ cnt C := by simp [cnt]
@[simp] theorem cnt_append (C D : List Bool) : cnt (C ++ D) = cnt C ++ cnt D := by simp [cnt]
theorem cnt_zeros (j : Nat) : cnt (replicate j false) = replicate j Tok.b := by
  induction j with
  | zero => rfl
  | succ j ih => simp [replicate_succ, ih]

/-- one increment: `t` carry trips and the final trip, each with its right-end event -/
theorem incr (t : Nat) : ∀ (j : Nat) (rest : List Bool) {B M B' M'}, EvN (t + 1) B M B' M' →
    Reach ⟨.D, stk j, false, z4 ++ enc (cnt (replicate t true ++ false :: rest) ++ B) ++ M⟩
      ⟨.D, [], false, z4 ++ enc (cnt (replicate (j + t) false ++ true :: rest) ++ B') ++ M'⟩ := by
  induction t with
  | zero =>
    intro j rest B M B' M' h
    obtain ⟨B1, M1, h1, h2, h3⟩ := h
    subst h2 h3
    have := trip0 j (h1.pre (cnt rest))
    simpa [cnt_zeros] using this
  | succ t ih =>
    intro j rest B M B' M' h
    obtain ⟨B1, M1, h1, h2⟩ := h
    have t1 := trip1 (stk j) (h1.pre (cnt (replicate t true ++ false :: rest)))
    have t2 := ih (j + 1) rest h2
    rw [show [true, false, true] ++ stk j = stk (j + 1) from rfl] at t1
    have e : j + 1 + t = j + (t + 1) := by omega
    rw [e] at t2
    have := Reach.trans t1 (by simpa using t2)
    simpa [replicate_succ] using this

/-- checkpoint: blank left, head on blank, `0000`, low counter bits, token list `B`, medium `M` -/
def ck (C : List Bool) (B : List Tok) (M : List Bool) : Cfg :=
  ⟨.D, [], false, z4 ++ enc (cnt C ++ B) ++ M⟩

theorem incr_ck (w n : Nat) (hn : n + 1 < 2 ^ w) {B M B' M'} (h : EvN (tzw w n + 1) B M B' M') :
    Reach (ck (bits w n) B M) (ck (bits w (n + 1)) B' M') := by
  obtain ⟨rest, r1, r2⟩ := bits_succ w n hn
  have := incr (tzw w n) 0 rest h
  simp only [Nat.zero_add] at this
  unfold ck; rw [r1, r2]; exact this

/-! ## event sequences of the two modes -/

def ones (n : Nat) : List Bool := replicate n true

theorem evN_G (f : Nat) : ∀ (B : List Tok) (m : Nat) (X : List Bool), f ≤ m →
    EvN f B (ones (2 * m) ++ X) (B ++ replicate f Tok.b) (ones (2 * (m - f)) ++ X) := by
  induction f with
  | zero => intro B m X _; simp [EvN]
  | succ f ih =>
    intro B m X hf
    refine ⟨B ++ [Tok.b], ones (2 * (m - 1)) ++ X, ?_, ?_⟩
    · have e : ones (2 * m) ++ X = true :: true :: (ones (2 * (m - 1)) ++ X) := by
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        simp [ones, Nat.mul_succ, replicate_succ]
      rw [e]; exact Ev.g _ _
    · have := ih (B ++ [Tok.b]) (m - 1) X (by omega)
      rw [show m - 1 - f = m - (f + 1) by omega] at this
      simpa [replicate_succ] using this

theorem evN_T (f : Nat) : ∀ (B0 : List Tok) (p : Nat) (X : List Bool),
    EvN f (B0 ++ [Tok.b]) (false :: (ones p ++ X)) (B0 ++ [Tok.b]) (false :: (ones (p + f) ++ X)) := by
  induction f with
  | zero => intro B0 p X; simp [EvN]
  | succ f ih =>
    intro B0 p X
    refine ⟨B0 ++ [Tok.b], false :: (ones (p + 1) ++ X), ?_, ?_⟩
    · have := Ev.t B0 (ones p ++ X)
      simpa [ones, replicate_succ] using this
    · have := ih B0 (p + 1) X
      rwa [show p + 1 + f = p + (f + 1) by omega] at this

/-! ## epochs -/

theorem growth (w : Nat) (k : Nat) : ∀ (n : Nat) (B : List Tok) (m : Nat) (X : List Bool),
    n + k < 2 ^ w → trips w n k ≤ m →
    ReachE (ck (bits w n) B (ones (2 * m) ++ X))
      (ck (bits w (n + k)) (B ++ replicate (trips w n k) Tok.b) (ones (2 * (m - trips w n k)) ++ X)) := by
  induction k with
  | zero => intro n B m X _ _; simpa [trips] using ReachE.refl _
  | succ k ih =>
    intro n B m X hn ht
    simp only [trips] at ht ⊢
    have s1 := incr_ck w n (by omega) (evN_G (tzw w n + 1) B m X (by omega))
    have s2 := ih (n + 1) (B ++ replicate (tzw w n + 1) Tok.b) (m - (tzw w n + 1)) X (by omega) (by omega)
    rw [show n + 1 + k = n + (k + 1) by omega, show m - (tzw w n + 1) - trips w (n + 1) k
      = m - (tzw w n + 1 + trips w (n + 1) k) by omega] at s2
    refine s1.toE.trans ?_
    simpa [← replicate_append_replicate] using s2

theorem translate (w : Nat) (k : Nat) : ∀ (n : Nat) (B0 : List Tok) (p : Nat) (X : List Bool),
    n + k < 2 ^ w →
    ReachE (ck (bits w n) (B0 ++ [Tok.b]) (false :: (ones p ++ X)))
      (ck (bits w (n + k)) (B0 ++ [Tok.b]) (false :: (ones (p + trips w n k) ++ X))) := by
  induction k with
  | zero => intro n B0 p X _; simpa [trips] using ReachE.refl _
  | succ k ih =>
    intro n B0 p X hn
    simp only [trips]
    have s1 := incr_ck w n (by omega) (evN_T (tzw w n + 1) B0 p X)
    have s2 := ih (n + 1) B0 (p + (tzw w n + 1)) X (by omega)
    rw [show n + 1 + k = n + (k + 1) by omega, show p + (tzw w n + 1) + trips w (n + 1) k
      = p + (tzw w n + 1 + trips w (n + 1) k) by omega] at s2
    exact s1.toE.trans s2

end M7
