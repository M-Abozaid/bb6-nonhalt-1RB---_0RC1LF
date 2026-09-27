namespace M7
open List

/-! # Binary counter arithmetic (LSB first, fixed width). -/

/-- `bits w n`: the low `w` bits of `n`, least significant first -/
def bits : Nat → Nat → List Bool
  | 0, _ => []
  | w + 1, n => (n % 2 == 1) :: bits w (n / 2)

@[simp] theorem bits_length (w n : Nat) : (bits w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [bits, ih]

/-- population count at width `w` -/
def pcw (w n : Nat) : Nat := (bits w n).count true

/-- number of trailing ones -/
def tzw (w n : Nat) : Nat := ((bits w n).takeWhile id).length

theorem bits_zero (w : Nat) : bits w 0 = replicate w false := by
  induction w with
  | zero => rfl
  | succ w ih => simp [bits, ih, replicate_succ]

theorem pow_pos' (w : Nat) : 0 < 2 ^ w := Nat.pow_pos (by decide)

theorem bits_ones (w : Nat) : bits w (2 ^ w - 1) = replicate w true := by
  induction w with
  | zero => rfl
  | succ w ih =>
    have h1 : (2 ^ (w + 1) - 1) % 2 = 1 := by
      have := pow_pos' w; rw [Nat.pow_succ]; omega
    have h2 : (2 ^ (w + 1) - 1) / 2 = 2 ^ w - 1 := by
      have := pow_pos' w; rw [Nat.pow_succ]; omega
    simp [bits, h1, h2, ih, replicate_succ]

/-- concatenation of bit fields -/
theorem bits_add (a b x y : Nat) (hx : x < 2 ^ a) :
    bits (a + b) (x + 2 ^ a * y) = bits a x ++ bits b y := by
  induction a generalizing x with
  | zero =>
    have : x = 0 := by simp at hx; omega
    subst this; simp [bits]
  | succ a ih =>
    rw [Nat.add_right_comm, bits]
    have hp : 2 ^ (a + 1) = 2 * 2 ^ a := by rw [Nat.pow_succ, Nat.mul_comm]
    have h1 : (x + 2 ^ (a + 1) * y) % 2 = x % 2 := by
      rw [hp, Nat.mul_assoc]; omega
    have h2 : (x + 2 ^ (a + 1) * y) / 2 = x / 2 + 2 ^ a * y := by
      rw [hp, Nat.mul_assoc]; omega
    have hx' : x / 2 < 2 ^ a := by rw [hp] at hx; omega
    rw [h1, h2, ih _ hx']
    rfl

/-- increment: `1^t 0 rest -> 0^t 1 rest` -/
theorem bits_succ (w n : Nat) (h : n + 1 < 2 ^ w) :
    ∃ rest, bits w n = replicate (tzw w n) true ++ false :: rest ∧
      bits w (n + 1) = replicate (tzw w n) false ++ true :: rest := by
  induction w generalizing n with
  | zero => simp at h
  | succ w ih =>
    rcases Nat.mod_two_eq_zero_or_one n with h0 | h0
    · refine ⟨bits w (n / 2), ?_, ?_⟩
      · simp [tzw, bits, h0]
      · have e1 : (n + 1) % 2 = 1 := by omega
        have e2 : (n + 1) / 2 = n / 2 := by omega
        simp [tzw, bits, h0, e1, e2]
    · have hn : n / 2 + 1 < 2 ^ w := by rw [Nat.pow_succ] at h; omega
      obtain ⟨rest, r1, r2⟩ := ih (n / 2) hn
      refine ⟨rest, ?_, ?_⟩
      · simp only [tzw, bits, h0] at r1 ⊢
        rw [r1]
        simp [replicate_succ, takeWhile_append, takeWhile_replicate]
      · have e1 : (n + 1) % 2 = 0 := by omega
        have e2 : (n + 1) / 2 = n / 2 + 1 := by omega
        simp only [tzw, bits, h0, e1, e2] at r1 r2 ⊢
        rw [r2, r1]
        simp [replicate_succ, takeWhile_append, takeWhile_replicate]

theorem pcw_succ (w n : Nat) (h : n + 1 < 2 ^ w) : pcw w (n + 1) + tzw w n = pcw w n + 1 := by
  obtain ⟨rest, r1, r2⟩ := bits_succ w n h
  unfold pcw
  rw [r2, r1]
  simp [count_replicate]
  omega

/-- total trips of `k` increments starting at `n` -/
def trips (w n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (tzw w n + 1) + trips w (n + 1) k

theorem trips_eq (w n k : Nat) (h : n + k < 2 ^ w) :
    trips w n k + pcw w (n + k) = pcw w n + 2 * k := by
  induction k generalizing n with
  | zero => simp [trips]
  | succ k ih =>
    have h1 := pcw_succ w n (by omega)
    have h2 := ih (n + 1) (by omega)
    simp only [trips]
    rw [show n + (k + 1) = n + 1 + k by omega]
    omega

end M7
