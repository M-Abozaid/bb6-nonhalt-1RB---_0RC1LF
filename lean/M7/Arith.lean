import M7.Counter
namespace M7
open List
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! # Popcount values at the epoch endpoints (P = 2^j) -/

theorem pw (j c : Nat) : 2 ^ (j + c) = 2 ^ c * 2 ^ j := by
  rw [Nat.pow_add, Nat.mul_comm]

theorem pcw_add (a b x y : Nat) (hx : x < 2 ^ a) :
    pcw (a + b) (x + 2 ^ a * y) = pcw a x + pcw b y := by
  unfold pcw; rw [bits_add a b x y hx, List.count_append]

theorem pcw_zero (w : Nat) : pcw w 0 = 0 := by
  unfold pcw; rw [bits_zero]; simp [List.count_replicate]

theorem pcw_ones (w : Nat) : pcw w (2 ^ w - 1) = w := by
  unfold pcw; rw [bits_ones]; simp [List.count_replicate]

theorem pcw_one (b : Nat) : pcw (b + 1) 1 = 1 := by
  unfold pcw; simp [bits, bits_zero, List.count_replicate]

theorem pcw_top (a b : Nat) : pcw (a + (b + 1)) (2 ^ a) = 1 := by
  have := pcw_add a (b + 1) 0 1 (pow_pos' a)
  simp only [Nat.zero_add, Nat.mul_one] at this
  rw [this, pcw_zero, pcw_one]

/-- `x + 2^a * P`-shaped values with `x < 2^a` a small constant and `y` a small constant times `2^j` -/
theorem pcw_mulP (j c y : Nat) (hy : y < 2 ^ c) : pcw (j + c) (2 ^ j * y) = pcw c y := by
  have := pcw_add j c 0 y (pow_pos' j)
  rw [Nat.zero_add, pcw_zero, Nat.zero_add] at this
  exact this
  -- (hy unused but documents the range)

theorem v_e0start (j : Nat) : pcw (j + 7) (64 * 2 ^ j + 1) = 2 := by
  have h := pcw_add 1 (j + 6) 1 (2 ^ (j + 5)) (by decide)
  have e1 : 1 + 2 ^ 1 * 2 ^ (j + 5) = 64 * 2 ^ j + 1 := by rw [pw j 5]; simp; omega
  rw [e1, show 1 + (j + 6) = j + 7 by omega, pcw_top (j + 5) 0] at h
  rw [h]; rfl

theorem v_e0contact (j : Nat) : pcw (j + 7) (80 * 2 ^ j) = 2 := by
  have h := pcw_mulP j 7 80 (by decide)
  rw [Nat.mul_comm] at h; rw [h]; decide

theorem v_e1contact (j : Nat) : pcw (j + 8) (28 * 2 ^ j + 1) = 4 := by
  have h := pcw_add 2 (j + 6) 1 (7 * 2 ^ j) (by decide)
  have h2 := pcw_mulP j 6 7 (by decide)
  rw [show 1 + 2 ^ 2 * (7 * 2 ^ j) = 28 * 2 ^ j + 1 by simp; omega, show 2 + (j + 6) = j + 8 by omega,
    Nat.mul_comm 7, h2] at h
  rw [h]; decide

theorem v_e1swallow (j : Nat) : pcw (j + 8) (28 * 2 ^ j + 2) = 4 := by
  have h := pcw_add 2 (j + 6) 2 (7 * 2 ^ j) (by decide)
  have h2 := pcw_mulP j 6 7 (by decide)
  rw [show 2 + 2 ^ 2 * (7 * 2 ^ j) = 28 * 2 ^ j + 2 by simp; omega, show 2 + (j + 6) = j + 8 by omega,
    Nat.mul_comm 7, h2] at h
  rw [h]; decide

theorem bits_e1a (j : Nat) : bits (j + 8) (28 * 2 ^ j + 1) = true :: false :: bits (j + 6) (7 * 2 ^ j) := by
  have h := bits_add 2 (j + 6) 1 (7 * 2 ^ j) (by decide)
  rw [show 1 + 2 ^ 2 * (7 * 2 ^ j) = 28 * 2 ^ j + 1 by simp; omega, show 2 + (j + 6) = j + 8 by omega] at h
  rw [h]; rfl

theorem bits_e1b (j : Nat) : bits (j + 8) (28 * 2 ^ j + 2) = false :: true :: bits (j + 6) (7 * 2 ^ j) := by
  have h := bits_add 2 (j + 6) 2 (7 * 2 ^ j) (by decide)
  rw [show 2 + 2 ^ 2 * (7 * 2 ^ j) = 28 * 2 ^ j + 2 by simp; omega, show 2 + (j + 6) = j + 8 by omega] at h
  rw [h]; rfl

theorem bits_one' (w : Nat) : bits (w + 1) 1 = true :: replicate w false := by
  simp [bits, bits_zero]

theorem bits_top1 (a : Nat) : bits (a + 2) (2 ^ (a + 1) + 1) = true :: (replicate a false ++ [true]) := by
  have h1 : (2 ^ (a + 1) + 1) % 2 = 1 := by rw [Nat.pow_succ]; omega
  have h2 : (2 ^ (a + 1) + 1) / 2 = 0 + 2 ^ a * 1 := by rw [Nat.pow_succ]; omega
  have h3 := bits_add a 1 0 1 (pow_pos' a)
  show ((2 ^ (a + 1) + 1) % 2 == 1) :: bits (a + 1) ((2 ^ (a + 1) + 1) / 2) = _
  rw [h1, h2, h3, bits_zero]
  simp [bits, bits_zero]

/-- trips from the popcount identity -/
theorem trips_val (w n k v : Nat) (h : n + k < 2 ^ w) (hv : pcw w n + 2 * k = v + pcw w (n + k)) :
    trips w n k = v := by
  have := trips_eq w n k h; omega

end M7
