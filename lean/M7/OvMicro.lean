import M7.Incr
namespace M7
open List

set_option linter.unusedSimpArgs false

/-! # Micro lemmas for overflow handling -/

/-- the configuration after the top trip of an overflow: stack `(101)^j`, then `0000 0 W M` -/
def OV (j : Nat) (W : List Tok) (M : List Bool) : Cfg :=
  ⟨.D, stk j, false, z4 ++ false :: (enc W ++ M)⟩

/-- Z-start on `b`: `0000 0 100` -> left `101010`, cursor -/
theorem lez (L R : List Bool) :
    run 6 ⟨.D, L, false, z4 ++ false :: (tk .b ++ R)⟩
      = ⟨.D, [false, true, false, true, false, true] ++ L, true, [false, false] ++ R⟩ := by
  have h := frame (n := 6) (s := .D) (s' := .D) (L := []) (h := false)
    (R := [false, false, false, false, false, true, false, false]) (L' := [false, true, false, true, false, true]) (h' := true)
    (R' := [false, false]) L R (by decide)
  simpa [tk, z4] using h

/-- skip: `0000 0 0` -> left `10` -/
theorem skip (L R : List Bool) :
    run 2 ⟨.D, L, false, z4 ++ false :: false :: R⟩
      = ⟨.D, [false, true] ++ L, false, z4 ++ R⟩ := by
  have h := frame (n := 2) (s := .D) (s' := .D) (L := []) (h := false)
    (R := [false, false, false, false, false, false]) (L' := [false, true]) (h' := false)
    (R' := [false, false, false, false]) L R (by decide)
  simpa [z4] using h

/-- left-end growth: `0000 11` -> left `10`, head on a new `1`, left sweep begins -/
theorem leg (L Y : List Bool) :
    run 10 ⟨.D, L, false, z4 ++ true :: true :: Y⟩ = lsc (true :: [false, true] ++ L) Y := by
  have h := frame (n := 10) (s := .D) (s' := .D) (L := []) (h := false)
    (R := [false, false, false, false, true, true]) (L' := [false, true]) (h' := true)
    (R' := [false, false, false, false]) L Y (by decide)
  simpa [z4, lsc] using h

/-- O2/O3 start, part 1: `0000 0 10` -> left `10101`, head on `0`, then `00` -/
theorem leo2a (L R : List Bool) :
    run 11 ⟨.D, L, false, z4 ++ false :: (tk .a ++ true :: R)⟩
      = ⟨.D, [true, false, true, false, true] ++ L, false, [false, false] ++ true :: R⟩ := by
  have h := frame (n := 11) (s := .D) (s' := .D) (L := []) (h := false)
    (R := [false, false, false, false, false, true, false, true]) (L' := [true, false, true, false, true]) (h' := false)
    (R' := [false, false, true]) L R (by decide)
  simpa [tk, z4] using h

/-- O2 start, part 2: `[0] 00 100` -> left `101`, cursor -/
theorem leo2b (L R : List Bool) :
    run 5 ⟨.D, L, false, [false, false] ++ tk .b ++ R⟩
      = ⟨.D, [true, false, true] ++ L, true, [false, false] ++ R⟩ := by
  have h := frame (n := 5) (s := .D) (s' := .D) (L := []) (h := false)
    (R := [false, false, true, false, false]) (L' := [true, false, true]) (h' := true)
    (R' := [false, false]) L R (by decide)
  simpa [tk] using h

/-- O3 start, part 2: `[0] 00 10 1` -> left `10`, cursor -/
theorem leo3b (L R : List Bool) :
    run 10 ⟨.D, L, false, [false, false] ++ tk .a ++ true :: R⟩
      = ⟨.D, [false, true] ++ L, true, [false, false, true] ++ R⟩ := by
  have h := frame (n := 10) (s := .D) (s' := .D) (L := []) (h := false)
    (R := [false, false, true, false, true]) (L' := [false, true]) (h' := true)
    (R' := [false, false, true]) L R (by decide)
  simpa [tk] using h

/-- left-sweep step over a length-3 remnant `0111`: emits `0010` -/
theorem ls3 (L R : List Bool) :
    run 14 (lsc ([true, true, true, false] ++ L) R) = lsc L ([false, false, true, false] ++ R) := by
  have h := frame (n := 13) (s := .D) (s' := .F) (L := [true, true, false]) (h := true)
    (R := [false, false, false, false]) (L' := []) (h' := false)
    (R' := [false, false, false, false, false, true, false]) L R (by decide)
  rw [show 14 = 13 + 1 from rfl, run_add]
  simp only [lsc, List.cons_append, List.nil_append, List.tail_cons, List.headD_cons] at h ⊢
  rw [h, fstep]

end M7
