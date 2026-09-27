import M7.Overflow
import M7.Arith
namespace M7
open List

set_option linter.unusedSimpArgs false

/-! # The level cycle E0 -> E1 -> E2 -> E3 -> E4 -> E0' (P = 2^j, A = 16P, w0 = j+8) -/

theorem b_comm (n : Nat) : Tok.b :: replicate n Tok.b = replicate n Tok.b ++ [Tok.b] := by
  rw [← replicate_succ, replicate_succ']

theorem Reach.cast {c1 c2 c1' c2' : Cfg} (h : Reach c1 c2) (e1 : c1' = c1) (e2 : c2 = c2') :
    Reach c1' c2' := by subst e1 e2; exact h
theorem ReachE.cast {c1 c2 c1' c2' : Cfg} (h : ReachE c1 c2) (e1 : c1' = c1) (e2 : c2 = c2') :
    ReachE c1' c2' := by subst e1 e2; exact h

/-- the fossil tail: `0 Q 0 1^Z Rest` -/
def T0 (Q : List Tok) (Z : Nat) (Rest : List Bool) : List Bool := false :: (enc Q ++ false :: (ones Z ++ Rest))

/-- E0 checkpoint at `u = 1`: counter `1 0^(j+5) 1 | 1`, empty `W`, trail `1^(64P-4)` -/
def tmpl (j : Nat) (Q : List Tok) (Z : Nat) (Rest : List Bool) : Cfg :=
  ck (bits (j + 7) (2 ^ (j + 6) + 1)) [Tok.a, Tok.b] (ones (2 ^ (j + 6) - 4) ++ T0 Q Z Rest)

theorem ones_add (m n : Nat) : ones (m + n) = ones m ++ ones n := by simp [ones, ← replicate_append_replicate]

theorem lt_pow (j : Nat) : j < 2 ^ j := Nat.lt_two_pow_self

/-- E0: growth (E0-G), contact + translate (E0-T), overflow O1 -/
theorem phaseE0 (j : Nat) (Q : List Tok) (Z : Nat) (Rest : List Bool) :
    Reach (tmpl j Q Z Rest)
      (ck (replicate (j + 8) false) (Tok.a :: Tok.b :: abk (16 * 2 ^ j - 2) ++ [Tok.a, Tok.a, Tok.a])
        (ones (112 * 2 ^ j - 2) ++ (enc Q ++ false :: (ones Z ++ Rest)))) := by
  have hP := pow_pos' j
  have hj := lt_pow j
  have e6 : 2 ^ (j + 6) = 64 * 2 ^ j := pw j 6
  have e7 : 2 ^ (j + 7) = 128 * 2 ^ j := pw j 7
  generalize hX : enc Q ++ false :: (ones Z ++ Rest) = X
  -- E0-G
  have t1 : trips (j + 7) (64 * 2 ^ j + 1) (16 * 2 ^ j - 1) = 32 * 2 ^ j - 2 := by
    apply trips_val _ _ _ _ (by omega)
    rw [show 64 * 2 ^ j + 1 + (16 * 2 ^ j - 1) = 80 * 2 ^ j by omega, v_e0start, v_e0contact]; omega
  have g := growth (j + 7) (16 * 2 ^ j - 1) (64 * 2 ^ j + 1) [Tok.a, Tok.b] (32 * 2 ^ j - 2) (false :: X)
    (by omega) (by omega)
  rw [t1, show 64 * 2 ^ j + 1 + (16 * 2 ^ j - 1) = 80 * 2 ^ j by omega, Nat.sub_self, Nat.mul_zero] at g
  -- E0-T (the contact is the first translate trip, with `p = 0`)
  have t2 : trips (j + 7) (80 * 2 ^ j) (48 * 2 ^ j - 1) = 96 * 2 ^ j - (j + 7) := by
    apply trips_val _ _ _ _ (by omega)
    rw [show 80 * 2 ^ j + (48 * 2 ^ j - 1) = 2 ^ (j + 7) - 1 by omega, v_e0contact, pcw_ones]; omega
  have tr := translate (j + 7) (48 * 2 ^ j - 1) (80 * 2 ^ j) (Tok.a :: replicate (32 * 2 ^ j - 2) Tok.b) 0 X
    (by omega)
  rw [t2, show 80 * 2 ^ j + (48 * 2 ^ j - 1) = 2 ^ (j + 7) - 1 by omega, bits_ones, Nat.zero_add] at tr
  -- overflow entry
  have ev := evN_T (j + 7 + 1) (replicate (32 * 2 ^ j - 2) Tok.b) (96 * 2 ^ j - (j + 7)) X
  rw [← b_comm] at ev
  have ov := ovEntry_ck (j + 7) (replicate (32 * 2 ^ j - 2) Tok.b) ev
  -- O1
  have o := o1 (j + 7 + 1) (16 * 2 ^ j - 1) (96 * 2 ^ j - (j + 7) + (j + 7 + 1)) X (by omega) (by omega)
  have s1 : ReachE (tmpl j Q Z Rest) _ := ReachE.cast (g.trans (ReachE.cast tr ?_ rfl)) ?_ rfl
  · refine s1.transR (Reach.trans (Reach.cast ov ?_ rfl) (Reach.cast o ?_ ?_))
    · simp [cons_append, append_assoc, b_comm]
    · simp only [List.tail_cons]
      rw [show 2 * (16 * 2 ^ j - 1) = 32 * 2 ^ j - 2 by omega]
    · rw [show 16 * 2 ^ j - 1 - 1 = 16 * 2 ^ j - 2 by omega,
        show 96 * 2 ^ j - (j + 7) + (j + 7 + 1) + (16 * 2 ^ j - 1) - 2 = 112 * 2 ^ j - 2 by omega]
  · simp [ones, b_comm]
  · unfold tmpl T0
    rw [e6, show 64 * 2 ^ j - 4 = 2 * (32 * 2 ^ j - 2) by omega, hX]

/-- the E1 swallow increment (low bits `1 0 rest`, one carry): the carry trip eats the last `11` of the
trail (G); the final trip absorbs the whole fossil `Q0 b` into `W` and translates (T) -/
theorem swallow (rest : List Bool) (B Q0 : List Tok) (Y : List Bool) :
    Reach (ck (true :: false :: rest) B (ones 2 ++ (enc (Q0 ++ [Tok.b]) ++ false :: Y)))
      (ck (false :: true :: rest) (B ++ [Tok.b] ++ Q0 ++ [Tok.b]) (false :: true :: Y)) := by
  have h1 := trip1 [] (Ev.g (Tok.b :: cnt rest ++ B) (enc (Q0 ++ [Tok.b]) ++ false :: Y))
  have h2 := trip0 1 (Ev.t (cnt rest ++ B ++ [Tok.b] ++ Q0) Y)
  refine Reach.trans (Reach.cast h1 ?_ rfl) (Reach.cast h2 ?_ ?_)
  · simp [ck, ones, append_assoc]
  · simp [stk, append_assoc]
  · simp [ck, append_assoc]

/-- E1: growth (E1-G), swallow, translate (E1-T), overflow entry -/
theorem phaseE1 (j : Nat) (Q0 : List Tok) (Z : Nat) (Rest : List Bool) :
    Reach (ck (replicate (j + 8) false) (Tok.a :: Tok.b :: abk (16 * 2 ^ j - 2) ++ [Tok.a, Tok.a, Tok.a])
        (ones (112 * 2 ^ j - 2) ++ (enc (Q0 ++ [Tok.b]) ++ false :: (ones Z ++ Rest))))
      (OV (j + 9) (abk (16 * 2 ^ j - 2) ++ [Tok.a, Tok.a, Tok.a] ++ replicate (56 * 2 ^ j - 1) Tok.b ++ Q0 ++ [Tok.b])
        (false :: (ones (Z + 456 * 2 ^ j) ++ Rest))) := by
  have hP := pow_pos' j
  have hj := lt_pow j
  have e8 : 2 ^ (j + 8) = 256 * 2 ^ j := pw j 8
  generalize hW1 : Tok.a :: Tok.b :: abk (16 * 2 ^ j - 2) ++ [Tok.a, Tok.a, Tok.a] = W1
  -- E1-G
  have t1 : trips (j + 8) 0 (28 * 2 ^ j + 1) = 56 * 2 ^ j - 2 := by
    apply trips_val _ _ _ _ (by omega)
    rw [Nat.zero_add, v_e1contact, pcw_zero]; omega
  have g := growth (j + 8) (28 * 2 ^ j + 1) 0 W1 (56 * 2 ^ j - 1)
    (enc (Q0 ++ [Tok.b]) ++ false :: (ones Z ++ Rest)) (by omega) (by omega)
  rw [t1, Nat.zero_add, bits_zero, show 56 * 2 ^ j - 1 - (56 * 2 ^ j - 2) = 1 by omega, bits_e1a] at g
  -- swallow
  have sw := swallow (bits (j + 6) (7 * 2 ^ j)) (W1 ++ replicate (56 * 2 ^ j - 2) Tok.b) Q0 (ones Z ++ Rest)
  rw [← bits_e1b] at sw
  -- E1-T
  have t2 : trips (j + 8) (28 * 2 ^ j + 2) (228 * 2 ^ j - 3) = 456 * 2 ^ j - (j + 10) := by
    apply trips_val _ _ _ _ (by omega)
    rw [show 28 * 2 ^ j + 2 + (228 * 2 ^ j - 3) = 2 ^ (j + 8) - 1 by omega, v_e1swallow, pcw_ones]; omega
  have tr := translate (j + 8) (228 * 2 ^ j - 3) (28 * 2 ^ j + 2)
    (W1 ++ replicate (56 * 2 ^ j - 1) Tok.b ++ Q0) (Z + 1) Rest (by omega)
  rw [t2, show 28 * 2 ^ j + 2 + (228 * 2 ^ j - 3) = 2 ^ (j + 8) - 1 by omega, bits_ones] at tr
  -- overflow entry
  have ev := evN_T (j + 8 + 1)
    (Tok.b :: (abk (16 * 2 ^ j - 2) ++ [Tok.a, Tok.a, Tok.a] ++ replicate (56 * 2 ^ j - 1) Tok.b ++ Q0))
    (Z + 1 + (456 * 2 ^ j - (j + 10))) Rest
  have ov := ovEntry_ck (j + 8)
    (abk (16 * 2 ^ j - 2) ++ [Tok.a, Tok.a, Tok.a] ++ replicate (56 * 2 ^ j - 1) Tok.b ++ Q0 ++ [Tok.b])
    (by simpa [append_assoc] using ev)
  rw [show 112 * 2 ^ j - 2 = 2 * (56 * 2 ^ j - 1) by omega]
  refine (g.transR (Reach.trans sw ?_))
  refine (ReachE.transR (ReachE.cast tr ?_ rfl) (Reach.cast ov ?_ ?_))
  · have e : 56 * 2 ^ j - 1 = (56 * 2 ^ j - 2) + 1 := by omega
    rw [show ones (Z + 1) = true :: ones Z from rfl]
    simp [e, replicate_succ', append_assoc]
  · rw [← hW1]; simp [append_assoc]
  · simp only [List.tail_cons]
    rw [show Z + 1 + (456 * 2 ^ j - (j + 10)) + (j + 8 + 1) = Z + 456 * 2 ^ j by omega]
    simp [append_assoc]

theorem abk_succ (k : Nat) : abk (k + 1) = Tok.a :: Tok.b :: abk k := by simp [abk, replicate_succ]

/-- the fossil born at the O3 overflow of the level (without its final `b`) -/
def nq (j : Nat) (Q0 : List Tok) : List Tok :=
  Tok.b :: Tok.a :: (abk (16 * 2 ^ j - 5) ++ [Tok.a, Tok.a, Tok.a] ++ replicate (56 * 2 ^ j - 1) Tok.b ++ Q0)

/-- O2 (delete the first `b`), E2 (pure translate), overflow entry, O3 (W detaches as the new fossil) -/
theorem phaseE2 (j : Nat) (Q0 : List Tok) (Y : Nat) (Rest : List Bool) :
    Reach (OV (j + 9) (abk (16 * 2 ^ j - 2) ++ [Tok.a, Tok.a, Tok.a] ++ replicate (56 * 2 ^ j - 1) Tok.b ++ Q0 ++ [Tok.b])
        (false :: (ones Y ++ Rest)))
      (ck (replicate (j + 10) false) [Tok.a, Tok.b]
        (false :: (enc (Tok.a :: (nq j Q0 ++ [Tok.b])) ++ false :: (ones (Y + 1024 * 2 ^ j + 2) ++ Rest)))) := by
  have hP := pow_pos' j
  have hj := lt_pow j
  have e9 : 2 ^ (j + 9) = 512 * 2 ^ j := pw j 9
  have ek2 : abk (16 * 2 ^ j - 2) = Tok.a :: Tok.b :: abk (16 * 2 ^ j - 3) := by
    rw [show 16 * 2 ^ j - 2 = (16 * 2 ^ j - 3) + 1 by omega, abk_succ]
  have ek3 : abk (16 * 2 ^ j - 3) = Tok.a :: Tok.b :: Tok.a :: Tok.b :: abk (16 * 2 ^ j - 5) := by
    rw [show 16 * 2 ^ j - 3 = (16 * 2 ^ j - 5) + 1 + 1 by omega, abk_succ, abk_succ]
  generalize hV1 : abk (16 * 2 ^ j - 5) ++ [Tok.a, Tok.a, Tok.a] ++ replicate (56 * 2 ^ j - 1) Tok.b ++ Q0 = V1
  -- O2
  have h2 := o2 (j + 9) (Tok.a :: Tok.b :: Tok.a :: Tok.b :: V1) (ones Y ++ Rest)
  -- E2
  have t1 : trips (j + 9) 0 (512 * 2 ^ j - 1) = 1024 * 2 ^ j - (j + 11) := by
    apply trips_val _ _ _ _ (by omega)
    rw [Nat.zero_add, pcw_zero, show 512 * 2 ^ j - 1 = 2 ^ (j + 9) - 1 by omega, pcw_ones]; omega
  have tr := translate (j + 9) (512 * 2 ^ j - 1) 0
    (Tok.a :: Tok.b :: Tok.a :: Tok.a :: Tok.b :: Tok.a :: Tok.b :: V1) (Y + 1) Rest (by omega)
  rw [t1, Nat.zero_add, show 512 * 2 ^ j - 1 = 2 ^ (j + 9) - 1 by omega, bits_ones, bits_zero] at tr
  -- overflow entry
  have ev := evN_T (j + 9 + 1) (Tok.b :: Tok.a :: Tok.a :: Tok.b :: Tok.a :: Tok.b :: V1)
    (Y + 1 + (1024 * 2 ^ j - (j + 11))) Rest
  have ov := ovEntry_ck (j + 9) (Tok.a :: Tok.a :: Tok.b :: Tok.a :: Tok.b :: V1 ++ [Tok.b])
    (by simpa [append_assoc] using ev)
  -- O3
  have h3 := o3 (j + 9 + 1) V1 (ones (Y + 1024 * 2 ^ j) ++ Rest)
  have x1 : Reach (OV (j + 9) (abk (16 * 2 ^ j - 2) ++ [Tok.a, Tok.a, Tok.a] ++ replicate (56 * 2 ^ j - 1) Tok.b
        ++ Q0 ++ [Tok.b]) (false :: (ones Y ++ Rest)))
      (ck (replicate (j + 9) false) (Tok.a :: Tok.b :: Tok.a :: Tok.a :: Tok.b :: Tok.a :: Tok.b :: V1 ++ [Tok.b])
        (false :: (ones (Y + 1) ++ Rest))) := by
    refine Reach.cast h2 ?_ ?_
    · rw [ek2, ek3, ← hV1]; simp [append_assoc]
    · rw [show ones (Y + 1) = true :: ones Y from rfl]; simp [append_assoc]
  have x2 : Reach (ck (replicate (j + 9) true)
        (Tok.a :: Tok.b :: Tok.a :: Tok.a :: Tok.b :: Tok.a :: Tok.b :: V1 ++ [Tok.b])
        (false :: (ones (Y + 1 + (1024 * 2 ^ j - (j + 11))) ++ Rest)))
      (ck (replicate (j + 10) false) [Tok.a, Tok.b]
        (false :: (enc (Tok.a :: (nq j Q0 ++ [Tok.b])) ++ false :: (ones (Y + 1024 * 2 ^ j + 2) ++ Rest)))) := by
    refine Reach.trans (Reach.cast ov ?_ rfl) (Reach.cast h3 ?_ ?_)
    · simp [append_assoc]
    · simp only [List.tail_cons]
      rw [show Y + 1 + (1024 * 2 ^ j - (j + 11)) + (j + 9 + 1) = Y + 1024 * 2 ^ j by omega]
      simp [append_assoc]
    · rw [show Y + 1024 * 2 ^ j + 2 = (Y + 1024 * 2 ^ j) + 1 + 1 from rfl]
      simp [nq, ← hV1, ones, replicate_succ, append_assoc]
  exact x1.trans (ReachE.transR tr x2)

theorem tzw_zero (w : Nat) : tzw (w + 1) 0 = 0 := by simp [tzw, bits, bits_zero]

/-- E3 (pure translate), overflow entry with empty W, O0, PEND: the next level's E0 template -/
theorem phaseE3 (j : Nat) (Q0 : List Tok) (Z : Nat) (Rest : List Bool) :
    Reach (ck (replicate (j + 10) false) [Tok.a, Tok.b]
        (false :: (enc (Tok.a :: (Q0 ++ [Tok.b])) ++ false :: (ones Z ++ Rest))))
      (tmpl (j + 5) (Q0 ++ [Tok.b]) Z Rest) := by
  have hP := pow_pos' j
  have hj := lt_pow j
  have e10 : 2 ^ (j + 10) = 1024 * 2 ^ j := pw j 10
  have e11 : 2 ^ (j + 11) = 2048 * 2 ^ j := pw j 11
  generalize hX : enc (Tok.a :: (Q0 ++ [Tok.b])) ++ false :: (ones Z ++ Rest) = X
  have t1 : trips (j + 10) 0 (1024 * 2 ^ j - 1) = 2048 * 2 ^ j - (j + 12) := by
    apply trips_val _ _ _ _ (by omega)
    rw [Nat.zero_add, pcw_zero, show 1024 * 2 ^ j - 1 = 2 ^ (j + 10) - 1 by omega, pcw_ones]; omega
  have tr := translate (j + 10) (1024 * 2 ^ j - 1) 0 [Tok.a] 0 X (by omega)
  rw [t1, Nat.zero_add, show 1024 * 2 ^ j - 1 = 2 ^ (j + 10) - 1 by omega, bits_ones, bits_zero] at tr
  have ev := evN_T (j + 10 + 1) [] (2048 * 2 ^ j - (j + 12)) X
  have ov := ovEntry_ck (j + 10) [] (by simpa using ev)
  have h0 := o0 (j + 10 + 1) (2048 * 2 ^ j - (j + 12) + (j + 10 + 1)) X (by omega)
  -- PEND: one increment from 0 with a growth trip
  have ev1 : EvN (tzw (j + 11) 0 + 1) [Tok.a, Tok.a, Tok.a] (true :: true :: (ones (2048 * 2 ^ j - 5) ++ X))
      [Tok.a, Tok.a, Tok.a, Tok.b] (ones (2048 * 2 ^ j - 5) ++ X) := by
    rw [show j + 11 = (j + 10) + 1 from rfl, tzw_zero]
    exact ⟨_, _, Ev.g _ _, rfl, rfl⟩
  have pend := incr_ck (j + 11) 0 (by omega) ev1
  refine ReachE.transR (ReachE.cast tr ?_ rfl)
    (Reach.trans (Reach.cast ov ?_ rfl) (Reach.trans h0 (Reach.cast pend ?_ ?_)))
  · simp [ones]
  · simp
  · rw [bits_zero, show 2048 * 2 ^ j - (j + 12) + (j + 10 + 1) - 2 = (2048 * 2 ^ j - 5) + 2 by omega]
    simp [ck, cnt_append, ones, replicate_succ, append_assoc]
  · unfold tmpl T0
    rw [show j + 5 + 7 = (j + 10) + 2 from rfl, show j + 5 + 6 = (j + 10) + 1 from rfl, bits_top1,
      show 1 = 0 + 1 from rfl, show j + 11 = (j + 10) + 1 from rfl, bits_one',
      show (j + 10) + 1 = j + 11 from rfl, e11, ← hX,
      show 2048 * 2 ^ j - 4 = (2048 * 2 ^ j - 5) + 1 by omega, ones_add]
    simp [ck, cnt_append, cnt_zeros, ones, append_assoc, tk]

/-- **The level theorem**: the E0 template at level `j` reaches the E0 template at level `j + 5`. -/
theorem level (j : Nat) (Q0 : List Tok) (Z : Nat) (Rest : List Bool) :
    Reach (tmpl j (Q0 ++ [Tok.b]) Z Rest) (tmpl (j + 5) (nq j Q0 ++ [Tok.b]) (Z + 1480 * 2 ^ j + 2) Rest) := by
  have h0 := phaseE0 j (Q0 ++ [Tok.b]) Z Rest
  have h1 := phaseE1 j Q0 Z Rest
  have h2 := phaseE2 j Q0 (Z + 456 * 2 ^ j) Rest
  have h3 := phaseE3 j (nq j Q0) (Z + 1480 * 2 ^ j + 2) Rest
  rw [show Z + 456 * 2 ^ j + 1024 * 2 ^ j + 2 = Z + 1480 * 2 ^ j + 2 by omega] at h2
  exact h0.trans (h1.trans (h2.trans h3))

end M7
