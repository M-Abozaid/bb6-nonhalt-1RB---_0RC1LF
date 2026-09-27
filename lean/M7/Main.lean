import M7.Base
namespace M7

/-! # Nonhalting of M7 -/

/-- level invariant: the E0 template at level `j`, for some fossil `Q0 b`, trail `Z`, far tape `Rest` -/
def Inv (j : Nat) (c : Cfg) : Prop := ∃ Q0 Z Rest, c = tmpl j (Q0 ++ [Tok.b]) Z Rest

theorem reach_levels (i : Nat) : ∃ n c, run n init = c ∧ Inv (4 + 5 * i) c ∧ i ≤ n := by
  induction i with
  | zero =>
    obtain ⟨n, hn⟩ := base
    exact ⟨n, _, hn, ⟨[], 0, Rest0, rfl⟩, Nat.zero_le _⟩
  | succ i ih =>
    obtain ⟨n, c, hn, ⟨Q0, Z, Rest, rfl⟩, hi⟩ := ih
    obtain ⟨m, hm, e⟩ := level (4 + 5 * i) Q0 Z Rest
    refine ⟨n + m, _, by rw [run_add, hn, e],
      ⟨nq (4 + 5 * i) Q0, Z + 1480 * 2 ^ (4 + 5 * i) + 2, Rest, ?_⟩, by omega⟩
    rw [show 4 + 5 * (i + 1) = 4 + 5 * i + 5 by omega]

theorem nonhalt : ∀ n, ¬ halted (run n init) := by
  intro n hn
  obtain ⟨m, c, hm, ⟨Q0, Z, Rest, rfl⟩, hle⟩ := reach_levels n
  have e : run m init = run (m - n) (run n init) := by
    rw [← run_add]; congr 1; omega
  rw [run_H _ _ hn, hm] at e
  have : (run n init).st = St.D := by rw [← e]; rfl
  unfold halted at hn
  rw [hn] at this
  cases this

end M7
