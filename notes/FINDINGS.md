# 1RB---_0RC1LF_1LC1LD_1RE0RA_0RD1RF_0LD0LF  ("Translated Counter")  — deep cryptid check 2026-09-26
Notation a=10, b=100.
- Checkpoint: head at new leftmost cell in state D, one per increment.
  Tape: [D]0000 · COUNTER · W · 1^n0 · F1 · 1^n1 · F2 … 0 a b^28 0 1^741
- Counter: fixed width w, LSB left, bit0=100, bit1=1010, +1 per checkpoint; word moves 2 left/increment.
- Modes: growth (W right end eats trail: two 1s -> one b), translate (leaves trail of 1s),
  contact with fossil (worn down or swallowed, by trail-length parity), overflow (w+1 or w+2; detach -> fossil).
- Multi-level: fossils + trails nest; trail lengths ~ 2^(w-2)*const. Real run to 2.6e11 (epochs*.txt).
- HALT iff D reads 1 with 1 to its right (A only via D1->0RA). Routes H1/H2, both need '11' => only at trail boundaries.
- Sweeps (~106k exact sims, runs/): distance/fossil/block sweeps 0 halts (~75k).
  Halts ONLY in region: overflow during growth epoch starting with empty W within k* ~ n/8 increments
  (k*=8,32,59,124,248,497,998 for n=100..8000); sharp inequality boundary, no isolated points.
  Repro: repro/halt_counter_c943.in (counter 4095 halts @6535; 3972 halts; 3971 runs).
- Real run: each empty-W growth epoch has room ~n (1023 vs 1020 @w=12; 32767 vs 32764 @w=17) ~ 8x k*.
- Verdict: PROMISING with caveats. Proof plan: macro rules + contact table; fossils in finite template family;
  prove epoch schedule gives room >= n/8 (risk: schedule depends on parity-dependent contacts).
