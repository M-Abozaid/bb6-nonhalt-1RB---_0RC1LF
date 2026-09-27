# M7 Lean proof — progress notes
Machine 1RB---_0RC1LF_1LC1LD_1RE0RA_0RD1RF_0LD0LF. Build: `export PATH=$HOME/.elan/bin:$PATH; cd lean && lake build`.
No Mathlib. Toolchain v4.33.1.

## Micro structure (derived 2026-09-27 from traces, lean/trace2.py, loc.py)
Tokens a=10, b=100.  Checkpoint = D on blank, L=[], R = 0000 ++ enc(ts) ++ M, where
ts = low counter bits (1->aa, 0->b, LSB first) ++ [a,b] (top bit 1 + separator 0) ++ W.
Trip start = D scanning 0, R = 0000 ++ enc(ts) ++ M, L = (101)^j stack (j = trips done in this increment).
 LE1 (first token a): 0000 10 -> left 1010, cursor [D1]00.   LE0 (first token b): 0000 100 -> left 10101, cursor.
 RS: cursor [D1]00 moves right: a(10)->remnant 01 (12 steps, peeks next cell=1), b(100)->011 (7 steps).
 end events: G: [1]00 11 X -> head 1 left, R = 0000 0 X.  T: 011[1]00 0 X -> head 4 left, R = 0000 0 0 1 X.
 LS: head on last cell of remnant, R=0000..: 01 -> emits 10 (12 st), 011 -> emits 010 (13 st).
 stops when the next cell left is 0 (trip-1: stack grows by 101) or runs into blank (trip-0 -> checkpoint).
 Key identity: em(a::xs) ++ 0::Y = enc(xs ++ [b]) ++ Y.

## Lean progress (2026-09-27)
- M7/Machine.lean, Frame.lean (runB/frame from m23), Micro.lean (tokens, rs/ls steps, le1/le0, evG/evT,
  rsweep/lsweep by induction), Trip.lean (trip1G/T, trip0G/T), Counter.lean (bits/pcw/tzw/trips identity),
  Incr.lean (Ev/EvN, incr, ck, growth/translate epochs), OvMicro.lean (lez, skip, leg, leo2a/b, leo3b, ls3).
  All proven, no sorry. Micro windows checked by `decide` on runB (fast); symbolic tails via frame.
- Key identity: ems (a :: ys) = enc (ys ++ [a]) (left sweep output = token list shifted by one).
- Overflow micro (from lean/ovf.py exploration): after top trip, OV j W M = stk j, 0000 0 enc W M.
  O1 = Z-trips (each eats bb, T-mode) + skip + leg + final LS; O0 = skip + leg + final LS (PEND);
  O2 = leo2a + leo2b + RS/evT/LS + final LS; O3 = leo2a + leo3b + RS/evT/LS (-> OV-like with extra stack
  110101) then O2 + final LS with one length-3 remnant (ls3: 0111 -> 0010, the fossil's bare 0).
- Overflow.lean: finalLS, trip1top, ovEntry/ovEntry_ck, ztrip/ztrips, oend, o0 (PEND), o1, o2, o3 — all proven.
## Round 2 (2026-09-27): COMPLETE — `M7.nonhalt : ∀ n, ¬ halted (run n init)`
Axioms: [propext, Classical.choice, Quot.sound]. No sorry/admit/native_decide. Full `lake build` ~2.5 min (Base ~80 s).
- Arith.lean: pcw_add/zero/ones/top, endpoint popcounts with P=2^j (v_e0start, v_e0contact, v_e1contact,
  v_e1swallow), bits_e1a/b (low bits `10`/`01` at the swallow), bits_top1, trips_val (trips from trips_eq).
- Level.lean (level j <-> w0 = j+8, A = 16P, P = 2^j):
  tmpl j Q Z Rest = ck (bits (j+7) (2^(j+6)+1)) [a,b] (1^(2^(j+6)-4) ++ 0 enc(Q) 0 1^Z Rest)  (E0 at u=1).
  phaseE0: growth (A-1 incs, trips 2A-2 = whole trail) + translate (E0 contact is simply the first
    translate trip with p=0; the worn 'b' is a re-parse) + ovEntry + o1.
  swallow: 2-trip increment (G, then T after absorbing the fossil `Q0 b` into W; pure re-parse).
  phaseE1: growth (7A/4+1 incs) + swallow + translate + ovEntry.  phaseE2: o2 + translate + ovEntry + o3.
  phaseE3: translate + ovEntry(W=[]) + o0 + PEND (incr_ck from 0 with one G trip) = tmpl (j+5).
  level : Reach (tmpl j (Q0++[b]) Z Rest) (tmpl (j+5) (nq j Q0 ++ [b]) (Z + 1480*2^j + 2) Rest)
  (1480P+2 = 185A/2+2 matches room/NOTES Z-recurrence; Q never needs to start with b, only end with b.)
- Base.lean: init -> checkpoint 943 (t=1132435) in 13 kernel chunks (`decide +kernel`, <=90k steps each,
  configs as run-length lists; maxRecDepth raised), then k943 = tmpl 4 ([]++[b]) 0 Rest0 by decide +kernel,
  Rest0 = enc(a a b^28) 0 1^741.  (Chunk lemma via run_add; the old '2.6k limit' was elaborator `decide`.)
- Main.lean: reach_levels i (level 4+5i reached at step >= i), nonhalt via run_H (halting absorbing).
