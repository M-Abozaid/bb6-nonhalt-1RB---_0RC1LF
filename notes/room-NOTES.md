# M7 room analysis (2026-09-27) — working notes
Goal: formula for counter value / trail length n at start of every empty-W growth epoch; decide STRUCTURAL vs ARITHMETIC.

## Initial observation from epochs_long.txt
Empty-W epochs with long trail occur at w=12 (c=943), w=17 (c=30639), w=22 (c=980911):
counter (LSB-left) = 1 + 2^(w-2) + 2^(w-1), n = 2^(w-2) - 4, room to overflow 2^w = 2^(w-2) - 1 = n+3.
The value is fixed by w (not by prior arithmetic) at these three. Need to explain why and check all other epochs.

## Epoch cycle (from shapes2.c output, shapes_c63k.txt) — period 5 in w, starting w=7
Let W' = w at empty-W epoch (7,12,17,22,...). Epoch types by w - W' :
 +0 empty-W growth: counter v = 1+2^(w-2)+2^(w-1), n = 2^(w-2)-4 (w>=12). Eats trail at 2 ones/bit-flip.
    Flips from low-value 1 to 2^(w-4) = 2^(w-3)-2  => trail exhausted EXACTLY after 2^(w-4)-1 increments
    (255 @w12, 8191 @w17 — matches). Then W=b^(2^(w-3)-2) contacts last fossil "0 b ..." (worn), translate
    till overflow (room n+3 = 2^(w-2)-1).
 +1 growth with NONEMPTY W = (ab)^X a^3 (the detached b-block), counter = 2^(w-1), trail 2*3*2^(w-5)+... 
 +2 translate whole epoch (counter 2^(w-1) -> 2^w).
 +3 pure translate, empty W, counter 2^(w-1)->2^w, leaves trail 2^w - 2.
 +4 one increment: leftover 'a' absorbed => width +1, value 2^(w-1)+1+2^w  => next +0 epoch.
So empty-W epoch start value is forced: it's 2^w (overflow of all-ones) + 1 + new top bit. Room = n+3 at all levels.

## Closed-form level cycle (derived from real run at level w0=17, checked vs w0=12 where applicable)
F(x) = flips(0->x) = 2x - popcount(x);  A = 2^(w0-4);  H = 2^(w0-2)+2^(w0-1)
Tail(L) = "0 b a (ab)^X0 (a)^3 b^Y0" + S + "0 1^Z 0 a b^28 0 1^741", X0=2^(w0-9)-5, Y0=7*2^(w0-10)
 E0-G  w=w0,   v=H+u, u in[1,A]      : 0 b^(F(u)-1) 1^(4A-4-2(F(u)-1)) Tail      (R=0 exactly at u=A since F(2^m)=2^(m+1)-1)
 E0-T  w=w0,   v=H+u, u in[A+1,4A-1] : 0 b^(2A-2) 0 1^(2+F(u)-F(A+1)) 0 0 a (ab)^X0 (a)^3 b^Y0 S 0 1^Z ...
 E1-G  w=w0+1, v=2^w0+u, u in[0,7A/4+1]: 0 (ab)^(A-2) (a)^3 b^F(u) 1^(7A-1-2F(u)) 0 0 a (ab)^X0 ...
 E1-T  u in [7A/4+2, 2^w0-1]           : 0 (ab)^(A-2) (a)^3 b^(7A/2) a (ab)^X0 (a)^3 b^Y0 S 0 1^(Z+1+F(u)-F(7A/4+2)) ...  (swallow)
 E2    w=w0+2, v=2^(w0+1)+u           : 0 a (ab)^(A-3) (a)^3 b^(7A/2) a (ab)^X0 .. S 0 1^(Z2+F(u)),  Z2 = Z_E1T(end)+w0+2
 E3    w=w0+3, v=2^(w0+2)+u, u>=1     : 0 0 1^(F(u)+1) 0 b a (ab)^(A-5) (a)^3 b^(7A/2) a (ab)^X0 .. S 0 1^Z3, Z3 = Z2+F(2^(w0+1)-1)+w0+4
 E4    w=w0+4, v=2^(w0+3)             : a 1^(2^(w0+3)-2) 0 b a (ab)^(A-5) ...
 E0'   w0' = w0+5, v = 1+2^(w0'-2)+2^(w0'-1), n0' = 2^(w0'-2)-4; X0'=A-5, Y0'=7A/2, S' = "a (ab)^X0 (a)^3 b^Y0"+S, Z'=Z3.
 Room at E0 = 2^(w0-2)-1 = n0+3 (identity, not arithmetic luck). Z(17)=23683, Z(22)=781445 match.
All checked against real run (macro.cpp = block-30 macro + chain sim, checkpoint-exact vs epochs_long.txt up to c=980915).

## Per-increment rule (all modes): f = tz1(v)+1 = bits flipped by v->v+1
 growth: B += f, R -= 2f ; translate/pure-translate: trail += f.  Hence closed forms via F(x)=2x-popcount(x).
 Transition points have level-INDEPENDENT low-bit patterns:
  E0 contact at u=A=2^(w0-4) with R=0 exactly (F(2^m)=2^(m+1)-1); next increment has f=1.
  E1 contact at u=7A/4+2, leftover 1^3 (popcount(7*2^m)=3).  Overflows at all-ones.
 Only level-dependent inputs to transitions: run lengths (A-2, 7A/2, ...) and carry length; parity of E0-T trail at
 overflow = w0 mod 2 (alternates) — covered by checking both parities (w0=17 odd, 22 even, 27 odd).

## Validation (check_level.py + pred.py + exwin.c)
 Exact TM runs from closed-form predicted tapes, crc32 of full tape compared at EVERY checkpoint in 13 windows/level
 (each transition + random mid-epoch points, incl. E3->E4->next-level E0).
 w0=17: 71/71 OK.  w0=22, 27: see chk22.txt, chk27_*.txt.  w0=32 E0-contact window: chk32_1.txt.
 RESULTS: w0=17 71/71, w0=22 71/71 (all 13 windows incl. E0->E1 detach, which is quadratic: ~1.4e12 steps),
 w0=27 12 of 13 windows 43/43 OK (E0->E1 detach skipped: ~1e15 steps), w0=32 E0-contact window 8/8 OK.
 0 mismatches anywhere. Macro sim (macro.cpp) reproduces real run checkpoint-exactly to c=980915 (t=7.7e11).

## VERDICT: STRUCTURAL
Empty-W growth epochs occur exactly once per level (E0, w0=7,12,17,22,...). Start value v0=1+2^(w0-2)+2^(w0-1) and
n0=2^(w0-2)-4 are forced: E3 is a pure counter-translate from overflow value 2^(w-1) to 2^w (trail = F(2^(w-1)-1)+1+
(w+1) = 2^w-2), E4 absorbs the leftover 'a' as new top bit. Room = n0+3 (>= n0/8 with 8x margin). Growth ends at
u=A=n0/4+1 with R=0 exactly; overflow 3A increments later. No dependence on earlier quasi-random values (contrast M4).
Remaining proof work: parameterized lemmas for the per-increment rules and the 6 transition rules (in A, carry length);
level induction C(w0,S,Z) -> C(w0+5,S',Z'). Levels 7/12 are a seed (fossil '0 b 0 a a b^28' non-template, same rules).
