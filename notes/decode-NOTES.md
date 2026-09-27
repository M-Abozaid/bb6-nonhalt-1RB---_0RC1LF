# m7 decode notes (token-level rules, replay, grammar)
Started 2026-09-27. Machine 1RB---_0RC1LF_1LC1LD_1RE0RA_0RD1RF_0LD0LF. Notation a=10, b=100.
## Log
- read FINDINGS.md, epochs*.txt. Plan: dump consecutive checkpoints, derive per-checkpoint rewrite on token string.
- Tools: ckd.c (dump ckpt tapes), shp.c (shape-change catalog; shp1e6.txt), absd.c (absolute windows, TRIP=1 per-trip),
  hsim.c (exact sim, per-ckpt poly hash of tape, abs coords; hsim1e6.txt) , tokz.py (tokenizer).
- Checkpoint c has lo = -(2c-1) (abs), tape = 0^5 C S. C = counter over {1=1010(=aa), 0=100(=b)}, LSB left.
- TRIP: every increment = f = (#trailing ones)+1 round trips lo -> W right end -> lo. Body (C+W) is rigid; its right end
  moves -1 cell per trip (counter right edge moves -(1+carries) per increment). Medium right of W is static (abs coords).
- Conservation: |0^5 C S| up to any untouched medium cell grows by exactly 2 per checkpoint (lo -2).
- Trip right-end rules (M = medium string right after W; W ends in 0):
    G  : M = 11X        -> W+=b, M = X            (growth; W eats two 1s)
    T  : M = 0 1^n X    -> M = 0 1^(n+1) X        (translate, n>=1; '0' = separator)
    C1 : M = 1 000 X    -> W+=b, M = 0 1 X        (odd-parity contact with fossil starting 000)
- Overflow (C=1^w) body rewrites observed (S after counter; trail count by conservation):
    O1: 0 b^(2m) 0 1^n X        -> 0 (ab)^(m-1) a^3 1^n' X        (translate->growth)
    O2: 0 (ab)^k a^3 Y 0 1^n X  -> 0 a a b (ab)^(k-2) a^3 Y 0 1^n' X   (= delete first b of W)
    O3: 0 a a b Z 0 1^n X       -> 0 0 a b g(Z) 0 1^n' X  ; next trip makes 0 0 1^2 0 b g(Z)0.. = W empty, fossil 0 b g(Z) 0
         g(a^3 b^29) = 0 a a b^28 ; g((ab)^252 a^3 b^896) = a a b (ab)^250 a^3 b^896
    O0: W empty: 0 0 1^n X -> a 1^n' X ; next ckpt (f=1): C 0^w1 -> 1 0^(w-1) 1 1 (w+2), S = 0 1^(n'-2) X (growth)
- KEY (2026-09-27): UNIVERSAL TRIP RULE. W := maximal greedy token sequence (b=100 preferred over a=10) after the
  counter separator. One trip: (1) absorb tokens from medium into W (free, no cell change: this is 'swallow');
  (2) if medium starts 11 -> 100 (W+=b, growth, +1 cell); else medium starts 0 -> insert 1 after it (translate, +1 cell).
  Contacts/wear-down/swallow are all instances (fossil '0 b ...' = sep+trail 1; odd trail -> 1|000.. absorbs b then T).
- Overflow probe tool: nck.c + ovf.py (synthetic C=1^w, arbitrary W). Tables show O(W) depends on W prefix only.
- replay.py implemented (INC/TRIP/O0/O1/O2/O3/PEND). test_small.py: exact full-tape string match c=16..4000.
  verify.py: poly-hash match vs hsim for EVERY checkpoint 17..170000 (incl. O0,O1 x3,O2 x2,O3 x2, PEND x2,
  swallow at 77744). Running to 1e6 as hsim progresses.
  O-rules as implemented (S = '0' W M, M front = '0 1^n' translate):
    O0: W=eps            -> PEND ('10' 1^n' X)
    O1: W=b^j (j>=2)     -> W=(ab)^(ceil(j/2)-1) a^3, drop M's leading 0 (mode -> growth)
    O2: W=(ab)^k a^3 Y, k>=2 -> W = a (ab)^(k-1) a^3 Y      (delete first b)
    O3: W=a a b Z        -> W=eps, M = 0 a b [0] Z' 0 1^n' ..., Z=(ab)^k a^3 Y: Z'=a (ab)^(k-1) a^3 Y ;
                            Z=a a a b Z'': [0] present, Z' = a a Z''.   (fossil born = '0 b' + Z' + old trail)
    trail count after any O = conservation (+2 cells per ckpt up to untouched medium).
- fast.py: epoch-accelerated replay (trips(v->v') = F(v')-F(v), F(v)=2v-popcount(v)); xval.py: equals step replay
  at 321 checkpoints up to 999999 (incl. all events). explore.py/struct.py: extrapolated to c~3e10 (w=37).
- STEADY STRUCTURE (period 5 in w): O0 at w=5j -> PEND (w=5j+2) -> empty-W growth (trail 2^(w-2)-4, need 2^(w-3)
  trips = 1/4 of available: ratio room/need = 4.00 exactly in increments) -> contact wears fossil front ->
  translate -> O1 (w=5j+2) -> growth eats trail, SWALLOWS fossil (odd parity) -> translate -> O2 (w=5j+3)
  -> O3 (w=5j+4): W detaches as new fossil F -> translate -> O0 ...
  W before O2 = B_J ... B_1 with blocks B = a (ab)^k a^3 b^m ; k_j = 2^(5j+3)-5 ... , m_j = 7*2^(5j+2).
  Medium: 0 1^n1 F 1^n2 [0 a b^28 0] 1^741 (the ancient F_A remnant never touched again).
- Growth-mode overflow probe: W=(ab)^k a^3 b^j (growth) SAFE; W=b^j or eps in growth mode HALTS (=room condition).
- synth.py/synth2.py: replay run on all 100,086 synthetic starts of the runs/ sweep (not included) (sim verdicts from *.out):
    66793 RUN: replay runs the same #ckpts with only known rules.
    5095 HALT: in EVERY one the replay stops at an overflow with W=b^j/eps in GROWTH mode (unhandled) -> the only
         halting mechanism seen is growth-mode empty-W-epoch overflow.  0 halts elsewhere.
    1970 RUN: replay stops exactly at the sim's final (maxov) overflow = unhandled off-orbit O shape, no conflict.
    26228 RUN: replay stops EARLY at growth-mode overflow on W=b^j that the sim SURVIVES -> growth-mode O1 is not
         front-local: probe (w=8, W=b^j, trail r then fossil): halts iff j < ~r/4 (r=40: j=1 only; r=80: j<=22;
         r=160: j<=58). Result when safe: (ab)^k' a^3 1^r' with k'>j/2 (the overflow keeps eating trail).
         => ARITHMETIC: empty-W growth epoch must be (nearly) done at overflow. Real run: always done, room 4.00x.
- shapes.py: all distinct abstract checkpoint shapes c=17..1e6 (exps>3 -> +): 64 shapes, one 7-phase cycle.
## GRAMMAR (steady state, from verified replay; D := a (ab)^+ a^3 b^+ , V := D^+ , A := 0 a b^28 0 1^741)
  config = 0^5 C S, C in {100,1010}^w (LSB left), S in
   P1 transl, W=eps      : 0 0 1^+ (0 b V 0) 1^+ A                 [O3 .. O0]
   P2 PEND (C=0^w 1)     : 1 0 1^+ (0 b V 0) 1^+ A
   P3 empty-W growth     : 0 b^* 1^+ (0 b V 0) 1^+ A   trail even   [ARITH room: must finish before C=1^w]
   P4 transl             : 0 b^+ 0 1^+ (0 0 V 0) 1^+ A             [contact1 wore 'b' off fossil front]
   P5 O1-growth          : 0 (ab)^+ a^3 b^* 1^+ (0 0 V 0) 1^+ A  trail odd  [contact2 = swallow]
   P6 transl (swallowed) : 0 (ab)^+ a^3 b^+ V 0 1^+ A
   P7 after O2           : 0 D V 0 1^+ A        -> O3 gives P1 with new fossil 0 b D V 0 (nesting depth +1)
  Real exponents: k_j=2^(5j+3)-5, m_j=7*2^(5j+2) (not needed for safety).
  Regular: counter word, token shapes, fossil templates (fresh 0bV0 / worn 00V0), separators/modes, parities
   (trail parity vs popcount(C) mod 2 etc.), TRIP transducer, O-front rewrites.
  Arithmetic: P3 room (unary trail n vs binary counter: n/2 <= F(2^w-1)-F(v)); real margin exactly 4x;
   (optionally P5 room to stay in the finite phase family; growth-mode O2 is safe per probe; margin ~9x).
- RESULT: verify.py hsim1e6.txt 16 1000000 -> VERIFIED 999,984 consecutive checkpoints (17..1e6, 7.85e11 TM steps):
  replay tape hash == direct-sim hash at every checkpoint. Events covered: O1x3 O2x3 O3x3 O0x3 PENDx3, G 84,664,
  T 1,915,125 trips, contacts at 1198/2416/38830 (wear) and 77744 (swallow).
