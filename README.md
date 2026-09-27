# Nonhalting proof: BB(6) holdout `1RB---_0RC1LF_1LC1LD_1RE0RA_0RD1RF_0LD0LF`

## Result

The machine

```
1RB---_0RC1LF_1LC1LD_1RE0RA_0RD1RF_0LD0LF
```

started in state A on the blank tape never halts. It is in the bbchallenge BB(6) holdout list of
2026-09-24 (815 classes), and it is alone in its equivalence class.

The proof is a single Lean 4 development (v4.33.1, no Mathlib). Its final theorem is

```lean
theorem M7.nonhalt : ∀ n, ¬ M7.halted (M7.run n M7.init)
```

It has no hypotheses and no `sorry`. `#print axioms M7.nonhalt` lists only `propext`,
`Classical.choice`, and `Quot.sound`. There is no `native_decide` anywhere. The 1,132,435-step base
case is checked by the Lean kernel itself with `decide +kernel`.

## How the machine behaves

Notation: `a = 10`, `b = 100`.

**A leftward-moving binary counter.** Once per increment the head reaches a new leftmost cell in state
D. We call this moment a *checkpoint*. At a checkpoint the tape reads

```
[D]0000 · COUNTER · W · (trail of 1s) · fossils and trails · ... · 0 a b^28 0 1^741
```

COUNTER is a fixed-width binary counter with the least significant bit on the left. The digit 0 is
written `100` (= b) and the digit 1 is written `1010` (= aa). It gains 1 per checkpoint. The whole word
moves 2 cells to the left per increment.

**A body that grows or translates.** Each increment of the counter costs `f = (trailing ones) + 1` round
trips of the head, from the left end to the right end of the body W and back. Every trip absorbs any
complete tokens at the front of the medium into W. What happens next depends on the medium just right of W:

- **growth:** if the medium starts with `11`, W eats those two 1s and gains one `b`.
- **translate:** if the medium starts with `0`, a 1 is inserted after that `0`, so the body leaves a
  growing trail of 1s behind it.

**Overflow and fossils.** When the counter is all ones it overflows. The width grows, and the front of W
is rewritten by one of four fixed rules (O0 to O3). One of these rules detaches W from the counter. It
is then left behind as a *fossil*, a frozen block of tokens that later bodies run into. Fossils nest, so
the tape looks like counter, body, trail, fossil, trail, fossil, and so on. The trail lengths grow like
`2^(w-2)` times a constant.

**Levels.** The behaviour settles into a cycle of five overflows, called E0, E1, E2, E3, E4. Each level
is 5 counter widths wider than the one before (w0 = 12, 17, 22, …). The next level starts from exactly
the same template, with one more fossil and a longer trail. Every exponent in the cycle has a closed form
in `A = 2^(w0-4)`. `notes/room-NOTES.md` gives all of them.

## The only way to halt, and why it never happens

The only undefined transition is A reading 1. State A is entered only through D1 → 0RA, so the machine
can halt only if D reads a 1 that has another 1 to its right. The only places with `11` are the ends of
trails. In an exhaustive study of about 106,000 perturbed starting tapes, exactly one mechanism ever led
to a halt. It needs all three of these:

1. W is empty, or made only of `b`s, and in **growth** mode (it is still eating a trail),
2. the counter overflows,
3. the overflow comes before the growth epoch has eaten enough of the trail. The empirical threshold was
   about n/8 increments for a trail of length n.

On the real run the dangerous empty-W growth epoch (E0) happens once per level, and it always starts from
exactly determined values:

```
counter value v0 = 1 + 2^(w-2) + 2^(w-1)      (width w = w0)
trail length  n0 = 2^(w-2) - 4
```

These values are forced by the structure, not by arithmetic luck. E3 is a pure translate from the
overflow value `2^(w-1)` up to `2^w`, which leaves a trail of `2^w - 2`. E4 then absorbs the leftover
`a` as a new top bit. So the room before the next overflow is `2^w - v0 = 2^(w-2) - 1 = n0 + 3`
increments. That is about 8× the halting threshold. Growth uses up the trail after exactly
`A = 2^(w-4)` increments, when the trail reaches length 0 (because `F(2^m) = 2^(m+1) - 1`, where
`F(x) = 2x - popcount(x)` counts bit flips). The overflow comes `3A` increments later, while the
machine is safely in translate mode. The same identity `room = n0 + 3` holds at every level, and the
Lean proof establishes it symbolically for all levels.

## Proof structure (Lean)

1. **Tape model** (`Machine`, `Frame`). The machine has exact semantics on `Cfg = (state, L, head, R)`.
   `runB` is a bounded runner on finite lists, and `runB_frame` shows that a successful bounded run also
   holds for every extension of the far tape.
2. **Sweep, trip and increment lemmas** (`Micro`, `Trip`, `Counter`, `Incr`). These give the token
   encoding and the right and left sweeps (proved by induction over token lists). They also give the end
   events G (growth) and T (translate), whole trips, the counter identity (trips per increment and
   `F(v) = 2v - popcount v`), and whole growth and translate epochs.
3. **Overflow lemmas** (`OvMicro`, `Overflow`). These cover entry into overflow, Z-trips, and the
   rewrites O0 (with the pending increment), O1, O2 and O3.
4. **Level theorem** (`Arith`, `Level`). `Arith` holds the popcount values at the epoch endpoints.
   `Level` defines the template `tmpl j Q Z Rest` (level `j` ↔ `w0 = j + 8`) and proves
   ```lean
   theorem M7.level (j) (Q0) (Z) (Rest) :
     Reach (tmpl j (Q0 ++ [b]) Z Rest) (tmpl (j+5) (nq j Q0 ++ [b]) (Z + 1480*2^j + 2) Rest)
   ```
   for all `j`, by chaining the phases E0 → E1 → E2 → E3 → E4.
5. **Kernel-checked base case** (`Base`). The run goes from the blank tape to checkpoint 943 in
   1,132,435 steps. It is checked in 13 chunks of at most 90k steps each, with `decide +kernel` on
   run-length-encoded configurations. It lands exactly on `tmpl 4 [b] 0 Rest0` (w0 = 12).
6. **Final theorem** (`Main`). By induction the machine reaches level `4 + 5i` at some step `≥ i`,
   for every `i`. The halting state is absorbing, but every template is in state D. So
   `M7.nonhalt : ∀ n, ¬ halted (run n init)`.

## Trust base

- The Lean 4 kernel (v4.33.1) and the standard axioms `propext`, `Classical.choice`, `Quot.sound`.
- No `native_decide`, `sorry`, `admit`, `implemented_by` or extra axioms. The base case uses
  `decide +kernel`, which the kernel evaluates itself.
- The statement only needs you to read `M7/Machine.lean`, about 65 lines: the transition table,
  `step`, `run`, `init`, and `halted`.

## Build and check

Requirements: [elan](https://github.com/leanprover/elan). The toolchain `leanprover/lean4:v4.33.1` is
pinned in `lean/lean-toolchain`. No other dependencies are needed.

```sh
cd lean
lake build                     # builds M7; about 1.5 min from scratch on x86-64 (M7.Base ~80 s, single-threaded), peak RAM ~5.6 GB
lake env lean Axioms.lean      # prints the axioms of M7.nonhalt and M7.level
```

Expected output of the second command:

```
'M7.nonhalt' depends on axioms: [propext, Classical.choice, Quot.sound]
'M7.level' depends on axioms: [propext, Classical.choice, Quot.sound]
M7.nonhalt : ∀ (n : Nat), ¬M7.halted (M7.run n M7.init)
```

## Layout

`lean/`: the Lean project (`lakefile.toml`, `lean-toolchain`, `M7.lean`, `Axioms.lean`)

| file | contents |
|---|---|
| `M7/Machine.lean` | the machine, its exact one-step semantics, `run`, `init`, `halted`, `run_add`, `run_H` |
| `M7/Frame.lean` | bounded runner `runB` on finite lists, and the frame lemma for arbitrary far tape |
| `M7/Micro.lean` | tokens a/b, encoding, right and left sweeps by induction, end events G/T |
| `M7/Trip.lean` | `Reach`, and whole round trips (G and T, top and inner) |
| `M7/Counter.lean` | LSB-first fixed-width counter: `bits`, popcount/trailing-ones, trips per increment |
| `M7/Incr.lean` | checkpoints `ck`, single increments, and whole growth and translate epochs |
| `M7/OvMicro.lean` | micro lemmas for overflow (skip, leg, the O2/O3 fronts, length-3 remnant) |
| `M7/Overflow.lean` | overflow transitions: entry, Z-trips, O0 with pending increment, O1, O2, O3 |
| `M7/Arith.lean` | popcount and bit patterns at the epoch endpoints (`P = 2^j`) |
| `M7/Level.lean` | template `tmpl`, phases E0 to E4, `M7.level : level j → level j+5` |
| `M7/Base.lean` | blank tape to checkpoint 943 (1,132,435 steps) with `decide +kernel`, in 13 chunks |
| `M7/Main.lean` | `reach_levels` and the final theorem `M7.nonhalt` |
| `Axioms.lean` | `#print axioms` check |

`notes/`: supplementary working notes. They are not needed to check the proof.

- `FINDINGS.md`: the first characterization, and the sweep results on the halting region.
- `decode-NOTES.md`: token-level trip and overflow rules and the steady-state grammar. The replay was
  verified against direct simulation at every one of 999,984 consecutive checkpoints (17 to 10^6, about
  7.85·10¹¹ TM steps).
- `room-NOTES.md`: the closed-form level cycle, its exact values, and why the room condition is
  structural. It was checked by exact simulation windows at w0 = 17, 22, 27 and 32, with 0 mismatches.
- `lean-NOTES.md`: development notes for the Lean proof.

`sim/`: the small simulation tools referenced by the notes (C and Python 3, standard library only;
`exwin.c` needs zlib).

- `tm.h`, `sim.py`: direct simulators.
- `decode/hsim.c`: exact simulation from blank that prints a tape hash at every checkpoint.
  `decode/ckd.c`: dumps checkpoint tapes.
- `decode/replay.py`, `fast.py`, `verify.py`, `xval.py`, `tokz.py`: the token-level replay and its
  verification against `hsim`.
- `room/pred.py`: the closed-form predictor for level tapes. `room/check_level.py` with `exwin.c`: exact
  simulation windows compared against the predictions. `room/macro.cpp`: a macro plus chain-rule
  accelerated simulator.

The scripts call `./ckd`, `./exwin`, and so on, so compile each C file in its own directory first. For
example: `cd sim/decode && gcc -O2 -o hsim hsim.c && gcc -O2 -o ckd ckd.c`.

## SHA-256

See `SHA256SUMS` (check it with `sha256sum -c SHA256SUMS`). Key files:

```
cb24d669d76adf84965243d628d78559e8ef2d816cd9e48f1cd1f97394d8886c  ./lean/Axioms.lean
3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71  ./lean/lean-toolchain
ed880f1cfb4b0865c4903d16fdfa0e82b29cbb282acda9f7a3fbc6d4a630dfcf  ./lean/M7/Base.lean
3030ace28e7b34fd07a4bf4be5524ec10c8cb403dfffe9d1035912f78e8eb56a  ./lean/M7/Level.lean
7b780320c3dbff812779e43d42e27e5fed98f4ca6a970f26810ba57ab9a85f37  ./lean/M7/Machine.lean
02451c5a76fd684d73afe789a58366525ff4481f89cf34877f295711a2afe59d  ./lean/M7/Main.lean
```
