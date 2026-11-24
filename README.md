# The Tammes problem for N = 16

An independent verification of the Tammes problem for 16 points: the largest possible smallest angle between
16 points on a sphere is

    d16 = arccos(u0) = 52.2443957527...°

where u0 is the root in (0.61, 0.62) of 23u⁶ + 6u⁵ + 5u⁴ + 4u³ − 3u² − 2u − 1, attained by four staggered
squares.

- `paper/`: the paper, [`tammes-16.pdf`](paper/tammes-16.pdf).
- `lean/`: Lean 4 proofs (Lean 4.34.1, Mathlib v4.34.1).
  - The lower bound d16 ≥ arccos u0 is proved in full.
  - `Tammes16/Main.lean` proves d16 = arccos u0 from it and five named hypotheses.
  - Only the standard axioms are used.

```bash
cd lean && lake exe cache get && lake build Tammes16
```

Licensed under the Apache License 2.0 (see `LICENSE`).
