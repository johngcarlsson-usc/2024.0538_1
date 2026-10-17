# Lean proof that β₂ < 0.93

`BHHStrip.lean` is a complete, machine-checked Lean 4 / Mathlib proof of the classical
Beardwood–Halton–Hammersley strip bound: if `L n` is the expected optimal tour length of
`n` independent uniform points in the unit square, then

```lean
theorem bhh_lt_point_nine_three :
    ∃ c < (0.93 : ℝ), ∀ᶠ n in Filter.atTop, L n ≤ c * Real.sqrt n
```

(with `c = 0.927`). It contains no `sorry`, and it depends only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). The definitions of `tourLength` and `L` are
at the top of the file, so the statement can be checked against the informal one directly.

## Verifying

Install Lean through [elan](https://github.com/leanprover/elan), then from this folder run:

```bash
lake exe cache get   # download prebuilt Mathlib (pinned in lakefile.toml)
lake build           # checks BHHStrip.lean, about 5 minutes
```

The build ends by printing the axioms the theorem depends on:

```
'bhh_lt_point_nine_three' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Toolchain: `leanprover/lean4:v4.33.0-rc1`, with Mathlib at commit `9944fe29`.

## Proof outline

* **Part A (deterministic).** Cut the square into `k ≈ √(n/3)` horizontal strips and visit
  each strip left to right in a serpentine. The tour length is then at most the sum of
  distances between x-consecutive points in each strip, plus edge gaps and `O(1)`.
* **Part B (probability).** By exchangeability, the expected sum reduces to a double integral
  over one pair of points. That integral is weighted by the probability that the other
  `n − 2` points avoid the segment between them. The argument works directly with `n`
  uniform points, so it needs no Poissonization.
* **Part C (analysis).** Use `(1 − x)^m ≤ e^{−mx}` and rescale by `√n`. Then bound the
  BHH-type integral with a certified rational quadrature (`envelope_le`, ≈ 0.8003 ≤ 0.802).

`tools/gen_numerics.py` regenerates the numeric tables used in `envelope_le`, re-checking
every inequality in exact rational arithmetic. You don't need it to verify the proof.
