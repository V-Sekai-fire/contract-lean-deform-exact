# lean-deform-exact

Deformable attention samples a feature map at `reference + learned offset`, which torch
lowers to `GridSample`. The Hailo Dataflow Compiler refuses that operator, and the refusal
is not a naming problem: on the exported RF-DETR keypoint model all eight `GridSample`
nodes take a **data-dependent** grid, so the constant fold that removed the `Tile` blocker
does not apply.

This repository proves the rewrite that gets around it.

## The rewrite

Bilinear interpolation is a separable tent kernel, and the tent vanishes beyond one pixel,
so sampling at `y + d` is a weighted sum over **integer** shifts:

    out y = ∑ k, v (y + k) * tent (d - k)

Every `v (y + k)` is a static shift — a pad and a constant slice, fixed at compile time —
and everything that depends on the image has moved into a scalar multiplier. **No address
depends on the image.** The addresses were the objection; the arithmetic never was.

## What is proved

`DeformExact/Tent.lean`, six theorems, kernel-checked:

| theorem | statement |
| --- | --- |
| `tent_eq_zero_of_one_le_abs` | the tent is zero at distance one or more |
| `tent_of_mem_unit` | on the unit cell the shift at 0 weighs `1 - d` |
| `tent_sub_one_of_mem_unit` | and the shift at 1 weighs `d` |
| `tent_int_eq_zero` | every other integer shift drops out |
| `bounded_sum_eq_bilinear` | **the tent-weighted sum equals bilinear interpolation** |
| `bounded_sum_eq_bilinear_two` | and the 2D case, by separability |

The main theorem holds for **any** finite window containing 0 and 1. That is the part that
matters for deployment: the clamp radius is a cost parameter, not a correctness one, so
widening or narrowing it cannot change the answer.

    $ lake build
    Build completed successfully (1978 jobs).

    $ python scripts/check_no_sorry.py DeformExact --self-test
      ok    0 admitted goals: no sorry, no sorryAx, no native_decide
      ok    control fires on a planted sorry and not on one in a comment

Each theorem depends on `[propext, Classical.choice, Quot.sound]` and nothing else — no
`sorryAx`, so none is admitted. Check it with `#print axioms`.

## Why a proof and not the test

`rf-detr-cpp/scripts/deform_bounded.py` checks the same equality against
`torch.nn.functional.grid_sample` and agrees to **3e-15**, with a negative control that
correctly fails when the offset leaves the clamp. That is evidence a counterexample was not
sampled, not evidence that none exists.

Two things found on the way there, both by measurement rather than review: an `eps` inside
`sqrt((d-k)²+eps)` was the entire error term, not float accumulation — removing it improved
agreement a millionfold, 1e-9 to 1e-15 — and a fixed absolute tolerance across different
term counts was the wrong bar, since r=3 accumulates 81 products where r=1 accumulates 25.

## Measured downstream

The rewrite exports to 160 ONNX nodes using only `Pad`, `Slice`, `Sub`, `Pow`, `Mul`,
`Sqrt`, `Relu`, `Add`, `Concat`, `Reshape`, `Transpose`, `Cast`, `Constant` — and the real
Dataflow Compiler parses it for `hailo10h`:

    DeformBounded          unclassified   OK      NEWLY CLASSIFIED

## Build

Lean `v4.30.0` with Mathlib pinned to the same tag, matching `lean-humanoid-rom` and
`truth_research_zk`. A proof that only builds against a moving Mathlib is a proof nobody can
re-check.

    lake update && lake exe cache get && lake build

On Windows, build from a short path. Mathlib's own directory depth plus a deep working
directory exceeds `MAX_PATH`, and the failure reads as `failed to create file` on an
unrelated Mathlib module rather than as a path-length problem.
