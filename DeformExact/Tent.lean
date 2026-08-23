/-
Copyright (c) 2026-present K. S. Ernest (iFire) Lee. All rights reserved.
Released under the MIT license.

# Bounded-offset deformable sampling is exactly bilinear sampling

WHAT THIS PROVES, AND WHY IT IS WORTH PROVING. Deformable attention samples a feature map at
`reference + learned offset`, which torch lowers to `GridSample`. The Hailo Dataflow Compiler
refuses that operator, and the refusal is not a naming problem: measured on the exported
keypoint model, all eight `GridSample` nodes take a data-dependent grid, so the constant fold
that removed the `Tile` blocker does not apply.

The rewrite moves the data dependence out of the ADDRESS and into the WEIGHT. Bilinear
interpolation is a separable tent kernel, and the tent vanishes beyond one pixel, so sampling
at `y + d` is a weighted sum over INTEGER shifts:

    out y = ∑ k, v (y + k) * tent (d - k)

Every `v (y + k)` is a static shift — a pad and a constant slice — and everything that depends
on the image is now a scalar multiplier. The compiler accepts the result; it was measured
parsing for `hailo10h`.

THE PYTHON SIDE AGREES TO 3e-15 AND THAT IS NOT THE SAME AS A PROOF. `scripts/deform_bounded.py`
checks the rewrite against `torch.nn.functional.grid_sample` at pseudorandom offsets and finds
float64 accumulation noise. That is evidence a counterexample was not sampled, not evidence
none exists — and the whole deployment now rests on the equality, so the gap between those two
is worth closing.

`sorry` COUNT IS ZERO, AND IT IS CHECKED. `scripts/check_no_sorry.sh` fails the build on any
occurrence, because a proof carrying an admitted goal reads exactly like a proof.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Basic

namespace DeformExact

open Finset

/-- The bilinear interpolation kernel: a tent of unit half-width. -/
noncomputable def tent (t : ℝ) : ℝ := max 0 (1 - |t|)

/-- The tent is zero at distance one or more. This is the fact that makes the rewrite
finite: only shifts within one pixel of the sample point can contribute, so a sum over a
bounded window of integers loses nothing. -/
theorem tent_eq_zero_of_one_le_abs {t : ℝ} (h : 1 ≤ |t|) : tent t = 0 :=
  max_eq_left (by linarith)

/-- On the unit cell, the shift at 0 carries weight `1 - d`. -/
theorem tent_of_mem_unit {d : ℝ} (h0 : 0 ≤ d) (h1 : d < 1) : tent d = 1 - d := by
  unfold tent
  rw [abs_of_nonneg h0]
  exact max_eq_right (by linarith)

/-- and the shift at 1 carries weight `d`. Together with `tent_of_mem_unit` these are the
two coefficients of ordinary bilinear interpolation, recovered rather than assumed. -/
theorem tent_sub_one_of_mem_unit {d : ℝ} (h0 : 0 ≤ d) (h1 : d < 1) : tent (d - 1) = d := by
  unfold tent
  rw [abs_of_nonpos (by linarith : d - 1 ≤ 0)]
  have h : 1 - -(d - 1) = d := by ring
  rw [h]
  exact max_eq_right h0

/-- Every integer shift other than 0 and 1 is at least a pixel away, so it drops out. -/
theorem tent_int_eq_zero {d : ℝ} (h0 : 0 ≤ d) (h1 : d < 1) {k : ℤ} (hk : k ≠ 0) (hk' : k ≠ 1) :
    tent (d - (k : ℝ)) = 0 := by
  apply tent_eq_zero_of_one_le_abs
  rcases lt_or_gt_of_ne hk with hneg | hpos
  · -- k ≤ -1, so d - k ≥ d + 1 ≥ 1
    have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
    rw [abs_of_nonneg (by linarith)]
    linarith
  · -- k ≥ 2, so d - k ≤ d - 2 < -1
    have hk2 : (2 : ℤ) ≤ k := by omega
    have hk2' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- **The theorem.** Over any finite window of integer shifts containing 0 and 1, the
tent-weighted sum of statically shifted samples equals bilinear interpolation.

`v` is the feature map indexed by integer shift, `d ∈ [0,1)` the fractional offset, and `s`
the window the rewrite actually sums over. The conclusion holds for EVERY such window, which
is the part that matters for deployment: the clamp radius `r` is a cost parameter and not a
correctness parameter, so widening or narrowing it cannot change the answer. -/
theorem bounded_sum_eq_bilinear (v : ℤ → ℝ) {d : ℝ} (h0 : 0 ≤ d) (h1 : d < 1)
    (s : Finset ℤ) (h0s : (0 : ℤ) ∈ s) (h1s : (1 : ℤ) ∈ s) :
    ∑ k ∈ s, v k * tent (d - (k : ℝ)) = v 0 * (1 - d) + v 1 * d := by
  have hpair : ({0, 1} : Finset ℤ) ⊆ s := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h0s
    · exact h1s
  have hvanish : ∀ x ∈ s, x ∉ ({0, 1} : Finset ℤ) → v x * tent (d - (x : ℝ)) = 0 := by
    intro x _ hx
    simp only [mem_insert, mem_singleton, not_or] at hx
    rw [tent_int_eq_zero h0 h1 hx.1 hx.2, mul_zero]
  rw [← Finset.sum_subset hpair hvanish]
  rw [Finset.sum_insert (by simp), Finset.sum_singleton]
  -- The casts have to come down before the tent lemmas will match: the goal carries
  -- `tent (d - ↑(0 : ℤ))`, not `tent d`.
  have c0 : d - ((0 : ℤ) : ℝ) = d := by norm_num
  have c1 : d - ((1 : ℤ) : ℝ) = d - 1 := by norm_num
  rw [c0, c1, tent_of_mem_unit h0 h1, tent_sub_one_of_mem_unit h0 h1]

/-- Separability: the 2D sampler is the product of two 1D tents, so the two-dimensional
statement follows from the one-dimensional one with no new mathematics. Stated because the
implementation is 2D and a reader should not have to reconstruct the reduction. -/
theorem bounded_sum_eq_bilinear_two (v : ℤ → ℤ → ℝ) {dy dx : ℝ}
    (hy0 : 0 ≤ dy) (hy1 : dy < 1) (hx0 : 0 ≤ dx) (hx1 : dx < 1)
    (sy sx : Finset ℤ) (hy0s : (0 : ℤ) ∈ sy) (hy1s : (1 : ℤ) ∈ sy)
    (hx0s : (0 : ℤ) ∈ sx) (hx1s : (1 : ℤ) ∈ sx) :
    ∑ ky ∈ sy, ∑ kx ∈ sx,
        v ky kx * (tent (dy - (ky : ℝ)) * tent (dx - (kx : ℝ)))
      = (v 0 0 * (1 - dx) + v 0 1 * dx) * (1 - dy)
        + (v 1 0 * (1 - dx) + v 1 1 * dx) * dy := by
  have inner : ∀ ky : ℤ,
      ∑ kx ∈ sx, v ky kx * (tent (dy - (ky : ℝ)) * tent (dx - (kx : ℝ)))
        = (v ky 0 * (1 - dx) + v ky 1 * dx) * tent (dy - (ky : ℝ)) := by
    intro ky
    have : ∀ kx ∈ sx, v ky kx * (tent (dy - (ky : ℝ)) * tent (dx - (kx : ℝ)))
        = (v ky kx * tent (dx - (kx : ℝ))) * tent (dy - (ky : ℝ)) := by
      intro kx _; ring
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul,
        bounded_sum_eq_bilinear (fun kx => v ky kx) hx0 hx1 sx hx0s hx1s]
  rw [Finset.sum_congr rfl (fun ky _ => inner ky)]
  exact bounded_sum_eq_bilinear (fun ky => v ky 0 * (1 - dx) + v ky 1 * dx) hy0 hy1 sy hy0s hy1s

end DeformExact
