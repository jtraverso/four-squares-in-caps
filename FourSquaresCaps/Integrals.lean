/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Elementary integrals for the weight bounds

For `0 < a ≤ c`:
* `integral_max_inv_pow_four_le`: `∫_{-c}^{c} max(|u|, a)^{-4} du ≤ (8/3) a^{-3}`;
* `integral_max_inv_le`: `∫_{-c}^{c} max(|u|, a)^{-1} du ≤ 2 (1 + log(c/a))`.
-/

@[expose] public section

namespace FourSquaresCaps

open intervalIntegral

/-- Symmetry: `∫_{-c}^{c} g(|u|) du = 2 ∫_0^c g(u) du` for continuous `g`. -/
theorem integral_comp_abs_symm (g : ℝ → ℝ) (hg : Continuous g) (c : ℝ) (hc : 0 ≤ c) :
    ∫ u in -c..c, g |u| = 2 * ∫ u in (0 : ℝ)..c, g u := by
  have hgi : ∀ a b : ℝ, IntervalIntegrable (fun u => g |u|) MeasureTheory.volume a b :=
    fun a b => (hg.comp continuous_abs).intervalIntegrable a b
  rw [← integral_add_adjacent_intervals (hgi (-c) 0) (hgi 0 c)]
  have h1 : ∫ u in -c..0, g |u| = ∫ u in (0 : ℝ)..c, g u := by
    rw [← neg_zero, ← integral_comp_neg (fun u => g |u|), neg_zero]
    refine integral_congr fun u hu => ?_
    simp only [abs_neg]
    rw [Set.uIcc_of_le hc] at hu
    rw [abs_of_nonneg hu.1]
  have h2 : ∫ u in (0 : ℝ)..c, g |u| = ∫ u in (0 : ℝ)..c, g u := by
    refine integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hc] at hu
    simp only [abs_of_nonneg hu.1]
  rw [h1, h2]; ring

theorem continuous_max_inv_pow (a : ℝ) (ha : 0 < a) (k : ℕ) :
    Continuous (fun u : ℝ => ((max u a) ^ k)⁻¹) :=
  ((continuous_id.max continuous_const).pow k).inv₀ fun u =>
    pow_ne_zero _ (lt_of_lt_of_le ha (le_max_right u a)).ne'

/-- `∫_0^c max(u, a)^{-4} = a^{-3} + (a^{-3} − c^{-3})/3 ≤ (4/3) a^{-3}`. -/
theorem integral_max_inv_pow_four_half_le (a c : ℝ) (ha : 0 < a) (hac : a ≤ c) :
    ∫ u in (0 : ℝ)..c, ((max u a) ^ 4)⁻¹ ≤ 4 / 3 * (a ^ 3)⁻¹ := by
  have hci := continuous_max_inv_pow a ha 4
  rw [← integral_add_adjacent_intervals (hci.intervalIntegrable 0 a) (hci.intervalIntegrable a c)]
  have h1 : ∫ u in (0 : ℝ)..a, ((max u a) ^ 4)⁻¹ = a * (a ^ 4)⁻¹ := by
    rw [integral_congr (g := fun _ => (a ^ 4)⁻¹) fun u hu => by
      rw [Set.uIcc_of_le ha.le] at hu; simp only [max_eq_right hu.2]]
    simp
  have h2 : ∫ u in a..c, ((max u a) ^ 4)⁻¹ = ((a ^ 3)⁻¹ - (c ^ 3)⁻¹) / 3 := by
    rw [integral_congr (g := fun u => u ^ (-4 : ℤ)) fun u hu => by
      rw [Set.uIcc_of_le hac] at hu
      simp only [max_eq_left hu.1, zpow_neg, zpow_ofNat]]
    have h0 : (0 : ℝ) ∉ Set.uIcc a c := by
      rw [Set.uIcc_of_le hac]; intro h; linarith [h.1]
    rw [integral_zpow (Or.inr ⟨by norm_num, h0⟩)]
    have hc0 : 0 < c := lt_of_lt_of_le ha hac
    norm_num
    field_simp
    ring
  rw [h1, h2]
  have hc0 : 0 < c := lt_of_lt_of_le ha hac
  have : 0 ≤ (c ^ 3)⁻¹ := by positivity
  have e : a * (a ^ 4)⁻¹ = (a ^ 3)⁻¹ := by field_simp
  rw [e]
  linarith

theorem integral_max_inv_pow_four_le (a c : ℝ) (ha : 0 < a) (hac : a ≤ c) :
    ∫ u in -c..c, ((max |u| a) ^ 4)⁻¹ ≤ 8 / 3 * (a ^ 3)⁻¹ := by
  have hc0 : 0 ≤ c := (lt_of_lt_of_le ha hac).le
  rw [integral_comp_abs_symm (fun u => ((max u a) ^ 4)⁻¹) (continuous_max_inv_pow a ha 4) c hc0]
  have := integral_max_inv_pow_four_half_le a c ha hac
  linarith

/-- `∫_0^c max(u, a)^{-1} = 1 + log(c/a)`. -/
theorem integral_max_inv_half_le (a c : ℝ) (ha : 0 < a) (hac : a ≤ c) :
    ∫ u in (0 : ℝ)..c, ((max u a) ^ 1)⁻¹ ≤ 1 + Real.log (c / a) := by
  have hci := continuous_max_inv_pow a ha 1
  rw [← integral_add_adjacent_intervals (hci.intervalIntegrable 0 a) (hci.intervalIntegrable a c)]
  have h1 : ∫ u in (0 : ℝ)..a, ((max u a) ^ 1)⁻¹ = 1 := by
    rw [integral_congr (g := fun _ => a⁻¹) fun u hu => by
      rw [Set.uIcc_of_le ha.le] at hu; simp only [max_eq_right hu.2, pow_one]]
    simp [ha.ne']
  have h2 : ∫ u in a..c, ((max u a) ^ 1)⁻¹ = Real.log (c / a) := by
    rw [integral_congr (g := fun u => u⁻¹) fun u hu => by
      rw [Set.uIcc_of_le hac] at hu; simp only [max_eq_left hu.1, pow_one]]
    exact integral_inv_of_pos ha (lt_of_lt_of_le ha hac)
  rw [h1, h2]

theorem integral_max_inv_le (a c : ℝ) (ha : 0 < a) (hac : a ≤ c) :
    ∫ u in -c..c, ((max |u| a) ^ 1)⁻¹ ≤ 2 * (1 + Real.log (c / a)) := by
  have hc0 : 0 ≤ c := (lt_of_lt_of_le ha hac).le
  rw [integral_comp_abs_symm (fun u => ((max u a) ^ 1)⁻¹) (continuous_max_inv_pow a ha 1) c hc0]
  have := integral_max_inv_half_le a c ha hac
  linarith

end FourSquaresCaps
