/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Integrals over the line of `max(|τ|, b)^{-k}`

`integral_max_inv_pow_le`: for `b > 0`, `k ≥ 2`, `max(|τ|, b)^{-k}` is integrable on `ℝ` and
`∫ max(|τ|, b)^{-k} dτ ≤ 4 b^{1-k}`.
-/

@[expose] public section

namespace FourSquaresCaps

open MeasureTheory Set

theorem continuous_max_abs_inv_pow (b : ℝ) (hb : 0 < b) (k : ℕ) :
    Continuous (fun τ : ℝ => ((max |τ| b) ^ k)⁻¹) :=
  ((continuous_abs.max continuous_const).pow k).inv₀ fun τ =>
    pow_ne_zero _ (lt_of_lt_of_le hb (le_max_right _ _)).ne'

theorem integrable_max_inv_pow (b : ℝ) (hb : 0 < b) (k : ℕ) (hk : 2 ≤ k) :
    Integrable (fun τ : ℝ => ((max |τ| b) ^ k)⁻¹) := by
  set c := (1 + b) / b with hc
  have hc0 : 0 < c := by positivity
  have hdom : Integrable (fun τ : ℝ => c ^ k * (1 + ‖τ‖) ^ (-(k : ℝ))) :=
    (integrable_one_add_norm (by simp; exact_mod_cast (show 1 < k by omega))).const_mul _
  refine hdom.mono' (continuous_max_abs_inv_pow b hb k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun τ => ?_)
  have hm : 0 < max |τ| b := lt_of_lt_of_le hb (le_max_right _ _)
  have h1 : 1 + |τ| ≤ c * max |τ| b := by
    rcases le_total |τ| b with h | h
    · rw [max_eq_right h, hc, div_mul_cancel₀ _ hb.ne']; linarith
    · rw [max_eq_left h, hc]
      rw [div_mul_eq_mul_div, le_div_iff₀ hb]
      nlinarith [abs_nonneg τ]
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos hm k)), Real.norm_eq_abs,
    Real.rpow_neg (by positivity), Real.rpow_natCast]
  rw [inv_le_iff_one_le_mul₀ (pow_pos hm k)]
  have h2 : (1 + |τ|) ^ k ≤ c ^ k * (max |τ| b) ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1 k
  calc (1 : ℝ) = (1 + |τ|) ^ k * ((1 + |τ|) ^ k)⁻¹ := by
        rw [mul_inv_cancel₀ (by positivity)]
    _ ≤ c ^ k * (max |τ| b) ^ k * ((1 + |τ|) ^ k)⁻¹ := by gcongr
    _ = (max |τ| b) ^ k * (c ^ k * ((1 + |τ|) ^ k)⁻¹) := by ring
    _ = c ^ k * ((1 + |τ|) ^ k)⁻¹ * (max |τ| b) ^ k := by ring

theorem integral_max_inv_pow_le (b : ℝ) (hb : 0 < b) (k : ℕ) (hk : 2 ≤ k) :
    ∫ τ : ℝ, ((max |τ| b) ^ k)⁻¹ ≤ 4 * (b ^ (k - 1))⁻¹ := by
  set f : ℝ → ℝ := fun x => ((max x b) ^ k)⁻¹ with hf
  have hfi := integrable_max_inv_pow b hb k hk
  rw [show (fun τ : ℝ => ((max |τ| b) ^ k)⁻¹) = fun τ => f |τ| from rfl, integral_comp_abs]
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  -- the two pieces
  have hfIoi : IntegrableOn f (Ioi b) := by
    have := integrableOn_Ioi_rpow_of_lt (a := -(k : ℝ)) (by linarith) hb
    refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [hf, mem_Ioi] at hx ⊢
    rw [max_eq_left hx.le, Real.rpow_neg (by linarith), Real.rpow_natCast]
  have hfIoc : IntegrableOn f (Ioc 0 b) := by
    have hc : IntegrableOn (fun _ : ℝ => ((b ^ k)⁻¹ : ℝ)) (Ioc 0 b) :=
      (continuous_const.integrableOn_Icc (a := 0) (b := b)).mono_set Ioc_subset_Icc_self
    refine hc.congr_fun (fun x hx => ?_) measurableSet_Ioc
    simp only [hf, mem_Ioc] at hx ⊢
    rw [max_eq_right hx.2]
  rw [← Ioc_union_Ioi_eq_Ioi hb.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    hfIoc hfIoi]
  have e1 : ∫ x in Ioc 0 b, f x = b * (b ^ k)⁻¹ := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (b ^ k)⁻¹) (fun x hx => by
      simp only [hf, mem_Ioc] at hx ⊢; rw [max_eq_right hx.2])]
    simp [hb.le]
  have e2 : ∫ x in Ioi b, f x = (b ^ (k - 1))⁻¹ / ((k : ℝ) - 1) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun x => x ^ (-(k : ℝ))) (fun x hx => by
      simp only [hf, mem_Ioi] at hx ⊢
      rw [max_eq_left hx.le, Real.rpow_neg (by linarith), Real.rpow_natCast]),
      integral_Ioi_rpow_of_lt (by linarith) hb]
    rw [show -(k : ℝ) + 1 = -((k - 1 : ℕ) : ℝ) by push_cast [show 1 ≤ k by omega]; ring,
      Real.rpow_neg hb.le, Real.rpow_natCast]
    push_cast [show 1 ≤ k by omega]
    field_simp
  rw [e1, e2]
  have hbk : b * (b ^ k)⁻¹ = (b ^ (k - 1))⁻¹ := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]; field_simp
  rw [hbk]
  have hpos : 0 < (b ^ (k - 1))⁻¹ := by positivity
  have : (b ^ (k - 1))⁻¹ / ((k : ℝ) - 1) ≤ (b ^ (k - 1))⁻¹ := by
    rw [div_le_iff₀ (by linarith)]
    have : (1 : ℝ) ≤ k - 1 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    nlinarith
  linarith

end FourSquaresCaps
