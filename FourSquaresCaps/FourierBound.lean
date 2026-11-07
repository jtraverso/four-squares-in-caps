/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Fourier.Inversion

/-!
# Fourier decay from derivatives

For a smooth compactly supported `h : ℝ → ℝ`:
`(2π|w|)^n ‖𝓕 h(w)‖ ≤ ∫ |h^{(n)}|` (`fourier_decay`).
-/

@[expose] public section

namespace FourSquaresCaps

open MeasureTheory Real FourierTransform

theorem hasCompactSupport_iteratedDeriv {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    ∀ n : ℕ, HasCompactSupport (iteratedDeriv n f)
  | 0 => by simpa using hf
  | n + 1 => by rw [iteratedDeriv_succ]; exact (hasCompactSupport_iteratedDeriv hf n).deriv

theorem norm_fourier_le_integral (g : ℝ → ℂ) (w : ℝ) : ‖𝓕 g w‖ ≤ ∫ v, ‖g v‖ := by
  rw [Real.fourier_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  ext v
  rw [Circle.norm_smul]

theorem norm_iteratedDeriv_ofReal {h : ℝ → ℝ} (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    (n : ℕ) (x : ℝ) : ‖iteratedDeriv n (fun u => (h u : ℂ)) x‖ = |iteratedDeriv n h x| := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← Real.norm_eq_abs,
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left (f := h) hsm.contDiffAt
    (by exact_mod_cast le_top)

/-- **Fourier decay.** -/
theorem fourier_decay {h : ℝ → ℝ} (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    (hcs : HasCompactSupport h) (n : ℕ) (w : ℝ) :
    (2 * π * |w|) ^ n * ‖𝓕 (fun u => (h u : ℂ)) w‖ ≤ ∫ u, |iteratedDeriv n h u| := by
  set hc : ℝ → ℂ := fun u => (h u : ℂ) with hhc
  have hcsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) hc := Complex.ofRealCLM.contDiff.comp hsm
  have hcs' : HasCompactSupport hc := hcs.comp_left Complex.ofReal_zero
  have hint : ∀ k : ℕ, Integrable (iteratedDeriv k hc) := by
    intro k
    refine (hcsm.continuous_iteratedDeriv k (by exact_mod_cast le_top)).integrable_of_hasCompactSupport
      ?_
    have : iteratedDeriv k hc = fun x => iteratedFDeriv ℝ k hc x (fun _ => 1) := by
      ext x; rw [iteratedDeriv_eq_iteratedFDeriv]
    rw [this]
    exact (hcs'.iteratedFDeriv k).mono fun x hx => by
      simp only [Function.mem_support, ne_eq] at hx ⊢
      intro h0; apply hx; rw [h0]; rfl
  have hF := fourier_iteratedDeriv (N := (n : ℕ∞)) (hcsm.of_le (by exact_mod_cast le_top))
    (fun k _ => hint k) le_rfl
  have key : ‖𝓕 (iteratedDeriv n hc) w‖ = (2 * π * |w|) ^ n * ‖𝓕 hc w‖ := by
    rw [hF]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos pi_pos]
  rw [← key]
  refine (norm_fourier_le_integral _ w).trans (le_of_eq ?_)
  congr 1
  ext u
  exact norm_iteratedDeriv_ofReal hsm n u

section

variable {h : ℝ → ℝ} (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) (hcs : HasCompactSupport h)
include hsm hcs

theorem integrable_ofReal_of_smooth : Integrable (fun u => (h u : ℂ)) :=
  (Complex.continuous_ofReal.comp hsm.continuous).integrable_of_hasCompactSupport
    (hcs.comp_left Complex.ofReal_zero)

theorem integrable_fourier_of_smooth : Integrable (𝓕 (fun u => (h u : ℂ))) := by
  set A := ∫ u, |iteratedDeriv 0 h u|
  set B := ∫ u, |iteratedDeriv 4 h u|
  have hcont : Continuous (𝓕 (fun u => (h u : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by fun_prop) (integrable_ofReal_of_smooth hsm hcs)
  have hdom : Integrable (fun τ : ℝ => 8 * (A + B) * (1 + ‖τ‖) ^ (-(4 : ℝ))) :=
    (integrable_one_add_norm (by norm_num)).const_mul _
  refine hdom.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun τ => ?_)
  have h0 := fourier_decay hsm hcs 0 τ
  have h4 := fourier_decay hsm hcs 4 τ
  rw [pow_zero, one_mul] at h0
  set F := ‖𝓕 (fun u => (h u : ℂ)) τ‖
  have hF0 : 0 ≤ F := norm_nonneg _
  have hpi : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
  have hx : |τ| ^ 4 ≤ (2 * π * |τ|) ^ 4 := by
    gcongr; nlinarith [abs_nonneg τ]
  have key : F * (1 + |τ| ^ 4) ≤ A + B := by nlinarith
  have hpos : 0 < 1 + |τ| := by positivity
  have hb : (1 + |τ|) ^ 4 ≤ 8 * (1 + |τ| ^ 4) := by
    nlinarith [sq_nonneg (|τ| - 1), sq_nonneg (|τ| + 1), abs_nonneg τ, sq_nonneg (|τ| ^ 2 - 1)]
  rw [Real.norm_eq_abs, Real.rpow_neg hpos.le, show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, le_mul_inv_iff₀ (by positivity)]
  calc F * (1 + |τ|) ^ 4 ≤ F * (8 * (1 + |τ| ^ 4)) := by gcongr
    _ = 8 * (F * (1 + |τ| ^ 4)) := by ring
    _ ≤ 8 * (A + B) := by linarith

/-- **Fourier inversion**: `h(x) = ∫ 𝓕h(τ) e(τ x) dτ`. -/
theorem eq_integral_fourier (x : ℝ) :
    (h x : ℂ) = ∫ τ, 𝓕 (fun u => (h u : ℂ)) τ * Complex.exp (2 * π * Complex.I * (τ : ℂ) * x) := by
  have hinv := MeasureTheory.Integrable.fourierInv_fourier_eq (integrable_ofReal_of_smooth hsm hcs)
    (integrable_fourier_of_smooth hsm hcs)
    (v := x) (Complex.continuous_ofReal.comp hsm.continuous).continuousAt
  rw [← hinv, fourierInv_eq']
  congr 1
  ext τ
  rw [smul_eq_mul, mul_comm]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

end

end FourSquaresCaps
