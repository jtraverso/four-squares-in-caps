/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.DFIFourier
public import FourSquaresCaps.Integrals
public import FourSquaresCaps.FourierBound
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Fourier.Inversion

/-!
# `L¹` norms of the cut-off DFI weight and the Fourier bounds

With `a = qQ`, `2a ≤ T`:
* `integral_abs_hW_le`: `∫ |h| ≤ 6CE T / a`;
* `integral_abs_deriv_hW_le`: `∫ |h'| ≤ 6CE (3 + 2 log(T/(2a))) / a`;
* `integral_abs_iteratedDeriv_four_hW_le`: `∫ |h⁗| ≤ 656 CE / a⁴`;
* `norm_fourier_hW_le`: the three resulting bounds for `‖𝓕 h(τ)‖`.
-/

@[expose] public section

namespace FourSquaresCaps

open MeasureTheory Real FourierTransform intervalIntegral

theorem integral_abs_le_of_support (f g : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c) (hf : Continuous f)
    (hz : ∀ u, c < |u| → f u = 0) (hg : Continuous g) (hle : ∀ u, |u| ≤ c → |f u| ≤ g u) :
    ∫ u, |f u| ≤ ∫ u in -c..c, g u := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc (-c) c) (fun u hu => by
    have : c < |u| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hu
      rcases hu with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h
    rw [hz u this, abs_zero])]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  exact intervalIntegral.integral_mono_on (by linarith) (hf.abs.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _) fun u hu => hle u (abs_le.mpr ⟨hu.1, hu.2⟩)

theorem b4_eq (a u : ℝ) : b4 a u = ((max |u| a) ^ 4)⁻¹ := by
  unfold b4
  split_ifs with h
  · rw [max_eq_right h.le]
  · rw [max_eq_left (not_lt.mp h)]

theorem b1_le (a u : ℝ) (ha : 0 < a) : b1 a u ≤ ((max |u| a) ^ 1)⁻¹ := by
  unfold b1
  split_ifs with h
  · rw [pow_one]; exact (inv_pos.mpr (lt_of_lt_of_le ha (le_max_right _ _))).le
  · rw [max_eq_left (not_lt.mp h), pow_one]

section

variable {ω η : ℝ → ℝ} {Q C E : ℝ} (h : DFIOmega ω Q C) (hη : DFIEta η E) (D q : ℕ) (hq : 1 ≤ q)
  {T : ℝ} (hT : 2 * (q * Q) ≤ T)
include h hη hq hT

theorem integral_abs_hW_le :
    ∫ u, |hW ω η D q T u| ≤ 6 * C * E * T / (q * Q) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ : 0 < Q := lt_of_lt_of_le one_pos h.one_le
  have hT0 : 0 < T := by nlinarith
  refine (integral_abs_le_of_support _ (fun _ => 6 * C * E / (q * Q)) (T / 2) (by linarith)
    (contDiff_hW h hη D q hq T).continuous (fun u hu => hW_eq_zero hη D q hT0 u hu)
    continuous_const fun u _ => abs_hW_le h hη D q hq T u).trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring

theorem integral_abs_deriv_hW_le :
    ∫ u, |iteratedDeriv 1 (hW ω η D q T) u| ≤
      6 * C * E / (q * Q) * (3 + 2 * Real.log (T / (2 * (q * Q)))) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ : 0 < Q := lt_of_lt_of_le one_pos h.one_le
  have hqQ : 0 < (q : ℝ) * Q := by positivity
  have hT0 : 0 < T := by nlinarith
  have hC := h.C_nonneg
  have hE : 0 ≤ E := (abs_nonneg _).trans (hη.bound 0 (by norm_num) 0)
  have hK : 0 ≤ 6 * C * E / (q * Q) := by positivity
  have hcont := continuous_max_inv_pow (q * Q) hqQ 1
  refine (integral_abs_le_of_support _
    (fun u => 6 * C * E / (q * Q) * (((max |u| (q * Q)) ^ 1)⁻¹ + T⁻¹)) (T / 2) (by linarith)
    ((contDiff_hW h hη D q hq T).continuous_iteratedDeriv 1 (by exact_mod_cast le_top))
    (fun u hu => iteratedDeriv_hW_eq_zero hη D q hT0 1 u hu)
    (continuous_const.mul ((hcont.comp continuous_abs).add continuous_const))
    fun u _ => (abs_deriv_hW_le h hη D q hq hT0 u).trans ?_).trans ?_
  · gcongr; exact b1_le _ _ hqQ
  · have hii : IntervalIntegrable (fun u => ((max |u| ((q : ℝ) * Q)) ^ 1)⁻¹) volume
        (-(T / 2)) (T / 2) := (hcont.comp continuous_abs).intervalIntegrable _ _
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hii intervalIntegrable_const, intervalIntegral.integral_const]
    have hI := integral_max_inv_le (q * Q) (T / 2) hqQ (by linarith)
    simp only [smul_eq_mul] at *
    have e : T / 2 / (q * Q) = T / (2 * (q * Q)) := by ring
    rw [e] at hI
    have e2 : (T / 2 - -(T / 2)) * T⁻¹ = 1 := by field_simp; ring
    apply mul_le_mul_of_nonneg_left _ hK
    linarith

theorem integral_abs_iteratedDeriv_four_hW_le :
    ∫ u, |iteratedDeriv 4 (hW ω η D q T) u| ≤ 656 * C * E / (q * Q) ^ 4 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ : 0 < Q := lt_of_lt_of_le one_pos h.one_le
  have hqQ : 0 < (q : ℝ) * Q := by positivity
  have hT0 : 0 < T := by nlinarith
  have hC := h.C_nonneg
  have hE : 0 ≤ E := (abs_nonneg _).trans (hη.bound 0 (by norm_num) 0)
  have hcont := continuous_max_inv_pow (q * Q) hqQ 4
  have hck : ∀ k : ℕ, Continuous (iteratedDeriv k (hW ω η D q T)) := fun k =>
    (contDiff_hW h hη D q hq T).continuous_iteratedDeriv k (by exact_mod_cast le_top)
  refine (integral_abs_le_of_support _
    (fun u => 246 * C * E / (q * Q) * ((max |u| (q * Q)) ^ 4)⁻¹) (T / 2) (by linarith)
    (hck 4)
    (fun u hu => iteratedDeriv_hW_eq_zero hη D q hT0 4 u hu)
    (continuous_const.mul (hcont.comp continuous_abs))
    fun u _ => (abs_iteratedDeriv_hW_four_le h hη D q hq hT u).trans (le_of_eq (by
      rw [b4_eq]))).trans ?_
  rw [intervalIntegral.integral_const_mul]
  have hI := integral_max_inv_pow_four_le (q * Q) (T / 2) hqQ (by linarith)
  calc 246 * C * E / (q * Q) * ∫ u in -(T / 2)..T / 2, ((max |u| (q * Q)) ^ 4)⁻¹
      ≤ 246 * C * E / (q * Q) * (8 / 3 * (((q : ℝ) * Q) ^ 3)⁻¹) := by gcongr
    _ = 656 * C * E / (q * Q) ^ 4 := by field_simp; ring

/-- **Fourier bounds for the cut-off DFI weight.** -/
theorem norm_fourier_hW_le (τ : ℝ) :
    ‖𝓕 (fun u => (hW ω η D q T u : ℂ)) τ‖ ≤ 6 * C * E * T / (q * Q) ∧
    (2 * π * |τ|) * ‖𝓕 (fun u => (hW ω η D q T u : ℂ)) τ‖ ≤
      6 * C * E / (q * Q) * (3 + 2 * Real.log (T / (2 * (q * Q)))) ∧
    (2 * π * |τ|) ^ 4 * ‖𝓕 (fun u => (hW ω η D q T u : ℂ)) τ‖ ≤ 656 * C * E / (q * Q) ^ 4 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ : 0 < Q := lt_of_lt_of_le one_pos h.one_le
  have hT0 : 0 < T := by nlinarith
  have hsm := contDiff_hW h hη D q hq T
  have hcs : HasCompactSupport (hW ω η D q T) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -(T / 2)) (b := T / 2)) fun u hu => ?_
    refine hW_eq_zero hη D q hT0 u ?_
    simp only [Set.mem_Icc, not_and_or, not_le] at hu
    rcases hu with h' | h'
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; exact h'
  refine ⟨?_, ?_, ?_⟩
  · have := fourier_decay hsm hcs 0 τ
    simp only [pow_zero, one_mul, iteratedDeriv_zero] at this
    exact this.trans (integral_abs_hW_le h hη D q hq hT)
  · have := fourier_decay hsm hcs 1 τ
    rw [pow_one] at this
    exact this.trans (integral_abs_deriv_hW_le h hη D q hq hT)
  · exact (fourier_decay hsm hcs 4 τ).trans (integral_abs_iteratedDeriv_four_hW_le h hη D q hq hT)

end

theorem hasCompactSupport_hW {ω η : ℝ → ℝ} {E : ℝ} (hη : DFIEta η E) (D q : ℕ) {T : ℝ}
    (hT0 : 0 < T) : HasCompactSupport (hW ω η D q T) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(T / 2)) (b := T / 2)) fun u hu => ?_
  refine hW_eq_zero hη D q hT0 u ?_
  simp only [Set.mem_Icc, not_and_or, not_le] at hu
  rcases hu with h' | h'
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; exact h'

end FourSquaresCaps
