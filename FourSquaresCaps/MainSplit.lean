/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.ErrorTotal

/-!
# Splitting off the `c = 0` term; it depends on the center only through `|A|²`

* `prod_mTerm_zero`: `∏ᵢ Mᵢ(τ, 0) = exp(π |A|² / (L⁴ D) − π |A|² / L²)`, `D = 1/L² − 2iτ`.
* `aq_inv_pow_four`: `(a_q^{-1/2})⁴ = a_q^{-2}`.
-/

@[expose] public section

namespace FourSquaresCaps

open Complex Real Finset MeasureTheory FourierTransform

theorem aq_inv_pow_four (z : ℂ) : (1 / z ^ (1 / 2 : ℂ)) ^ 4 = 1 / z ^ 2 := by
  have h : (z ^ (1 / 2 : ℂ)) ^ 2 = z := by
    rw [show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by push_cast; ring]
    exact cpow_nat_inv_pow z two_ne_zero
  rw [div_pow, one_pow, show (z ^ (1 / 2 : ℂ)) ^ 4 = ((z ^ (1 / 2 : ℂ)) ^ 2) ^ 2 by ring, h]

theorem mTerm_zero (A L t : ℝ) (hL : L ≠ 0) (q : ℕ) [NeZero q] :
    mTerm A L t q 0 = cexp (π * A ^ 2 / (L ^ 4 * (1 / L ^ 2 - 2 * I * t)) - π * A ^ 2 / L ^ 2) := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hD : (1 : ℂ) / L ^ 2 - 2 * I * t ≠ 0 := by
    intro h
    have h2 := congrArg Complex.re h
    simp [sq] at h2
    exact hL (by simpa using h2)
  unfold mTerm
  congr 1
  rw [zero_add]
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- `∏ᵢ Mᵢ(τ, 0)` depends only on `∑ Aᵢ²`. -/
theorem prod_mTerm_zero (A : Fin 4 → ℝ) (L t : ℝ) (hL : L ≠ 0) (q : ℕ) [NeZero q] :
    ∏ i, mTerm (A i) L t q ((0 : ℤ) : ℂ) =
      cexp (π * (∑ i, A i ^ 2 : ℝ) / (L ^ 4 * (1 / L ^ 2 - 2 * I * t)) -
        π * (∑ i, A i ^ 2 : ℝ) / L ^ 2) := by
  simp only [Int.cast_zero]
  simp_rw [mTerm_zero _ L t hL q]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [sum_sub_distrib, mul_sum, sum_div, sum_div]

/-- The `u`-terms of the assembly are integrable. -/
theorem integrable_units_term (A : Fin 4 → ℝ) (L : ℝ) (hL : L ≠ 0) (m : ℤ) (F : ℝ → ℂ)
    (hF : Integrable F) (k : ℕ) (u : (ZMod (k + 1))ˣ) :
    Integrable (fun τ => F τ *
      (cexp (-(2 * π * I * (alphaU k u τ : ℂ) * m)) * ∏ i, thetaW (A i) L (alphaU k u τ))) := by
  set Θ := ∏ i, ∑' x : ℤ, ‖gTerm (A i) L 0 x‖
  have hα : Continuous (fun τ => alphaU k u τ) := by unfold alphaU; fun_prop
  refine hF.mul_bdd (c := Θ) ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    refine Continuous.mul (by fun_prop) ?_
    exact continuous_finsetProd _ fun i _ => (continuous_thetaW (A i) L hL).comp hα
  · refine Filter.Eventually.of_forall fun τ => ?_
    rw [norm_mul, norm_prod]
    have h1 : ‖cexp (-(2 * π * I * (alphaU k u τ : ℂ) * m))‖ = 1 := by
      rw [show -(2 * π * I * (alphaU k u τ : ℂ) * m) =
        ((-(2 * π * alphaU k u τ * m) : ℝ) : ℂ) * I by push_cast; ring]
      exact norm_exp_ofReal_mul_I _
    rw [h1, one_mul]
    exact prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => norm_thetaW_le _ _ _ hL

/-- `F · X` is integrable, `X = e(−τm) a⁻² ∑_c S(c) ∏ M(c)`. -/
theorem integrable_FX (A : Fin 4 → ℝ) (L : ℝ) (hL : L ≠ 0) (m : ℤ) (F : ℝ → ℂ)
    (hF : Integrable F) (k : ℕ) :
    Integrable (fun τ => F τ * (cexp (-(2 * π * I * (τ : ℂ) * m)) *
      (1 / (((k + 1 : ℕ) : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * τ)) ^ (1 / 2 : ℂ)) ^ 4 *
      ∑' c : Fin 4 → ℤ, expSumS (m : ZMod (k + 1)) (fun i => (c i : ZMod (k + 1))) *
        ∏ i, mTerm (A i) L τ (k + 1) (c i))) := by
  have := integrable_finsetSum (univ : Finset (ZMod (k + 1))ˣ)
    (fun u _ => integrable_units_term A L hL m F hF k u)
  refine this.congr (Filter.Eventually.of_forall fun τ => ?_)
  simp only
  rw [← mul_sum, sum_units_theta A L hL k m τ]

theorem summable_S_mTerm (A : Fin 4 → ℝ) (L : ℝ) (hL0 : 0 < L) (m : ℤ) (q : ℕ) [NeZero q]
    (τ : ℝ) : Summable (fun c : Fin 4 → ℤ =>
      expSumS (m : ZMod q) (fun i => (c i : ZMod q)) * ∏ i, mTerm (A i) L τ q (c i)) := by
  have hσ := sig_pos L τ hL0 q
  refine Summable.of_norm_bounded
    (((tsum_gauss4_le _ hσ (fun i => 2 * τ * q * A i)).1).mul_left ((q.totient : ℝ) * (2 * q) ^ 2))
    fun c => ?_
  rw [norm_mul, norm_prod_mTerm A L τ hL0 q c]
  exact mul_le_mul_of_nonneg_right (norm_expSumS_le _ _) (Real.exp_pos _).le

/-- `F · Y` is integrable, `Y = e(−τm) a⁻² S(0) ∏ M(0)`. -/
theorem integrable_FY (A : Fin 4 → ℝ) (L : ℝ) (hL0 : 0 < L) (m : ℤ) (F : ℝ → ℂ)
    (hF : Integrable F) (k : ℕ) :
    Integrable (fun τ => F τ * (cexp (-(2 * π * I * (τ : ℂ) * m)) *
      (1 / (((k + 1 : ℕ) : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * τ)) ^ (1 / 2 : ℂ)) ^ 4 *
      (expSumS (m : ZMod (k + 1)) (fun i => ((0 : Fin 4 → ℤ) i : ZMod (k + 1))) *
        ∏ i, mTerm (A i) L τ (k + 1) ((0 : Fin 4 → ℤ) i)))) := by
  have hL : L ≠ 0 := hL0.ne'
  set S0 := expSumS (m : ZMod (k + 1)) (fun i => ((0 : Fin 4 → ℤ) i : ZMod (k + 1)))
  refine hF.mul_bdd (c := L ^ 4 / ((k + 1 : ℕ) : ℝ) ^ 4 * ‖S0‖) ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    simp only [Pi.zero_apply]
    simp_rw [prod_mTerm_zero A L _ hL (k + 1), aq_inv_pow_four]
    fun_prop
  · refine Filter.Eventually.of_forall fun τ => ?_
    have he : ‖cexp (-(2 * π * I * (τ : ℂ) * m))‖ = 1 := by
      rw [show -(2 * π * I * (τ : ℂ) * m) = ((-(2 * π * τ * m)) : ℝ) * I by push_cast; ring]
      exact norm_exp_ofReal_mul_I _
    have hq : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    rw [norm_mul, norm_mul, he, one_mul, norm_aq_inv_pow L τ hL (k + 1), norm_mul,
      norm_prod_mTerm A L τ hL0 (k + 1) 0]
    have h1 : Real.exp (-π * ∑ i, ((((0 : Fin 4 → ℤ) i : ℤ) : ℝ) - 2 * τ * ((k + 1 : ℕ) : ℝ) *
        A i) ^ 2 / sig L τ (k + 1) ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ ∑ i, ((((0 : Fin 4 → ℤ) i : ℤ) : ℝ) - 2 * τ * ((k + 1 : ℕ) : ℝ) * A i) ^ 2 /
          sig L τ (k + 1) ^ 2 := sum_nonneg fun i _ => by positivity
      nlinarith [pi_pos]
    have h2 : L ^ 4 / (((k + 1 : ℕ) : ℝ) ^ 4 * (1 + 4 * τ ^ 2 * L ^ 4)) ≤
        L ^ 4 / ((k + 1 : ℕ) : ℝ) ^ 4 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have : (0 : ℝ) ≤ 4 * τ ^ 2 * L ^ 4 := by positivity
      nlinarith [pow_pos hq 4]
    calc L ^ 4 / (((k + 1 : ℕ) : ℝ) ^ 4 * (1 + 4 * τ ^ 2 * L ^ 4)) * (‖S0‖ * Real.exp _)
        ≤ L ^ 4 / ((k + 1 : ℕ) : ℝ) ^ 4 * (‖S0‖ * 1) := by gcongr
      _ = L ^ 4 / ((k + 1 : ℕ) : ℝ) ^ 4 * ‖S0‖ := by ring

/-- The weighted count `N_A(m)`. -/
noncomputable def countW (A : Fin 4 → ℝ) (L : ℝ) (m : ℤ) : ℂ :=
  ∑' x : Fin 4 → ℤ, (if ∑ i, x i ^ 2 = m then wt A L x else 0)

/-- `N_A(m) = M(A) + R(A)` with `M(A) = ∑_k ∫ F_k · (c = 0 term)`. -/
theorem countW_eq (A : Fin 4 → ℝ) (L : ℝ) (hL0 : 0 < L) (m : ℤ)
    {ω η : ℝ → ℝ} {Q C E : ℝ} (h : DFIOmega ω Q C) (hη : DFIEta η E) (D : ℕ)
    (hD : 2 * Q ≤ D) (hTD : 4 * Q ^ 2 / 2 ≤ D) (hsum : ∑ k ∈ range D, ω ((k : ℝ) + 1) = 1) :
    countW A L m =
      (∑ k ∈ range D, ∫ τ, 𝓕 (fun u => (hW ω η D (k + 1) (4 * Q ^ 2) u : ℂ)) τ *
        (cexp (-(2 * π * I * (τ : ℂ) * m)) *
          (1 / (((k + 1 : ℕ) : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * τ)) ^ (1 / 2 : ℂ)) ^ 4 *
          (expSumS (m : ZMod (k + 1)) (fun i => ((0 : Fin 4 → ℤ) i : ZMod (k + 1))) *
            ∏ i, mTerm (A i) L τ (k + 1) ((0 : Fin 4 → ℤ) i)))) +
      ∑ k ∈ range D, ∫ τ, 𝓕 (fun u => (hW ω η D (k + 1) (4 * Q ^ 2) u : ℂ)) τ *
        (cexp (-(2 * π * I * (τ : ℂ) * m)) *
          (1 / (((k + 1 : ℕ) : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * τ)) ^ (1 / 2 : ℂ)) ^ 4 *
          ∑' c : Fin 4 → ℤ, (if c = 0 then 0 else
            expSumS (m : ZMod (k + 1)) (fun i => (c i : ZMod (k + 1))) *
              ∏ i, mTerm (A i) L τ (k + 1) (c i))) := by
  have hL : L ≠ 0 := hL0.ne'
  have hQ0 : 0 < Q := lt_of_lt_of_le one_pos h.one_le
  have hT0 : (0 : ℝ) < 4 * Q ^ 2 := by positivity
  unfold countW
  rw [count_formula A L hL m h hη D hD hT0 hTD hsum, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  have hF : Integrable (𝓕 (fun u => (hW ω η D (k + 1) (4 * Q ^ 2) u : ℂ))) :=
    integrable_fourier_of_smooth (contDiff_hW h hη D (k + 1) (by omega) _)
      (hasCompactSupport_hW hη D (k + 1) hT0)
  set F := 𝓕 (fun u => (hW ω η D (k + 1) (4 * Q ^ 2) u : ℂ))
  have hX := integrable_FX A L hL m F hF k
  have hY := integrable_FY A L hL0 m F hF k
  have hpt : ∀ τ : ℝ, F τ * (cexp (-(2 * π * I * (τ : ℂ) * m)) *
      (1 / (((k + 1 : ℕ) : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * τ)) ^ (1 / 2 : ℂ)) ^ 4 *
      ∑' c : Fin 4 → ℤ, expSumS (m : ZMod (k + 1)) (fun i => (c i : ZMod (k + 1))) *
        ∏ i, mTerm (A i) L τ (k + 1) (c i)) =
      F τ * (cexp (-(2 * π * I * (τ : ℂ) * m)) *
        (1 / (((k + 1 : ℕ) : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * τ)) ^ (1 / 2 : ℂ)) ^ 4 *
        (expSumS (m : ZMod (k + 1)) (fun i => ((0 : Fin 4 → ℤ) i : ZMod (k + 1))) *
          ∏ i, mTerm (A i) L τ (k + 1) ((0 : Fin 4 → ℤ) i))) +
      F τ * (cexp (-(2 * π * I * (τ : ℂ) * m)) *
        (1 / (((k + 1 : ℕ) : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * τ)) ^ (1 / 2 : ℂ)) ^ 4 *
        ∑' c : Fin 4 → ℤ, (if c = 0 then 0 else
          expSumS (m : ZMod (k + 1)) (fun i => (c i : ZMod (k + 1))) *
            ∏ i, mTerm (A i) L τ (k + 1) (c i))) := by
    intro τ
    classical
    rw [(summable_S_mTerm A L hL0 m (k + 1) τ).tsum_eq_add_tsum_ite 0]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  refine integral_add hY ?_
  exact (hX.sub hY).congr (Filter.Eventually.of_forall fun τ => by
    simp only [Pi.sub_apply]; rw [hpt τ]; ring)

/-- **Comparison of two centers with `|A| = |A'|`.** -/
theorem countW_sub_le (A A' : Fin 4 → ℝ) (hAA : ∑ i, A i ^ 2 = ∑ i, A' i ^ 2)
    (L : ℝ) (hL0 : 0 < L) (m : ℤ)
    {ω η : ℝ → ℝ} {Q C E : ℝ} (h : DFIOmega ω Q C) (hη : DFIEta η E) (D : ℕ)
    (hD : 2 * Q ≤ D) (hTD : 4 * Q ^ 2 / 2 ≤ D) (hsum : ∑ k ∈ range D, ω ((k : ℝ) + 1) = 1)
    (Amax : ℝ) (hAmax : 0 < Amax) (hA : ∀ i, |A i| ≤ Amax) (hA' : ∀ i, |A' i| ≤ Amax)
    (g : ℕ → ℕ) (hg : ∀ q, q ≠ 0 → ∃ q₀, GoodDecomp (2 * m.natAbs) q q₀ (g q)) :
    ‖countW A L m - countW A' L m‖ ≤
      2 * (4 * (C * E) * errXi Q (4 * Q ^ 2) L Amax *
        ∑ q ∈ Icc 1 ⌊2 * Q⌋₊, (2 : ℝ) ^ (g q).primeFactors.card / Real.sqrt (g q)) := by
  have hL : L ≠ 0 := hL0.ne'
  rw [countW_eq A L hL0 m h hη D hD hTD hsum, countW_eq A' L hL0 m h hη D hD hTD hsum]
  have hmain : ∀ k τ, (∏ i, mTerm (A i) L τ (k + 1) ((0 : Fin 4 → ℤ) i)) =
      ∏ i, mTerm (A' i) L τ (k + 1) ((0 : Fin 4 → ℤ) i) := by
    intro k τ
    simp only [Pi.zero_apply]
    rw [prod_mTerm_zero A L τ hL (k + 1), prod_mTerm_zero A' L τ hL (k + 1), hAA]
  simp_rw [hmain]
  rw [add_sub_add_left_eq_sub]
  refine (norm_sub_le _ _).trans ?_
  have h1 := error_total_le A L hL0 m h hη D Amax hAmax hA g hg
  have h2 := error_total_le A' L hL0 m h hη D Amax hAmax hA' g hg
  linarith

end FourSquaresCaps
