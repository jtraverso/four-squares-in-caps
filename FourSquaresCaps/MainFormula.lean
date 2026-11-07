/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.DFIL1
public import FourSquaresCaps.Assembly

/-!
# The exact formula for the weighted number of representations

* `delta_hW`: `1[n = 0] = ∑_{q ≤ D} c_q(n) h_q(n)` for every integer `n` (cut-off DFI identity).
* `count_formula`: `∑_{|x|² = m} W(x) = ∑_q ∫ F_q(τ) e(−τm) a_q^{-2} ∑_{c ∈ ℤ⁴} S_q(m, c) ∏ Mᵢ(cᵢ) dτ`,
  `F_q = 𝓕 h_q`.
-/

@[expose] public section

namespace FourSquaresCaps

open MeasureTheory Real FourierTransform Finset Complex

/-- **The cut-off DFI identity.** -/
theorem delta_hW {ω η : ℝ → ℝ} {Q C E : ℝ} (h : DFIOmega ω Q C) (hη : DFIEta η E) (D : ℕ)
    (hD : 2 * Q ≤ D) {T : ℝ} (hT0 : 0 < T) (hTD : T / 2 ≤ D)
    (hsum : ∑ k ∈ range D, ω ((k : ℝ) + 1) = 1) (n : ℤ) :
    (if n = 0 then (1 : ℂ) else 0) =
      ∑ k ∈ range D, ram k n * (hW ω η D (k + 1) T n : ℂ) := by
  by_cases hn : |(n : ℝ)| ≤ T / 2
  · have hnD : n.natAbs ≤ D := by
      have : ((n.natAbs : ℕ) : ℝ) ≤ D := by
        rw [Nat.cast_natAbs, Int.cast_abs]; linarith
      exact_mod_cast this
    have hd := delta_units ω D (fun y hy => h.zero_out y (Or.inl (by linarith [h.one_le])))
      (fun y hy => h.zero_out y (Or.inr (by linarith))) hsum n hnD
    simp only [hW]
    push_cast
    have : ∑ k ∈ range D, ram k n * ((η (T⁻¹ * n) : ℂ) * (deltaW ω D (k + 1) n : ℂ)) =
        (η (T⁻¹ * n) : ℂ) * ∑ k ∈ range D, ram k n * (deltaW ω D (k + 1) n : ℂ) := by
      rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
    rw [this, hd]
    split_ifs with h0
    · subst h0; simp [hη.at_zero]
    · simp
  · push Not at hn
    have hn0 : n ≠ 0 := by
      rintro rfl; simp at hn; linarith
    simp only [hn0, ↓reduceIte]
    symm
    refine sum_eq_zero fun k _ => ?_
    rw [hW_eq_zero hη D (k + 1) hT0 _ hn]
    simp

theorem norm_thetaW_le (A L α : ℝ) (hL : L ≠ 0) :
    ‖thetaW A L α‖ ≤ ∑' x : ℤ, ‖gTerm A L 0 x‖ := by
  unfold thetaW
  refine (norm_tsum_le_tsum_norm (summable_norm_gTerm A L α hL)).trans (le_of_eq ?_)
  exact tsum_congr fun x => norm_gTerm A L α x

theorem continuous_thetaW (A L : ℝ) (hL : L ≠ 0) : Continuous (thetaW A L) := by
  unfold thetaW
  refine continuous_tsum (fun x => ?_) (summable_norm_gTerm A L 0 hL)
    (fun x α => (norm_gTerm A L α x).le)
  unfold gTerm
  fun_prop

/-- **The exact formula.** -/
theorem count_formula (A : Fin 4 → ℝ) (L : ℝ) (hL : L ≠ 0) (m : ℤ)
    {ω η : ℝ → ℝ} {Q C E : ℝ} (h : DFIOmega ω Q C) (hη : DFIEta η E) (D : ℕ)
    (hD : 2 * Q ≤ D) {T : ℝ} (hT0 : 0 < T) (hTD : T / 2 ≤ D)
    (hsum : ∑ k ∈ range D, ω ((k : ℝ) + 1) = 1) :
    ∑' x : Fin 4 → ℤ, (if ∑ i, x i ^ 2 = m then wt A L x else 0) =
      ∑ k ∈ range D, ∫ τ, 𝓕 (fun u => (hW ω η D (k + 1) T u : ℂ)) τ *
        (cexp (-(2 * π * I * (τ : ℂ) * m)) *
          (1 / (((k + 1 : ℕ) : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * τ)) ^ (1 / 2 : ℂ)) ^ 4 *
          ∑' c : Fin 4 → ℤ, expSumS (m : ZMod (k + 1)) (fun i => (c i : ZMod (k + 1))) *
            ∏ i, mTerm (A i) L τ (k + 1) (c i)) := by
  have hsm : ∀ k : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (hW ω η D (k + 1) T) :=
    fun k => contDiff_hW h hη D (k + 1) (by omega) T
  have hcs : ∀ k : ℕ, HasCompactSupport (hW ω η D (k + 1) T) :=
    fun k => hasCompactSupport_hW hη D (k + 1) hT0
  rw [count_eq A L hL m D (fun k n => (hW ω η D (k + 1) T n : ℂ))
    (fun k => 𝓕 (fun u => (hW ω η D (k + 1) T u : ℂ)))
    (delta_hW h hη D hD hT0 hTD hsum)
    (fun k n => by
      have := eq_integral_fourier (hsm k) (hcs k) (n : ℝ)
      push_cast at this ⊢
      exact this)
    (fun k => integrable_fourier_of_smooth (hsm k) (hcs k))]
  refine sum_congr rfl fun k _ => ?_
  set Θ := ∏ i, ∑' x : ℤ, ‖gTerm (A i) L 0 x‖ with hΘ
  have hint : ∀ u ∈ (univ : Finset (ZMod (k + 1))ˣ), Integrable (fun τ =>
      𝓕 (fun u => (hW ω η D (k + 1) T u : ℂ)) τ *
        (cexp (-(2 * π * I * (alphaU k u τ : ℂ) * m)) * ∏ i, thetaW (A i) L (alphaU k u τ))) := by
    intro u _
    have hα : Continuous (fun τ => alphaU k u τ) := by unfold alphaU; fun_prop
    refine (integrable_fourier_of_smooth (hsm k) (hcs k)).mul_bdd (c := Θ) ?_ ?_
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
  rw [← integral_finsetSum _ hint]
  congr 1
  ext τ
  rw [← mul_sum, sum_units_theta A L hL k m τ]

end FourSquaresCaps
