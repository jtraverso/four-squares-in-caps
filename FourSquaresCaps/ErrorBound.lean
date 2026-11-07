/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.ErrorTerm
public import FourSquaresCaps.ErrorIntegrals
public import FourSquaresCaps.Lattice

/-!
# The `c ≠ 0` sum at a fixed `τ`

`norm_prod_mTerm`: `‖∏ᵢ Mᵢ(cᵢ)‖ = exp(−π ∑ᵢ (cᵢ − yᵢ)²/σ²)`, `yᵢ = 2τqAᵢ`, `σ² = q²(1+s²)/L²`.
`tsum_ne_zero_le`: the weight `‖a^{-2}‖ ∑_{c≠0} ‖∏ Mᵢ(cᵢ)‖` is at most `1770 (1+s²)` when
`|τ| ≤ 1/(4 q A_max)` and at most `8(1+s²) + 128 (L/q)⁴/(1+s²)` always.
-/

@[expose] public section

namespace FourSquaresCaps

open Complex Real

/-- The width `σ = q √(1 + 4t²L⁴) / L`. -/
noncomputable def sig (L t : ℝ) (q : ℕ) : ℝ := q * Real.sqrt (1 + 4 * t ^ 2 * L ^ 4) / L

theorem sig_sq (L t : ℝ) (hL : 0 < L) (q : ℕ) :
    sig L t q ^ 2 = (q : ℝ) ^ 2 * (1 + 4 * t ^ 2 * L ^ 4) / L ^ 2 := by
  unfold sig
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]

theorem norm_prod_mTerm (A : Fin 4 → ℝ) (L t : ℝ) (hL0 : 0 < L) (q : ℕ) [NeZero q]
    (c : Fin 4 → ℤ) :
    ‖∏ i, mTerm (A i) L t q (c i)‖ = Real.exp (-π * ∑ i, (((c i : ℤ) : ℝ) - 2 * t * q * A i) ^ 2 /
      sig L t q ^ 2) := by
  have hL : L ≠ 0 := hL0.ne'
  rw [sig_sq L t hL0]
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hden : (0 : ℝ) < 1 + 4 * t ^ 2 * L ^ 4 := by positivity
  rw [norm_prod]
  simp only [show ∀ i, ((c i : ℤ) : ℂ) = (((c i : ℤ) : ℝ) : ℂ) from fun i => by push_cast; rfl]
  simp_rw [norm_mTerm _ L t hL q]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

theorem exp_mul_pow_le (σ : ℝ) (hσ : 0 < σ) :
    Real.exp (-π / (8 * σ ^ 2)) * (2 + Real.sqrt 2 * σ) ^ 4 ≤ 2000 * σ ^ 4 := by
  have hs2 : Real.sqrt 2 ≤ 1.4143 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hpi : 3.14 < π := Real.pi_gt_d2
  rcases le_or_gt 1 σ with h1 | h1
  · have he : Real.exp (-π / (8 * σ ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; apply div_nonpos_of_nonpos_of_nonneg <;> nlinarith [pi_pos]
    have hb : 2 + Real.sqrt 2 * σ ≤ 3.4143 * σ := by nlinarith
    have hb4 : (2 + Real.sqrt 2 * σ) ^ 4 ≤ (3.4143 * σ) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hb 4
    calc Real.exp (-π / (8 * σ ^ 2)) * (2 + Real.sqrt 2 * σ) ^ 4 ≤ 1 * (3.4143 * σ) ^ 4 :=
          mul_le_mul he hb4 (by positivity) (by norm_num)
      _ ≤ 2000 * σ ^ 4 := by rw [mul_pow]; nlinarith [pow_pos hσ 4]
  · have hb : 2 + Real.sqrt 2 * σ ≤ 3.4143 := by nlinarith
    have hb4 : (2 + Real.sqrt 2 * σ) ^ 4 ≤ 3.4143 ^ 4 := pow_le_pow_left₀ (by positivity) hb 4
    set x := π / (8 * σ ^ 2) with hx
    have hx0 : 0 < x := by positivity
    have hq := Real.quadratic_le_exp_of_nonneg hx0.le
    have he : Real.exp (-x) ≤ 2 / x ^ 2 := by
      rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos x)]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg x]
    have hx2 : 2 / x ^ 2 = 128 * σ ^ 4 / π ^ 2 := by rw [hx]; field_simp; ring
    rw [show -π / (8 * σ ^ 2) = -x by rw [hx]; ring]
    calc Real.exp (-x) * (2 + Real.sqrt 2 * σ) ^ 4 ≤ (128 * σ ^ 4 / π ^ 2) * 3.4143 ^ 4 :=
          mul_le_mul (he.trans (le_of_eq hx2)) hb4 (by positivity) (by positivity)
      _ ≤ 2000 * σ ^ 4 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          have : (9.8596 : ℝ) < π ^ 2 := by nlinarith
          nlinarith [pow_pos hσ 4]

theorem summable_gauss4_ite (σ : ℝ) (hσ : 0 < σ) (y : Fin 4 → ℝ) :
    Summable (fun c : Fin 4 → ℤ =>
      if c = 0 then 0 else Real.exp (-π * ∑ i, ((c i : ℝ) - y i) ^ 2 / σ ^ 2)) :=
  Summable.of_nonneg_of_le (fun c => by split_ifs <;> positivity)
    (fun c => by split_ifs <;> [exact (Real.exp_pos _).le; exact le_rfl])
    (tsum_gauss4_le σ hσ y).1

/-- The `c ≠ 0` Gaussian sum: `≤ (2+σ)⁴` always, `≤ 2000 σ⁴` when `|yᵢ| ≤ 1/2`. -/
theorem tsum_gauss4_ite_le (σ : ℝ) (hσ : 0 < σ) (y : Fin 4 → ℝ) :
    ∑' c : Fin 4 → ℤ, (if c = 0 then 0 else Real.exp (-π * ∑ i, ((c i : ℝ) - y i) ^ 2 / σ ^ 2))
      ≤ (2 + σ) ^ 4 ∧
    ((∀ i, |y i| ≤ 1 / 2) →
      ∑' c : Fin 4 → ℤ, (if c = 0 then 0 else Real.exp (-π * ∑ i, ((c i : ℝ) - y i) ^ 2 / σ ^ 2))
        ≤ 2000 * σ ^ 4) := by
  classical
  obtain ⟨hs, ht⟩ := tsum_gauss4_le σ hσ y
  refine ⟨((summable_gauss4_ite σ hσ y).tsum_le_tsum (fun c => by
    split_ifs <;> [exact (Real.exp_pos _).le; exact le_rfl]) hs).trans ht, fun hy => ?_⟩
  exact (tsum_gauss4_ne_zero_le σ hσ y hy).trans (exp_mul_pow_le σ hσ)

theorem sig_pos (L t : ℝ) (hL : 0 < L) (q : ℕ) [NeZero q] : 0 < sig L t q := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  unfold sig
  have : 0 < Real.sqrt (1 + 4 * t ^ 2 * L ^ 4) := Real.sqrt_pos.mpr (by positivity)
  positivity

/-- **The `c ≠ 0` part at a fixed `τ`.** -/
theorem error_integrand_le (A : Fin 4 → ℝ) (L : ℝ) (hL0 : 0 < L) (q : ℕ) [NeZero q] (m : ℤ)
    (Amax : ℝ) (hAmax : 0 < Amax) (hA : ∀ i, |A i| ≤ Amax) (B : ℝ)
    (hS : ∀ c : Fin 4 → ℤ, ‖expSumS (m : ZMod q) (fun i => (c i : ZMod q))‖ ≤ B) (τ : ℝ) :
    ‖cexp (-(2 * π * I * (τ : ℂ) * m)) *
        (1 / ((q : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * τ)) ^ (1 / 2 : ℂ)) ^ 4 *
        ∑' c : Fin 4 → ℤ, (if c = 0 then 0 else
          expSumS (m : ZMod q) (fun i => (c i : ZMod q)) * ∏ i, mTerm (A i) L τ q (c i))‖ ≤
      B * (2000 * (1 + 4 * τ ^ 2 * L ^ 4) +
        128 * (L / q) ^ 4 / (1 + 4 * τ ^ 2 * L ^ 4) *
          (if |τ| ≤ 1 / (4 * q * Amax) then 0 else 1)) := by
  classical
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hS 0)
  have hden : (0 : ℝ) < 1 + 4 * τ ^ 2 * L ^ 4 := by positivity
  set σ := sig L τ q with hσ
  have hσ0 : 0 < σ := sig_pos L τ hL0 q
  have hσ2 := sig_sq L τ hL0 q
  set y : Fin 4 → ℝ := fun i => 2 * τ * q * A i with hy
  set G := ∑' c : Fin 4 → ℤ,
    (if c = 0 then 0 else Real.exp (-π * ∑ i, ((c i : ℝ) - y i) ^ 2 / σ ^ 2)) with hG
  have he : ‖cexp (-(2 * π * I * (τ : ℂ) * m))‖ = 1 := by
    rw [show -(2 * π * I * (τ : ℂ) * m) = ((-(2 * π * τ * m)) : ℝ) * I by push_cast; ring]
    exact norm_exp_ofReal_mul_I _
  have hsum : ‖∑' c : Fin 4 → ℤ, (if c = 0 then 0 else
      expSumS (m : ZMod q) (fun i => (c i : ZMod q)) * ∏ i, mTerm (A i) L τ q (c i))‖ ≤ B * G := by
    have hterm : ∀ c : Fin 4 → ℤ, ‖(if c = 0 then 0 else
        expSumS (m : ZMod q) (fun i => (c i : ZMod q)) * ∏ i, mTerm (A i) L τ q (c i))‖ ≤
        B * (if c = 0 then 0 else Real.exp (-π * ∑ i, ((c i : ℝ) - y i) ^ 2 / σ ^ 2)) := by
      intro c
      split_ifs
      · simp
      · rw [norm_mul, norm_prod_mTerm A L τ hL0 q c]
        exact mul_le_mul_of_nonneg_right (hS c) (Real.exp_pos _).le
    have hsm := (summable_gauss4_ite σ hσ0 y).mul_left B
    refine (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsm)).trans ?_
    rw [hG, ← tsum_mul_left]
    exact (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsm).tsum_le_tsum hterm hsm
  rw [norm_mul, norm_mul, he, one_mul, norm_aq_inv_pow L τ hL0.ne' q]
  obtain ⟨hG1, hG2⟩ := tsum_gauss4_ite_le σ hσ0 y
  calc L ^ 4 / ((q : ℝ) ^ 4 * (1 + 4 * τ ^ 2 * L ^ 4)) * ‖_‖
      ≤ L ^ 4 / ((q : ℝ) ^ 4 * (1 + 4 * τ ^ 2 * L ^ 4)) * (B * G) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ B * (2000 * (1 + 4 * τ ^ 2 * L ^ 4) + 128 * (L / q) ^ 4 / (1 + 4 * τ ^ 2 * L ^ 4) *
          (if |τ| ≤ 1 / (4 * q * Amax) then 0 else 1)) := by
        rw [mul_left_comm]
        apply mul_le_mul_of_nonneg_left _ hB
        have hσ4 : σ ^ 4 = (q : ℝ) ^ 4 * (1 + 4 * τ ^ 2 * L ^ 4) ^ 2 / L ^ 4 := by
          rw [show σ ^ 4 = (σ ^ 2) ^ 2 by ring, hσ2]; field_simp
        split_ifs with hτ
        · have hyi : ∀ i, |y i| ≤ 1 / 2 := by
            intro i
            simp only [hy, abs_mul, abs_two, Nat.abs_cast]
            have h1 := hA i
            have h2 : |τ| * (4 * q * Amax) ≤ 1 := by
              rwa [le_div_iff₀ (by positivity)] at hτ
            calc 2 * |τ| * q * |A i| ≤ 2 * |τ| * q * Amax := by gcongr
              _ = (|τ| * (4 * q * Amax)) / 2 := by ring
              _ ≤ 1 / 2 := by linarith
          calc L ^ 4 / ((q : ℝ) ^ 4 * (1 + 4 * τ ^ 2 * L ^ 4)) * G
              ≤ L ^ 4 / ((q : ℝ) ^ 4 * (1 + 4 * τ ^ 2 * L ^ 4)) * (2000 * σ ^ 4) :=
                mul_le_mul_of_nonneg_left (hG2 hyi) (by positivity)
            _ = 2000 * (1 + 4 * τ ^ 2 * L ^ 4) := by rw [hσ4]; field_simp
            _ ≤ _ := by simp
        · have h8 : (2 + σ) ^ 4 ≤ 8 * (16 + σ ^ 4) := by
            nlinarith [sq_nonneg (σ - 2), sq_nonneg (σ ^ 2 - 4), sq_nonneg σ, pow_pos hσ0 3]
          calc L ^ 4 / ((q : ℝ) ^ 4 * (1 + 4 * τ ^ 2 * L ^ 4)) * G
              ≤ L ^ 4 / ((q : ℝ) ^ 4 * (1 + 4 * τ ^ 2 * L ^ 4)) * (8 * (16 + σ ^ 4)) :=
                mul_le_mul_of_nonneg_left (hG1.trans h8) (by positivity)
            _ = 8 * (1 + 4 * τ ^ 2 * L ^ 4) + 128 * (L / q) ^ 4 / (1 + 4 * τ ^ 2 * L ^ 4) := by
                rw [hσ4]; field_simp; ring
            _ ≤ _ := by
                rw [mul_one]
                have : 0 ≤ 1 + 4 * τ ^ 2 * L ^ 4 := hden.le
                linarith

/-- **The `c ≠ 0` part integrated.** With `‖F‖ ≤ B₀`, `|τ|‖F‖ ≤ B₁`, `τ⁴‖F‖ ≤ B₄`. -/
theorem error_q_le (A : Fin 4 → ℝ) (L : ℝ) (hL0 : 0 < L) (q : ℕ) [NeZero q] (m : ℤ)
    (Amax : ℝ) (hAmax : 0 < Amax) (hA : ∀ i, |A i| ≤ Amax) (B : ℝ)
    (hS : ∀ c : Fin 4 → ℤ, ‖expSumS (m : ZMod q) (fun i => (c i : ZMod q))‖ ≤ B)
    (F : ℝ → ℂ) (B0 B1 B4 a : ℝ) (ha : 0 < a)
    (hF0 : ∀ τ, ‖F τ‖ ≤ B0) (hF1 : ∀ τ, |τ| * ‖F τ‖ ≤ B1) (hF4 : ∀ τ, τ ^ 4 * ‖F τ‖ ≤ B4) :
    ‖∫ τ, F τ * (cexp (-(2 * π * I * (τ : ℂ) * m)) *
        (1 / ((q : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * τ)) ^ (1 / 2 : ℂ)) ^ 4 *
        ∑' c : Fin 4 → ℤ, (if c = 0 then 0 else
          expSumS (m : ZMod q) (fun i => (c i : ZMod q)) * ∏ i, mTerm (A i) L τ q (c i)))‖ ≤
      B * (8000 * max B0 (B4 * a ^ 4) / a + 32000 * L ^ 4 * max (B1 / a) (B4 * a ^ 2) / a +
        2048 * B1 * Amax ^ 2 / q ^ 2) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hS 0)
  have hB0 : 0 ≤ B0 := (norm_nonneg _).trans (hF0 0)
  have hB1 : 0 ≤ B1 := (mul_nonneg (abs_nonneg _) (norm_nonneg _)).trans (hF1 0)
  have hB4 : 0 ≤ B4 := (mul_nonneg (by positivity) (norm_nonneg _)).trans (hF4 0)
  set b := a⁻¹ with hb
  have hb0 : 0 < b := inv_pos.mpr ha
  set τ₀ := 1 / (4 * q * Amax) with hτ₀
  have hτ₀0 : 0 < τ₀ := by positivity
  set K₀ := max B0 (B4 * a ^ 4)
  set K₁ := max (B1 / a) (B4 * a ^ 2)
  set M : ℝ → ℕ → ℝ → ℝ := fun c k τ => ((max |τ| c) ^ k)⁻¹ with hM
  have P0 : ∀ τ, ‖F τ‖ ≤ K₀ * b ^ 4 * M b 4 τ := by
    intro τ
    simp only [hM]
    rcases le_or_gt |τ| b with h | h
    · rw [max_eq_right h, mul_inv_cancel_right₀ (pow_ne_zero 4 hb0.ne')]
      exact (hF0 τ).trans (le_max_left _ _)
    · rw [max_eq_left h.le]
      have hτ0 : 0 < |τ| := lt_trans hb0 h
      have h4 : ‖F τ‖ ≤ B4 / |τ| ^ 4 := by
        rw [le_div_iff₀ (by positivity), mul_comm, pow_abs, abs_of_nonneg (by positivity)]
        exact hF4 τ
      refine h4.trans ?_
      rw [div_eq_mul_inv]
      gcongr
      calc B4 = B4 * a ^ 4 * b ^ 4 := by rw [hb, inv_pow, mul_inv_cancel_right₀ (by positivity)]
        _ ≤ K₀ * b ^ 4 := by gcongr; exact le_max_right _ _
  have P2 : ∀ τ, τ ^ 2 * ‖F τ‖ ≤ K₁ * b ^ 2 * M b 2 τ := by
    intro τ
    simp only [hM]
    rcases le_or_gt |τ| b with h | h
    · rw [max_eq_right h, mul_inv_cancel_right₀ (pow_ne_zero 2 hb0.ne')]
      have : τ ^ 2 * ‖F τ‖ ≤ b * B1 := by
        rw [show τ ^ 2 = |τ| * |τ| by rw [← sq_abs]; ring, mul_assoc]
        exact mul_le_mul h (hF1 τ) (by positivity) hb0.le
      refine this.trans ?_
      rw [hb, inv_mul_eq_div]; exact le_max_left _ _
    · rw [max_eq_left h.le]
      have hτ0 : 0 < |τ| := lt_trans hb0 h
      have h2 : τ ^ 2 * ‖F τ‖ ≤ B4 / |τ| ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        calc τ ^ 2 * ‖F τ‖ * |τ| ^ 2 = τ ^ 4 * ‖F τ‖ := by rw [sq_abs τ]; ring
          _ ≤ B4 := hF4 τ
      refine h2.trans ?_
      rw [div_eq_mul_inv]
      gcongr
      calc B4 = B4 * a ^ 2 * b ^ 2 := by rw [hb, inv_pow, mul_inv_cancel_right₀ (by positivity)]
        _ ≤ K₁ * b ^ 2 := by gcongr; exact le_max_right _ _
  have P3 : ∀ τ, τ₀ < |τ| → ‖F τ‖ / (1 + 4 * τ ^ 2 * L ^ 4) ≤ B1 / (4 * L ^ 4) * M τ₀ 3 τ := by
    intro τ h
    simp only [hM]
    rw [max_eq_left h.le]
    have hτ0 : 0 < |τ| := lt_trans hτ₀0 h
    have h1 : ‖F τ‖ ≤ B1 / |τ| := by rw [le_div_iff₀ hτ0, mul_comm]; exact hF1 τ
    calc ‖F τ‖ / (1 + 4 * τ ^ 2 * L ^ 4) ≤ (B1 / |τ|) / (4 * |τ| ^ 2 * L ^ 4) := by
          apply div_le_div₀ (by positivity) h1 (by positivity)
          rw [sq_abs]; nlinarith [pow_pos hL0 4]
      _ = B1 / (4 * L ^ 4) * (|τ| ^ 3)⁻¹ := by field_simp
  set g : ℝ → ℝ := fun τ => B * (2000 * (K₀ * b ^ 4 * M b 4 τ + 4 * L ^ 4 * (K₁ * b ^ 2 * M b 2 τ)) +
    128 * (L / q) ^ 4 * (B1 / (4 * L ^ 4) * M τ₀ 3 τ)) with hg
  have hi4 := integrable_max_inv_pow b hb0 4 (by norm_num)
  have hi2 := integrable_max_inv_pow b hb0 2 (by norm_num)
  have hi3 := integrable_max_inv_pow τ₀ hτ₀0 3 (by norm_num)
  have hgi : MeasureTheory.Integrable g :=
    ((((hi4.const_mul _).add ((hi2.const_mul _).const_mul _)).const_mul _).add
      ((hi3.const_mul _).const_mul _)).const_mul _
  have hpt : ∀ τ, ‖F τ * (cexp (-(2 * π * I * (τ : ℂ) * m)) *
        (1 / ((q : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * τ)) ^ (1 / 2 : ℂ)) ^ 4 *
        ∑' c : Fin 4 → ℤ, (if c = 0 then 0 else
          expSumS (m : ZMod q) (fun i => (c i : ZMod q)) * ∏ i, mTerm (A i) L τ q (c i)))‖ ≤ g τ := by
    intro τ
    rw [norm_mul]
    have hW := error_integrand_le A L hL0 q m Amax hAmax hA B hS τ
    have hden : (0 : ℝ) < 1 + 4 * τ ^ 2 * L ^ 4 := by positivity
    have hM3 : 0 ≤ M τ₀ 3 τ := by simp only [hM]; positivity
    refine (mul_le_mul_of_nonneg_left hW (norm_nonneg _)).trans ?_
    simp only [hg]
    have e1 : ‖F τ‖ * (B * (2000 * (1 + 4 * τ ^ 2 * L ^ 4) +
        128 * (L / q) ^ 4 / (1 + 4 * τ ^ 2 * L ^ 4) *
          (if |τ| ≤ 1 / (4 * q * Amax) then 0 else 1))) =
        B * (2000 * (‖F τ‖ + 4 * L ^ 4 * (τ ^ 2 * ‖F τ‖)) +
          128 * (L / q) ^ 4 * ((‖F τ‖ / (1 + 4 * τ ^ 2 * L ^ 4)) *
            (if |τ| ≤ 1 / (4 * q * Amax) then 0 else 1))) := by
      ring
    rw [e1]
    apply mul_le_mul_of_nonneg_left _ hB
    have h1 := P0 τ
    have h2 := P2 τ
    have h3 : ‖F τ‖ / (1 + 4 * τ ^ 2 * L ^ 4) * (if |τ| ≤ 1 / (4 * q * Amax) then 0 else 1) ≤
        B1 / (4 * L ^ 4) * M τ₀ 3 τ := by
      split_ifs with hτ
      · rw [mul_zero]; positivity
      · rw [mul_one]; exact P3 τ (by push Not at hτ; exact hτ)
    exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add h1
      (mul_le_mul_of_nonneg_left h2 (by positivity))) (by norm_num))
      (mul_le_mul_of_nonneg_left h3 (by positivity))
  refine (MeasureTheory.norm_integral_le_of_norm_le hgi
    (Filter.Eventually.of_forall hpt)).trans ?_
  have I4 := integral_max_inv_pow_le b hb0 4 (by norm_num)
  have I2 := integral_max_inv_pow_le b hb0 2 (by norm_num)
  have I3 := integral_max_inv_pow_le τ₀ hτ₀0 3 (by norm_num)
  have hK₀ : 0 ≤ K₀ := le_trans hB0 (le_max_left _ _)
  have hK₁ : 0 ≤ K₁ := le_trans (div_nonneg hB1 ha.le) (le_max_left _ _)
  have hint : ∫ τ, g τ = B * (2000 * (K₀ * b ^ 4 * (∫ τ, M b 4 τ) +
      4 * L ^ 4 * (K₁ * b ^ 2 * (∫ τ, M b 2 τ))) +
      128 * (L / q) ^ 4 * (B1 / (4 * L ^ 4) * (∫ τ, M τ₀ 3 τ))) := by
    have j4 : MeasureTheory.Integrable (fun τ => M b 4 τ) := by simp only [hM]; exact hi4
    have j2 : MeasureTheory.Integrable (fun τ => M b 2 τ) := by simp only [hM]; exact hi2
    have j3 : MeasureTheory.Integrable (fun τ => M τ₀ 3 τ) := by simp only [hM]; exact hi3
    have k1 : MeasureTheory.Integrable
        (fun τ => K₀ * b ^ 4 * M b 4 τ + 4 * L ^ 4 * (K₁ * b ^ 2 * M b 2 τ)) :=
      (j4.const_mul _).add ((j2.const_mul _).const_mul _)
    have k2 : MeasureTheory.Integrable
        (fun τ => 2000 * (K₀ * b ^ 4 * M b 4 τ + 4 * L ^ 4 * (K₁ * b ^ 2 * M b 2 τ))) :=
      k1.const_mul _
    have k3 : MeasureTheory.Integrable (fun τ => 128 * (L / q) ^ 4 * (B1 / (4 * L ^ 4) * M τ₀ 3 τ)) :=
      (j3.const_mul _).const_mul _
    have k4 : MeasureTheory.Integrable (fun τ => K₀ * b ^ 4 * M b 4 τ) := j4.const_mul _
    have k5 : MeasureTheory.Integrable (fun τ => 4 * L ^ 4 * (K₁ * b ^ 2 * M b 2 τ)) :=
      (j2.const_mul _).const_mul _
    simp only [hg]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add k2 k3,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_add k4 k5,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  rw [hint]
  apply mul_le_mul_of_nonneg_left _ hB
  have t1 : K₀ * b ^ 4 * (∫ τ, M b 4 τ) ≤ K₀ * b ^ 4 * (4 * (b ^ 3)⁻¹) :=
    mul_le_mul_of_nonneg_left I4 (by positivity)
  have t2 : K₁ * b ^ 2 * (∫ τ, M b 2 τ) ≤ K₁ * b ^ 2 * (4 * (b ^ 1)⁻¹) :=
    mul_le_mul_of_nonneg_left I2 (by positivity)
  have t3 : B1 / (4 * L ^ 4) * (∫ τ, M τ₀ 3 τ) ≤ B1 / (4 * L ^ 4) * (4 * (τ₀ ^ 2)⁻¹) :=
    mul_le_mul_of_nonneg_left I3 (by positivity)
  have e1 : K₀ * b ^ 4 * (4 * (b ^ 3)⁻¹) = 4 * K₀ / a := by rw [hb]; field_simp
  have e2 : K₁ * b ^ 2 * (4 * (b ^ 1)⁻¹) = 4 * K₁ / a := by rw [hb]; field_simp
  have e3 : 128 * (L / q) ^ 4 * (B1 / (4 * L ^ 4) * (4 * (τ₀ ^ 2)⁻¹)) =
      2048 * B1 * Amax ^ 2 / q ^ 2 := by
    rw [hτ₀]; field_simp; ring
  have hL4 : 0 ≤ L ^ 4 := by positivity
  have hLq : 0 ≤ 128 * (L / q) ^ 4 := by positivity
  calc 2000 * (K₀ * b ^ 4 * (∫ τ, M b 4 τ) + 4 * L ^ 4 * (K₁ * b ^ 2 * (∫ τ, M b 2 τ))) +
        128 * (L / q) ^ 4 * (B1 / (4 * L ^ 4) * (∫ τ, M τ₀ 3 τ))
      ≤ 2000 * (K₀ * b ^ 4 * (4 * (b ^ 3)⁻¹) + 4 * L ^ 4 * (K₁ * b ^ 2 * (4 * (b ^ 1)⁻¹))) +
        128 * (L / q) ^ 4 * (B1 / (4 * L ^ 4) * (4 * (τ₀ ^ 2)⁻¹)) := by gcongr
    _ = 8000 * K₀ / a + 32000 * L ^ 4 * K₁ / a + 2048 * B1 * Amax ^ 2 / q ^ 2 := by
        rw [e1, e2, e3]; ring

end FourSquaresCaps
