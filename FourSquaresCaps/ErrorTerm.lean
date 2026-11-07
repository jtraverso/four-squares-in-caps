/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.MainFormula

/-!
# Sizes of the factors in the exact formula

* `norm_mTerm`: `‖M(n)‖ = exp(−π L² (n/q − 2tA)² / (1 + 4t²L⁴))`.
* `norm_aq_inv_pow`: `‖a_q^{-1/2}‖⁴ = (L/q)⁴ / (1 + 4t²L⁴)`.
-/

@[expose] public section

namespace FourSquaresCaps

open Complex Real

theorem inv_aq_eq (L t : ℝ) (hL : L ≠ 0) (q : ℕ) [NeZero q] :
    ((q : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * t))⁻¹ =
      ((L ^ 2 / ((q : ℝ) ^ 2 * (1 + 4 * t ^ 2 * L ^ 4)) : ℝ) : ℂ) * (1 + 2 * I * t * L ^ 2) := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hden : (1 : ℂ) + 4 * t ^ 2 * L ^ 4 ≠ 0 := by
    have : (0 : ℝ) < 1 + 4 * t ^ 2 * L ^ 4 := by positivity
    exact_mod_cast this.ne'
  have hD : (1 : ℂ) / L ^ 2 - 2 * I * t ≠ 0 := by
    intro h
    have h2 := congrArg Complex.re h
    simp [sq] at h2
    exact hL (by simpa using h2)
  rw [inv_eq_iff_eq_inv, eq_comm, ← mul_inv_eq_one₀ (mul_ne_zero (pow_ne_zero 2 hq) hD)]
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring_nf
  have hden' : (1 : ℂ) + (L : ℂ) ^ 4 * (t : ℂ) ^ 2 * 4 ≠ 0 := by
    rw [show (1 : ℂ) + (L : ℂ) ^ 4 * (t : ℂ) ^ 2 * 4 = 1 + 4 * t ^ 2 * L ^ 4 by ring]; exact hden
  field_simp
  ring

/-- `‖M(n)‖ = exp(−π L² (n/q − 2tA)² / (1 + 4t²L⁴))`. -/
theorem norm_mTerm (A L t : ℝ) (hL : L ≠ 0) (q : ℕ) [NeZero q] (n : ℝ) :
    ‖mTerm A L t q n‖ = Real.exp (-π * L ^ 2 * (n / q - 2 * t * A) ^ 2 / (1 + 4 * t ^ 2 * L ^ 4)) := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hden : (0 : ℝ) < 1 + 4 * t ^ 2 * L ^ 4 := by positivity
  unfold mTerm
  rw [Complex.norm_exp]
  congr 1
  rw [div_eq_mul_inv _ ((q : ℂ) ^ 2 * (1 / (L : ℂ) ^ 2 - 2 * I * t)), inv_aq_eq L t hL q]
  simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.I_re,
    Complex.I_im, sq, Complex.div_re, Complex.div_im, Complex.one_re, Complex.one_im,
    Complex.natCast_re, Complex.natCast_im, Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_apply]
  field_simp
  ring

/-- `‖a_q^{-1/2}‖⁴ = L⁴ / (q⁴ (1 + 4t²L⁴))`. -/
theorem norm_aq_inv_pow (L t : ℝ) (hL : L ≠ 0) (q : ℕ) [NeZero q] :
    ‖(1 / ((q : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * t)) ^ (1 / 2 : ℂ)) ^ 4‖ =
      L ^ 4 / ((q : ℝ) ^ 4 * (1 + 4 * t ^ 2 * L ^ 4)) := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  set aq : ℂ := (q : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * t) with haq
  have hn : ‖aq‖ ^ 2 = (q : ℝ) ^ 4 * (1 + 4 * t ^ 2 * L ^ 4) / L ^ 4 := by
    rw [Complex.sq_norm, Complex.normSq_apply, haq]
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, sq,
      Complex.div_re, Complex.div_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.natCast_re, Complex.natCast_im,
      Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_apply]
    field_simp
    ring
  rw [norm_pow, norm_div, norm_one, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_cpow_real, div_pow, one_pow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  norm_num
  rw [hn]
  field_simp

end FourSquaresCaps
