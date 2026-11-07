/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.GaussSum
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Gaussian theta sums near a rational point

`θ(α) = ∑_{x ∈ ℤ} exp(−π (x − A)² / L² + 2πi α x²)`. For `α = a/q + t`, splitting `x = b + q y`
and applying Jacobi's theta transformation (`Complex.tsum_exp_neg_quadratic`, Poisson summation for
complex Gaussians) to the sum over `y`:
`θ(a/q + t) = a_q^{-1/2} ∑_{n ∈ ℤ} G_q(a, n) exp(−π (n + i q A / L²)² / a_q − π A² / L²)`,
`a_q = q² (1/L² − 2 i t)` (`thetaW_rat`).
-/

@[expose] public section

namespace FourSquaresCaps

open Complex Finset Real

/-- Summability of complex Gaussians over `ℤ`. -/
theorem summable_cexp_quad (β γ δ : ℂ) (hβ : 0 < β.re) :
    Summable (fun n : ℤ => cexp (-π * β * (n : ℂ) ^ 2 + γ * n + δ)) := by
  have h := (summable_jacobiTheta₂_term_iff (γ / (2 * π * I)) (I * β)).mpr (by simpa using hβ)
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine (h.mul_left (cexp δ)).congr fun n => ?_
  simp only [jacobiTheta₂_term, ← Complex.exp_add]
  congr 1
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- The Gaussian summand. -/
noncomputable def gTerm (A L α : ℝ) (x : ℂ) : ℂ :=
  cexp (-π * (x - A) ^ 2 / (L : ℂ) ^ 2 + 2 * π * I * α * x ^ 2)

/-- The Gaussian theta sum `θ(α)`. -/
noncomputable def thetaW (A L α : ℝ) : ℂ := ∑' x : ℤ, gTerm A L α x

theorem gTerm_eq (A L α : ℝ) (hL : L ≠ 0) (x : ℂ) :
    gTerm A L α x = cexp (-π * ((1 : ℂ) / L ^ 2 - 2 * I * α) * x ^ 2 +
      (2 * π * A / L ^ 2) * x + (-π * A ^ 2 / L ^ 2)) := by
  unfold gTerm
  congr 1
  have : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  field_simp
  ring

theorem summable_gTerm (A L α : ℝ) (hL : L ≠ 0) :
    Summable (fun x : ℤ => gTerm A L α x) := by
  simp_rw [gTerm_eq A L α hL]
  refine summable_cexp_quad _ _ _ ?_
  have h : ((1 : ℂ) / (L : ℂ) ^ 2 - 2 * I * α) = ((1 / L ^ 2 : ℝ) : ℂ) + ((-2 * α : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [h, add_re, ofReal_re, re_ofReal_mul, I_re, mul_zero, add_zero]
  have : (0 : ℝ) < L ^ 2 := by positivity
  positivity

/-- Splitting the theta sum by residues mod `q`. -/
theorem thetaW_split (A L α : ℝ) (hL : L ≠ 0) (q : ℕ) [NeZero q] :
    thetaW A L α = ∑ b : Fin q, ∑' y : ℤ, gTerm A L α (((y * q + b : ℤ)) : ℂ) := by
  unfold thetaW
  let e : ℤ ≃ Fin q × ℤ := (Int.divModEquiv q).trans (Equiv.prodComm _ _)
  rw [← e.symm.tsum_eq]
  have hs : Summable (fun p : Fin q × ℤ => gTerm A L α ((e.symm p : ℤ) : ℂ)) :=
    (summable_gTerm A L α hL).comp_injective e.symm.injective
  rw [hs.tsum_prod' (fun b => (summable_gTerm A L α hL).comp_injective
    (e.symm.injective.comp (Prod.mk_right_injective b))), tsum_fintype]
  rfl

/-- The `b`-th residue class sum, before the theta transformation. -/
theorem gTerm_rat (A L t : ℝ) (hL : L ≠ 0) (q : ℕ) [NeZero q] (a y b : ℤ) :
    gTerm A L ((a : ℝ) / q + t) (((y * q + b : ℤ)) : ℂ) =
      cexp (2 * π * I * a * b ^ 2 / q) *
        cexp (-π * ((q : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * t)) * (y : ℂ) ^ 2 +
          2 * π * (-(q : ℂ) * (b - A) / L ^ 2 + 2 * I * q * t * b) * y +
          (-π * (b - A) ^ 2 / L ^ 2 + 2 * π * I * t * b ^ 2)) := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  unfold gTerm
  rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨a * (y ^ 2 * q + 2 * y * b), ?_⟩
  push_cast
  field_simp
  ring

/-- The Gaussian factor after the theta transformation. -/
noncomputable def mTerm (A L t : ℝ) (q : ℕ) (n : ℂ) : ℂ :=
  cexp (-π * (n + I * q * A / L ^ 2) ^ 2 / ((q : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * t)) -
    π * A ^ 2 / L ^ 2)

theorem re_aq_pos (L t : ℝ) (hL : L ≠ 0) (q : ℕ) [NeZero q] :
    0 < ((q : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * t)).re := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have h : ((q : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * t)) =
      (((q : ℝ) ^ 2 / L ^ 2 : ℝ) : ℂ) + ((-2 * (q : ℝ) ^ 2 * t : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [h, add_re, ofReal_re, re_ofReal_mul, I_re, mul_zero, add_zero]
  have : (0 : ℝ) < L ^ 2 := by positivity
  positivity

/-- The completed square: the `b`-dependence becomes the phase `e(n b / q)`. -/
theorem exp_complete (A L t : ℝ) (hL : L ≠ 0) (q : ℕ) [NeZero q] (b n : ℂ) (ht : (1 : ℂ) / L ^ 2 - 2 * I * t ≠ 0) :
    cexp (-π * (b - A) ^ 2 / L ^ 2 + 2 * π * I * t * b ^ 2) *
      cexp (-π / ((q : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * t)) *
        (n + I * (-(q : ℂ) * (b - A) / L ^ 2 + 2 * I * q * t * b)) ^ 2) =
      cexp (2 * π * I * n * b / q) * mTerm A L t q n := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  unfold mTerm
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  set D := (1 : ℂ) / L ^ 2 - 2 * I * t with hDdef
  set N := n + I * q * A / L ^ 2 with hN
  have h1 : I * (-(q : ℂ) * (b - A) / L ^ 2 + 2 * I * q * t * b) = I * q * A / L ^ 2 - I * b * q * D := by
    rw [hDdef]; ring
  have h2 : -π / ((q : ℂ) ^ 2 * D) * (n + (I * q * A / L ^ 2 - I * b * q * D)) ^ 2 =
      -π * N ^ 2 / ((q : ℂ) ^ 2 * D) + 2 * π * I * b * n / q + 2 * π * I ^ 2 * b * A / L ^ 2 -
        π * I ^ 2 * b ^ 2 * D := by
    rw [hN]; field_simp; ring
  rw [h1, h2, I_sq, hDdef]
  ring

/-- The Gauss sum as a sum over `Fin q`. -/
theorem sum_fin_eq_gaussQ (q : ℕ) [NeZero q] (a n : ℤ) :
    ∑ b : Fin q, cexp (2 * π * I * a * ((b : ℕ) : ℂ) ^ 2 / q) * cexp (2 * π * I * n * ((b : ℕ) : ℂ) / q) =
      gaussQ (a : ZMod q) (n : ZMod q) := by
  unfold gaussQ
  have hinj : Function.Injective (fun b : Fin q => ((b : ℕ) : ZMod q)) := by
    intro b c h
    have := congrArg ZMod.val h
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt b.2, Nat.mod_eq_of_lt c.2] at this
    exact Fin.ext this
  have hbij : Function.Bijective (fun b : Fin q => ((b : ℕ) : ZMod q)) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp⟩
  refine Fintype.sum_bijective _ hbij _ _ fun b => ?_
  have : ((a : ZMod q) * ((b : ℕ) : ZMod q) ^ 2 + (n : ZMod q) * ((b : ℕ) : ZMod q)) =
      (((a * (b : ℕ) ^ 2 + n * (b : ℕ) : ℤ)) : ZMod q) := by push_cast; ring
  rw [this, ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Theta transformation at a rational point.** -/
theorem thetaW_rat (A L t : ℝ) (hL : L ≠ 0) (q : ℕ) [NeZero q] (a : ℤ) :
    thetaW A L ((a : ℝ) / q + t) =
      1 / ((q : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * t)) ^ (1 / 2 : ℂ) *
        ∑' n : ℤ, gaussQ (a : ZMod q) (n : ZMod q) * mTerm A L t q n := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have haq_re := re_aq_pos L t hL q
  set aq := (q : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * t) with haq
  have haq0 : aq ≠ 0 := fun h => by rw [h, zero_re] at haq_re; exact lt_irrefl 0 haq_re
  have hD : (1 : ℂ) / L ^ 2 - 2 * I * t ≠ 0 := fun h => haq0 (by rw [haq, h, mul_zero])
  -- summability of the transformed terms
  have hsum : ∀ b : ℂ, Summable (fun n : ℤ => cexp (2 * π * I * n * b / q) * mTerm A L t q n) := by
    intro b
    have hre : 0 < (1 / aq).re := by
      rw [one_div, inv_re]; exact div_pos haq_re (normSq_pos.mpr haq0)
    refine (summable_cexp_quad (1 / aq) (2 * π * I * b / q - 2 * π * (I * q * A / L ^ 2) / aq)
      (-π * (I * q * A / L ^ 2) ^ 2 / aq - π * A ^ 2 / L ^ 2) hre).congr fun n => ?_
    unfold mTerm
    rw [← Complex.exp_add]
    congr 1
    rw [← haq]
    ring
  rw [thetaW_split A L _ hL q]
  have hb : ∀ b : Fin q, ∑' y : ℤ, gTerm A L ((a : ℝ) / q + t) (((y * q + (b : ℕ) : ℤ)) : ℂ) =
      1 / aq ^ (1 / 2 : ℂ) * ∑' n : ℤ, cexp (2 * π * I * a * ((b : ℕ) : ℂ) ^ 2 / q) *
        (cexp (2 * π * I * n * ((b : ℕ) : ℂ) / q) * mTerm A L t q n) := by
    intro b
    set bc : ℂ := (((b : ℕ) : ℤ) : ℂ) with hbc
    set B : ℂ := -(q : ℂ) * (bc - A) / L ^ 2 + 2 * I * q * t * bc with hB
    set C : ℂ := -π * (bc - A) ^ 2 / L ^ 2 + 2 * π * I * t * bc ^ 2 with hC
    set E : ℂ := cexp (2 * π * I * a * bc ^ 2 / q) with hE
    have hbc' : bc = ((b : ℕ) : ℂ) := by rw [hbc]; push_cast; rfl
    calc ∑' y : ℤ, gTerm A L ((a : ℝ) / q + t) (((y * q + (b : ℕ) : ℤ)) : ℂ)
        = ∑' y : ℤ, E * (cexp (-π * aq * (y : ℂ) ^ 2 + 2 * π * B * y) * cexp C) := by
          refine tsum_congr fun y => ?_
          rw [gTerm_rat A L t hL q a y ((b : ℕ) : ℤ)]
          simp only [hE, hB, hC, haq, hbc, ← Complex.exp_add]
      _ = E * ((1 / aq ^ (1 / 2 : ℂ) * ∑' n : ℤ, cexp (-π / aq * (n + I * B) ^ 2)) * cexp C) := by
          rw [tsum_mul_left, tsum_mul_right, Complex.tsum_exp_neg_quadratic haq_re]
      _ = 1 / aq ^ (1 / 2 : ℂ) * ∑' n : ℤ, E * (cexp C * cexp (-π / aq * (n + I * B) ^ 2)) := by
          rw [← tsum_mul_left, ← tsum_mul_right, ← tsum_mul_left, ← tsum_mul_left]
          refine tsum_congr fun n => ?_
          ring
      _ = _ := by
          congr 1
          refine tsum_congr fun n => ?_
          rw [hC, hB, haq, exp_complete A L t hL q bc n hD, hE, hbc']
  rw [sum_congr rfl fun b _ => hb b, ← mul_sum]
  congr 1
  rw [← Summable.tsum_finsetSum fun b _ => (hsum _).mul_left _]
  refine tsum_congr fun n => ?_
  rw [← sum_fin_eq_gaussQ q a n, sum_mul]
  refine sum_congr rfl fun b _ => ?_
  ring

end FourSquaresCaps
