/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A divisor bound

`sigmaHalf_le`: `∑_{g ∣ n} g^{-1/2} ≤ 4^{17} n^{1/8}` for `n ≥ 1`.
-/

@[expose] public section

namespace FourSquaresCaps

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

/-- `g ↦ g^{-1/2}` as an arithmetic function. -/
noncomputable def invSqrtAF : ArithmeticFunction ℝ := ⟨fun n => (Real.sqrt n)⁻¹, by simp⟩

theorem invSqrtAF_apply (n : ℕ) : invSqrtAF n = (Real.sqrt n)⁻¹ := rfl

theorem isMultiplicative_invSqrtAF : invSqrtAF.IsMultiplicative := by
  refine ⟨by simp [invSqrtAF_apply], fun {m n} _ => ?_⟩
  simp only [invSqrtAF_apply, Nat.cast_mul]
  rw [Real.sqrt_mul (Nat.cast_nonneg _), mul_inv]

/-- `∑_{g ∣ n} g^{-1/2}`. -/
noncomputable def sigmaHalf (n : ℕ) : ℝ := ∑ g ∈ n.divisors, (Real.sqrt g)⁻¹

theorem sigmaHalf_eq (n : ℕ) : sigmaHalf n = ((ζ : ArithmeticFunction ℝ) * invSqrtAF) n := by
  rw [coe_zeta_mul_apply]; rfl

/-- `n ↦ n^{1/8}` as an arithmetic function. -/
noncomputable def rpowAF : ArithmeticFunction ℝ := ⟨fun n => (n : ℝ) ^ (1 / 8 : ℝ), by simp⟩

theorem isMultiplicative_rpowAF : rpowAF.IsMultiplicative := by
  refine ⟨by simp [rpowAF], fun {m n} _ => ?_⟩
  simp only [rpowAF, ArithmeticFunction.coe_mk, Nat.cast_mul]
  exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem sigmaHalf_prime_pow_le (p k : ℕ) (hp : p.Prime) :
    sigmaHalf (p ^ k) ≤ (1 - (Real.sqrt p)⁻¹)⁻¹ := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hs : 1 < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  set r := (Real.sqrt p)⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hs
  unfold sigmaHalf
  rw [Nat.divisors_prime_pow hp, sum_map]
  simp only [Function.Embedding.coeFn_mk, Nat.cast_pow]
  have hsq : ∀ j : ℕ, (Real.sqrt ((p : ℝ) ^ j))⁻¹ = r ^ j := by
    intro j
    rw [hr, inv_pow]
    congr 1
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity), ← pow_mul, mul_comm, pow_mul,
      Real.sq_sqrt (by positivity)]
  simp_rw [hsq]
  rw [geom_sum_eq hr1.ne]
  have h1r : 0 < 1 - r := by linarith
  rw [div_le_iff_of_neg (by linarith), inv_mul_eq_div, div_eq_mul_inv]
  have : r ^ (k + 1) - 1 ≤ 0 := by
    have := pow_le_one₀ hr0 hr1.le (n := k + 1); linarith
  rw [show (r - 1) * (1 - r)⁻¹ = -1 by field_simp; ring]
  have : 0 ≤ r ^ (k + 1) := pow_nonneg hr0 _
  linarith

/-- For `p ≥ 17`: `(1 − p^{-1/2})⁻¹ ≤ p^{1/8}`. -/
theorem inv_one_sub_le_rpow (p : ℝ) (hp : 17 ≤ p) :
    (1 - (Real.sqrt p)⁻¹)⁻¹ ≤ p ^ (1 / 8 : ℝ) := by
  have hp0 : 0 < p := by linarith
  set y := p ^ (1 / 8 : ℝ) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hp0 _
  have hy8 : y ^ 8 = p := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num
  have hs : Real.sqrt p = y ^ 4 := by
    rw [Real.sqrt_eq_iff_eq_sq hp0.le (by positivity), ← pow_mul, hy8]
  have hy1 : 1.42 ≤ y := by
    by_contra h
    push Not at h
    have : y ^ 8 < (1.42 : ℝ) ^ 8 := pow_lt_pow_left₀ h hy0.le (by norm_num)
    nlinarith
  have hy4 : 1 < y ^ 4 := by
    have h1 : (1 : ℝ) < 1.42 ^ 4 := by norm_num
    have h2 := pow_le_pow_left₀ (by norm_num) hy1 4
    linarith
  have key : 0 ≤ y ^ 4 - y ^ 3 - 1 := by
    have h3 := pow_le_pow_left₀ (by norm_num) hy1 3
    have hm : (1.42 : ℝ) ^ 3 * 0.42 ≤ y ^ 3 * (y - 1) :=
      mul_le_mul h3 (by linarith) (by norm_num) (by positivity)
    have : (1 : ℝ) ≤ 1.42 ^ 3 * 0.42 := by norm_num
    nlinarith
  have hpos : 0 < 1 - (y ^ 4)⁻¹ := by rw [sub_pos]; exact inv_lt_one_of_one_lt₀ hy4
  rw [hs, inv_le_comm₀ hpos hy0]
  have e : 1 - (y ^ 4)⁻¹ - y⁻¹ = (y ^ 4 - y ^ 3 - 1) / y ^ 4 := by field_simp; ring
  have : 0 ≤ (y ^ 4 - y ^ 3 - 1) / y ^ 4 := div_nonneg key (by positivity)
  linarith

theorem sigmaHalf_prime_pow_le' (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    sigmaHalf (p ^ k) ≤ (if p < 17 then 4 else 1) * ((p ^ k : ℕ) : ℝ) ^ (1 / 8 : ℝ) := by
  have h1 := sigmaHalf_prime_pow_le p k hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hB : 1 ≤ ((p ^ k : ℕ) : ℝ) ^ (1 / 8 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast Nat.one_le_pow _ _ hp.pos) (by norm_num)
  split_ifs with h17
  · refine h1.trans ?_
    have hs : (4 : ℝ) / 3 ≤ Real.sqrt p := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]; nlinarith
    have : (1 - (Real.sqrt p)⁻¹)⁻¹ ≤ 4 := by
      have hs0 : 0 < Real.sqrt p := by linarith
      have : (Real.sqrt p)⁻¹ ≤ 3 / 4 := by
        rw [inv_le_comm₀ hs0 (by norm_num)]; norm_num; linarith
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    nlinarith
  · push Not at h17
    refine h1.trans ((inv_one_sub_le_rpow p (by exact_mod_cast h17)).trans ?_)
    rw [one_mul]
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    push_cast
    exact le_self_pow₀ (by linarith) (by omega)

/-- **Divisor bound.** `∑_{g ∣ n} g^{-1/2} ≤ 4^{17} n^{1/8}`. -/
theorem sigmaHalf_le (n : ℕ) (hn : n ≠ 0) : sigmaHalf n ≤ 4 ^ 17 * (n : ℝ) ^ (1 / 8 : ℝ) := by
  have hm : ((ζ : ArithmeticFunction ℝ) * invSqrtAF).IsMultiplicative :=
    isMultiplicative_zeta.natCast.mul isMultiplicative_invSqrtAF
  have h1 : sigmaHalf n = ∏ p ∈ n.primeFactors, sigmaHalf (p ^ n.factorization p) := by
    rw [sigmaHalf_eq, hm.multiplicative_factorization _ hn, Finsupp.prod,
      Nat.support_factorization]
    exact prod_congr rfl fun p _ => (sigmaHalf_eq _).symm
  have h2 : (n : ℝ) ^ (1 / 8 : ℝ) = ∏ p ∈ n.primeFactors,
      ((p ^ n.factorization p : ℕ) : ℝ) ^ (1 / 8 : ℝ) := by
    have := isMultiplicative_rpowAF.multiplicative_factorization rpowAF hn
    simpa [rpowAF, Finsupp.prod, Nat.support_factorization] using this
  rw [h1, h2]
  have hle : ∏ p ∈ n.primeFactors, sigmaHalf (p ^ n.factorization p) ≤
      ∏ p ∈ n.primeFactors, ((if p < 17 then (4 : ℝ) else 1) *
        ((p ^ n.factorization p : ℕ) : ℝ) ^ (1 / 8 : ℝ)) := by
    refine prod_le_prod₀ (fun p _ => ?_) fun p hp => ?_
    · unfold sigmaHalf; exact sum_nonneg fun _ _ => by positivity
    · have hpp := Nat.prime_of_mem_primeFactors hp
      exact sigmaHalf_prime_pow_le' p _ hpp
        (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp (by
          rwa [Nat.support_factorization])))
  refine hle.trans ?_
  rw [prod_mul_distrib]
  refine mul_le_mul_of_nonneg_right ?_ (prod_nonneg fun _ _ => by positivity)
  rw [prod_ite, prod_const_one, mul_one, prod_const]
  calc (4 : ℝ) ^ (n.primeFactors.filter (· < 17)).card ≤ 4 ^ 17 := by
        gcongr
        · norm_num
        · calc (n.primeFactors.filter (· < 17)).card ≤ (range 17).card :=
                card_le_card fun x hx => by
                  simp only [mem_filter] at hx; exact mem_range.mpr hx.2
            _ = 17 := card_range 17

end FourSquaresCaps
