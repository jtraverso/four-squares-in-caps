/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Elementary sums for the error term

* `sum_inv_sqrt_le`: `∑_{e=1}^{N} e^{-1/2} ≤ 2√N`.
* `sum_harmonic_le`: `∑_{d=1}^{N} 1/d ≤ 1 + log N`.
* `sum_card_divisors_div_sqrt_le`: `∑_{n=1}^{N} τ(n)/√n ≤ 2√N (1 + log N)`.
-/

@[expose] public section

namespace FourSquaresCaps

open Finset Real

theorem sum_inv_sqrt_le (N : ℕ) :
    ∑ e ∈ Icc 1 N, (Real.sqrt e)⁻¹ ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), Nat.cast_succ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
    have h2 : Real.sqrt n ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    have hs : Real.sqrt ((n : ℝ) + 1) ^ 2 = n + 1 := Real.sq_sqrt (by linarith)
    have hs' : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn
    -- `1/√(n+1) ≤ 2(√(n+1) − √n)`
    have key : (Real.sqrt ((n : ℝ) + 1))⁻¹ ≤ 2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) := by
      rw [inv_le_iff_one_le_mul₀ h1]
      nlinarith [Real.sqrt_nonneg n]
    linarith

theorem sum_harmonic_le (N : ℕ) : ∑ d ∈ Icc 1 N, (d : ℝ)⁻¹ ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  have : (harmonic N : ℝ) = ∑ d ∈ Icc 1 N, (d : ℝ)⁻¹ := by
    rw [harmonic_eq_sum_Icc]; push_cast; rfl
  linarith

/-- `∑_{n ≤ N} τ(n)/√n ≤ 2√N (1 + log N)`. -/
theorem sum_card_divisors_div_sqrt_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) / Real.sqrt n ≤ 2 * Real.sqrt N * (1 + Real.log N) := by
  -- rewrite as a sum over pairs `(d, e)` with `d e ≤ N`
  have h1 : ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) / Real.sqrt n =
      ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, (Real.sqrt d)⁻¹ * (Real.sqrt (n / d : ℕ))⁻¹ := by
    refine sum_congr rfl fun n hn => ?_
    rw [card_eq_sum_ones, Nat.cast_sum, sum_div]
    refine sum_congr rfl fun d hd => ?_
    have hdn := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
    rw [← mul_inv, ← Real.sqrt_mul (Nat.cast_nonneg _), ← Nat.cast_mul, mul_comm, hdn]
    simp
  rw [h1]
  have h2 : ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, (Real.sqrt d)⁻¹ * (Real.sqrt (n / d : ℕ))⁻¹ ≤
      ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 (N / d), (Real.sqrt d)⁻¹ * (Real.sqrt e)⁻¹ := by
    classical
    rw [sum_sigma', sum_sigma']
    refine sum_le_sum_of_injOn (fun x => (⟨x.2, x.1 / x.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_
      (fun x _ => le_rfl) (fun _ _ _ => by positivity)
    · intro x hx y hy hxy
      simp only [Sigma.mk.injEq] at hxy
      obtain ⟨h1, h2⟩ := hxy
      simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_Icc, Nat.mem_divisors] at hx hy
      have e1 := Nat.div_mul_cancel hx.2.1
      have e2 := Nat.div_mul_cancel hy.2.1
      have : x.1 = y.1 := by
        rw [← e1, ← e2]
        have h2' : x.1 / x.2 = y.1 / y.2 := by simpa using h2
        rw [h2', show x.2 = y.2 from h1]
      exact Sigma.ext this (heq_of_eq h1)
    · intro z hz
      simp only [mem_image, mem_sigma, mem_Icc, Nat.mem_divisors] at hz ⊢
      obtain ⟨x, ⟨⟨h1n, hnN⟩, hd, -⟩, rfl⟩ := hz
      have hd0 : 0 < x.2 := Nat.pos_of_dvd_of_pos hd (by omega)
      have hle : x.2 ≤ x.1 := Nat.le_of_dvd (by omega) hd
      refine ⟨⟨hd0, le_trans hle hnN⟩, ?_, ?_⟩
      · exact Nat.div_pos hle hd0
      · exact Nat.div_le_div_right hnN
  refine h2.trans ?_
  calc ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 (N / d), (Real.sqrt d)⁻¹ * (Real.sqrt e)⁻¹
      ≤ ∑ d ∈ Icc 1 N, (Real.sqrt d)⁻¹ * (2 * Real.sqrt (N / d : ℕ)) := by
        refine sum_le_sum fun d _ => ?_
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_inv_sqrt_le _) (by positivity)
    _ ≤ ∑ d ∈ Icc 1 N, 2 * Real.sqrt N * (d : ℝ)⁻¹ := by
        refine sum_le_sum fun d hd => ?_
        have hd0 : (0 : ℝ) < d := by simp only [mem_Icc] at hd; exact_mod_cast hd.1
        have hq : ((N / d : ℕ) : ℝ) ≤ N / d := Nat.cast_div_le
        have : Real.sqrt (N / d : ℕ) ≤ Real.sqrt N / Real.sqrt d := by
          rw [← Real.sqrt_div' _ hd0.le]; exact Real.sqrt_le_sqrt hq
        have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
        calc (Real.sqrt d)⁻¹ * (2 * Real.sqrt (N / d : ℕ))
            ≤ (Real.sqrt d)⁻¹ * (2 * (Real.sqrt N / Real.sqrt d)) := by gcongr
          _ = 2 * Real.sqrt N * (d : ℝ)⁻¹ := by
              field_simp
              rw [Real.sq_sqrt hd0.le]
              ring
    _ = 2 * Real.sqrt N * ∑ d ∈ Icc 1 N, (d : ℝ)⁻¹ := by rw [mul_sum]
    _ ≤ 2 * Real.sqrt N * (1 + Real.log N) :=
        mul_le_mul_of_nonneg_left (sum_harmonic_le N) (by positivity)

end FourSquaresCaps
