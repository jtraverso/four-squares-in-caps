/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Gaussian sums over the integers

* `tsum_gauss_nat_le`: `∑_{k ≥ 0} exp(−π k² / σ²) ≤ 1 + σ/2`.
* `tsum_gauss_int_le`: `∑_{n ∈ ℤ} exp(−π (n − y)² / σ²) ≤ 2 + σ`.
-/

@[expose] public section

namespace FourSquaresCaps

open Real Finset

theorem summable_gauss_nat (σ : ℝ) (hσ : 0 < σ) :
    Summable (fun k : ℕ => exp (-π * (k : ℝ) ^ 2 / σ ^ 2)) := by
  have hr : exp (-π / σ ^ 2) < 1 := by
    rw [Real.exp_lt_one_iff]; have := pi_pos; have : 0 < σ ^ 2 := by positivity
    exact div_neg_of_neg_of_pos (by linarith) this
  refine Summable.of_nonneg_of_le (fun k => (exp_pos _).le) (fun k => ?_)
    (summable_geometric_of_lt_one (exp_pos _).le hr)
  rw [← exp_nat_mul, exp_le_exp]
  have hk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ k := by exact_mod_cast h
      nlinarith
  have : 0 < σ ^ 2 := by positivity
  rw [div_le_iff₀ this, mul_comm, mul_assoc, div_mul_cancel₀ _ this.ne']
  have := pi_pos
  nlinarith

theorem tsum_gauss_nat_le (σ : ℝ) (hσ : 0 < σ) :
    ∑' k : ℕ, exp (-π * (k : ℝ) ^ 2 / σ ^ 2) ≤ 1 + σ / 2 := by
  have hs := summable_gauss_nat σ hσ
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_div, exp_zero, add_le_add_iff_left]
  have hσ2 : 0 < σ ^ 2 := by positivity
  set g : ℝ → ℝ := fun x => exp (-(π / σ ^ 2) * x ^ 2) with hg
  have hgeq : ∀ x : ℝ, exp (-π * x ^ 2 / σ ^ 2) = g x := by
    intro x; simp only [hg]; congr 1; ring
  have hanti : ∀ n : ℕ, AntitoneOn g (Set.Icc 0 (0 + n)) := by
    intro n x hx y hy hxy
    simp only [hg]
    apply exp_le_exp.mpr
    have h1 : x ^ 2 ≤ y ^ 2 := by nlinarith [hx.1]
    have : 0 < π / σ ^ 2 := div_pos pi_pos hσ2
    nlinarith
  have hint : MeasureTheory.IntegrableOn g (Set.Ioi 0) :=
    (integrable_exp_neg_mul_sq (div_pos pi_pos hσ2)).integrableOn
  have hval : ∫ x in Set.Ioi (0 : ℝ), g x = σ / 2 := by
    simp only [hg]
    rw [integral_gaussian_Ioi, div_div_cancel₀ pi_pos.ne', sqrt_sq hσ.le]
  refine (hs.comp_injective (add_left_injective 1)).tsum_le_of_sum_range_le fun n => ?_
  calc ∑ i ∈ range n, exp (-π * ((i + 1 : ℕ) : ℝ) ^ 2 / σ ^ 2)
      = ∑ i ∈ range n, g (0 + ((i + 1 : ℕ) : ℝ)) := by
        refine sum_congr rfl fun i _ => ?_; rw [zero_add, hgeq]
    _ ≤ ∫ x in (0 : ℝ)..0 + n, g x := (hanti n).sum_le_integral
    _ ≤ ∫ x in Set.Ioi (0 : ℝ), g x := by
        rw [zero_add, intervalIntegral.integral_of_le (Nat.cast_nonneg n)]
        exact MeasureTheory.setIntegral_mono_set hint
          (Filter.Eventually.of_forall fun x => (exp_pos _).le)
          (Filter.Eventually.of_forall Set.Ioc_subset_Ioi_self)
    _ = σ / 2 := hval

/-- `∑_{n ∈ ℤ} exp(−π (n − y)² / σ²) ≤ 2 + σ`. -/
theorem tsum_gauss_int_le (σ : ℝ) (hσ : 0 < σ) (y : ℝ) :
    Summable (fun n : ℤ => exp (-π * ((n : ℝ) - y) ^ 2 / σ ^ 2)) ∧
      ∑' n : ℤ, exp (-π * ((n : ℝ) - y) ^ 2 / σ ^ 2) ≤ 2 + σ := by
  set n₀ := ⌊y⌋ with hn₀
  set f : ℤ → ℝ := fun n => exp (-π * ((n : ℝ) - y) ^ 2 / σ ^ 2) with hf
  set g : ℕ → ℝ := fun k => exp (-π * (k : ℝ) ^ 2 / σ ^ 2) with hg
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hmono : ∀ (a b : ℝ), 0 ≤ b → b ≤ a → exp (-π * a ^ 2 / σ ^ 2) ≤ exp (-π * b ^ 2 / σ ^ 2) := by
    intro a b hb hba
    apply exp_le_exp.mpr
    rw [div_le_div_iff_of_pos_right hσ2]
    have : b ^ 2 ≤ a ^ 2 := by nlinarith
    nlinarith [pi_pos]
  have hy1 : y < (n₀ : ℝ) + 1 := Int.lt_floor_add_one y
  have hy0 : (n₀ : ℝ) ≤ y := Int.floor_le y
  let e := Equiv.addRight (n₀ + 1)
  have h1 : ∀ k : ℕ, (f ∘ e) k ≤ g k := by
    intro k
    simp only [Function.comp_apply, e, Equiv.coe_addRight, hf, hg]
    apply hmono _ _ (Nat.cast_nonneg k)
    push_cast; linarith
  have h2 : ∀ k : ℕ, (f ∘ e) (-(k + 1)) ≤ g k := by
    intro k
    simp only [Function.comp_apply, e, Equiv.coe_addRight, hf, hg]
    have : ((((-((k : ℤ) + 1) + (n₀ + 1)) : ℤ) : ℝ) - y) ^ 2 = (y - n₀ + k) ^ 2 := by
      push_cast; ring
    rw [this]
    apply hmono _ _ (Nat.cast_nonneg k)
    linarith
  have hgs := summable_gauss_nat σ hσ
  have hs1 : Summable fun k : ℕ => (f ∘ e) k :=
    Summable.of_nonneg_of_le (fun _ => (exp_pos _).le) h1 hgs
  have hs2 : Summable fun k : ℕ => (f ∘ e) (-(k + 1)) :=
    Summable.of_nonneg_of_le (fun _ => (exp_pos _).le) h2 hgs
  have hsum : Summable (f ∘ e) := Summable.of_nat_of_neg_add_one hs1 hs2
  refine ⟨(e.summable_iff).mp hsum, ?_⟩
  rw [← e.tsum_eq, show (fun n => f (e n)) = f ∘ e from rfl,
    tsum_of_nat_of_neg_add_one hs1 hs2]
  have := tsum_gauss_nat_le σ hσ
  have a1 := hs1.tsum_le_tsum h1 hgs
  have a2 := hs2.tsum_le_tsum h2 hgs
  linarith

/-- Products of absolutely convergent sums over `ℤ`. -/
theorem tsum_pi_prod {R : Type*} [NormedCommRing R] [CompleteSpace R] :
    ∀ {n : ℕ} (f : Fin n → ℤ → R), (∀ i, Summable fun x => ‖f i x‖) →
    Summable (fun x : Fin n → ℤ => ‖∏ i, f i (x i)‖) ∧
      ∑' x : Fin n → ℤ, ∏ i, f i (x i) = ∏ i, ∑' x, f i x
  | 0, _, _ => by
    refine ⟨Summable.of_finite, ?_⟩
    rw [tsum_eq_single (default : Fin 0 → ℤ) (fun b hb => (hb (Subsingleton.elim _ _)).elim)]
    simp
  | n + 1, f, hf => by
    obtain ⟨hs, ht⟩ := tsum_pi_prod (fun i => f i.succ) (fun i => hf i.succ)
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)
    have key : ∀ p : ℤ × (Fin n → ℤ),
        ∏ i, f i (e p i) = f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i) := by
      intro p
      rw [Fin.prod_univ_succ]
      simp [e, Fin.consEquiv]
    constructor
    · rw [← e.summable_iff]
      have := (hf 0).mul_norm hs
      refine this.congr fun p => ?_
      simp only [Function.comp_apply, key]
    · rw [← e.tsum_eq]
      simp_rw [key]
      rw [← tsum_mul_tsum_of_summable_norm (hf 0) hs, ht, Fin.prod_univ_succ]

theorem gauss_prod (σ : ℝ) (y : Fin 4 → ℝ) (c : Fin 4 → ℤ) :
    exp (-π * ∑ i, ((c i : ℝ) - y i) ^ 2 / σ ^ 2) =
      ∏ i, exp (-π * ((c i : ℝ) - y i) ^ 2 / σ ^ 2) := by
  rw [← exp_sum]; congr 1; rw [mul_sum]; exact sum_congr rfl fun i _ => by ring

/-- `∑_{c ∈ ℤ⁴} exp(−π |c − y|² / σ²) ≤ (2 + σ)⁴`. -/
theorem tsum_gauss4_le (σ : ℝ) (hσ : 0 < σ) (y : Fin 4 → ℝ) :
    Summable (fun c : Fin 4 → ℤ => exp (-π * ∑ i, ((c i : ℝ) - y i) ^ 2 / σ ^ 2)) ∧
      ∑' c : Fin 4 → ℤ, exp (-π * ∑ i, ((c i : ℝ) - y i) ^ 2 / σ ^ 2) ≤ (2 + σ) ^ 4 := by
  have hn : ∀ i, Summable fun n : ℤ => ‖exp (-π * ((n : ℝ) - y i) ^ 2 / σ ^ 2)‖ := by
    intro i
    simp_rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact (tsum_gauss_int_le σ hσ (y i)).1
  obtain ⟨hs, ht⟩ := tsum_pi_prod (fun i => fun n : ℤ => exp (-π * ((n : ℝ) - y i) ^ 2 / σ ^ 2)) hn
  simp_rw [gauss_prod]
  refine ⟨hs.of_norm, ?_⟩
  rw [ht]
  calc ∏ i, ∑' n : ℤ, exp (-π * ((n : ℝ) - y i) ^ 2 / σ ^ 2) ≤ ∏ _i : Fin 4, (2 + σ) :=
        prod_le_prod₀ (fun i _ => tsum_nonneg fun _ => (exp_pos _).le)
          fun i _ => (tsum_gauss_int_le σ hσ (y i)).2
    _ = (2 + σ) ^ 4 := by rw [prod_const, card_univ, Fintype.card_fin]

/-- The sum over `c ≠ 0` when `|yᵢ| ≤ 1/2`: `≤ exp(−π/(8σ²)) (2 + √2 σ)⁴`. -/
theorem tsum_gauss4_ne_zero_le (σ : ℝ) (hσ : 0 < σ) (y : Fin 4 → ℝ) (hy : ∀ i, |y i| ≤ 1 / 2) :
    ∑' c : Fin 4 → ℤ, (if c = 0 then 0 else exp (-π * ∑ i, ((c i : ℝ) - y i) ^ 2 / σ ^ 2)) ≤
      exp (-π / (8 * σ ^ 2)) * (2 + Real.sqrt 2 * σ) ^ 4 := by
  classical
  have hσ' : 0 < Real.sqrt 2 * σ := by positivity
  obtain ⟨hs, ht⟩ := tsum_gauss4_le (Real.sqrt 2 * σ) hσ' y
  have hsq : (Real.sqrt 2 * σ) ^ 2 = 2 * σ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hle : ∀ c : Fin 4 → ℤ, (if c = 0 then 0 else exp (-π * ∑ i, ((c i : ℝ) - y i) ^ 2 / σ ^ 2)) ≤
      exp (-π / (8 * σ ^ 2)) * exp (-π * ∑ i, ((c i : ℝ) - y i) ^ 2 / (Real.sqrt 2 * σ) ^ 2) := by
    intro c
    split_ifs with hc
    · positivity
    · obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
        by_contra h; push Not at h; exact hc (funext h)
      have hcj : (1 : ℝ) ≤ |(c j : ℝ)| := by
        have : (1 : ℤ) ≤ |c j| := Int.one_le_abs hj
        exact_mod_cast this
      have h1 : 1 / 2 ≤ |(c j : ℝ) - y j| := by
        have := abs_sub_abs_le_abs_sub (c j : ℝ) (y j)
        have := hy j
        linarith
      have hS : 1 / 4 ≤ ∑ i, ((c i : ℝ) - y i) ^ 2 := by
        have : ((c j : ℝ) - y j) ^ 2 ≤ ∑ i, ((c i : ℝ) - y i) ^ 2 :=
          single_le_sum (f := fun i => ((c i : ℝ) - y i) ^ 2) (fun i _ => sq_nonneg _) (mem_univ j)
        have : (1 / 2) ^ 2 ≤ ((c j : ℝ) - y j) ^ 2 := by
          rw [← sq_abs ((c j : ℝ) - y j)]; exact pow_le_pow_left₀ (by norm_num) h1 2
        linarith
      rw [← exp_add, exp_le_exp, hsq, ← sum_div, ← sum_div]
      set S := ∑ i, ((c i : ℝ) - y i) ^ 2
      have e : -π * (S / σ ^ 2) = -π / (8 * σ ^ 2) + -π * (S / (2 * σ ^ 2)) -
          π * (4 * S - 1) / (8 * σ ^ 2) := by
        field_simp; ring
      rw [e]
      have : 0 ≤ π * (4 * S - 1) / (8 * σ ^ 2) :=
        div_nonneg (mul_nonneg pi_pos.le (by linarith)) (by positivity)
      linarith
  have hs' : Summable fun c : Fin 4 → ℤ =>
      exp (-π / (8 * σ ^ 2)) * exp (-π * ∑ i, ((c i : ℝ) - y i) ^ 2 / (Real.sqrt 2 * σ) ^ 2) :=
    hs.mul_left _
  calc _ ≤ ∑' c : Fin 4 → ℤ, exp (-π / (8 * σ ^ 2)) *
        exp (-π * ∑ i, ((c i : ℝ) - y i) ^ 2 / (Real.sqrt 2 * σ) ^ 2) :=
        (Summable.of_nonneg_of_le (fun c => by split_ifs <;> positivity) hle hs').tsum_le_tsum
          hle hs'
    _ ≤ _ := by
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left ht (exp_pos _).le

end FourSquaresCaps
