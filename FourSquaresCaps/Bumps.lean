/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.DFIFourier
public import FourSquaresCaps.FourierBound
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Concrete choices of `η` and `ω`

* `exists_DFIEta`: a smooth `η` with `η(0) = 1`, vanishing for `|y| > 1/2`, bounded derivatives.
* `exists_DFIOmega`: a constant `C` such that for every `Q ≥ 4` and `D ≥ 2Q` there is `ω` with
  `DFIOmega ω Q C` and `∑_{d=1}^{D} ω(d) = 1`.
-/

@[expose] public section

namespace FourSquaresCaps

open Finset Metric

theorem exists_bound_cs {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    ∃ C, ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := hcs.isCompact.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact (hC x hx).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, abs_zero]; exact le_max_right _ _

/-- Uniform bound for the first five derivatives of a smooth compactly supported function. -/
theorem exists_deriv_bound {f : ℝ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hcs : HasCompactSupport f) : ∃ C, ∀ j ≤ 4, ∀ y, |iteratedDeriv j f y| ≤ C := by
  have hb : ∀ j : ℕ, ∃ C, ∀ y, |iteratedDeriv j f y| ≤ C := fun j =>
    exists_bound_cs (hf.continuous_iteratedDeriv j (by exact_mod_cast le_top))
      (hasCompactSupport_iteratedDeriv hcs j)
  choose C hC using hb
  refine ⟨∑ j ∈ range 5, |C j|, fun j hj y => ?_⟩
  calc |iteratedDeriv j f y| ≤ |C j| := (hC j y).trans (le_abs_self _)
    _ ≤ ∑ j ∈ range 5, |C j| :=
        single_le_sum (f := fun j => |C j|) (fun _ _ => abs_nonneg _) (mem_range.mpr (by omega))

theorem exists_DFIEta : ∃ η : ℝ → ℝ, ∃ E, DFIEta η E := by
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  obtain ⟨E, hE⟩ := exists_deriv_bound (b.contDiff (n := ⊤))
    b.hasCompactSupport
  refine ⟨b, E, b.contDiff, b.one_of_mem_closedBall (mem_closedBall_self (by norm_num)),
    fun y hy => ?_, hE⟩
  apply Function.notMem_support.mp
  rw [b.support_eq, mem_ball, Real.dist_eq, sub_zero, not_lt]
  exact hy.le

theorem exists_DFIOmega : ∃ C, ∀ Q : ℝ, 4 ≤ Q → ∀ D : ℕ, 2 * Q ≤ D →
    ∃ ω : ℝ → ℝ, DFIOmega ω Q C ∧ ∑ k ∈ range D, ω ((k : ℝ) + 1) = 1 := by
  let φ : ContDiffBump (3 / 2 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  obtain ⟨Cφ, hCφ⟩ := exists_deriv_bound (φ.contDiff (n := ⊤))
    φ.hasCompactSupport
  refine ⟨4 * Cφ, fun Q hQ D hD => ?_⟩
  have hQ0 : 0 < Q := by linarith
  set S := ∑ k ∈ range D, φ (((k : ℝ) + 1) / Q) with hS
  -- `S ≥ Q/4`
  have hSlow : Q / 4 ≤ S := by
    set I := Icc ⌈5 * Q / 4⌉₊ ⌊7 * Q / 4⌋₊ with hI
    have hcardI : Q / 2 - 1 ≤ (I.card : ℝ) := by
      rw [hI, Nat.card_Icc]
      have h1 : (⌈5 * Q / 4⌉₊ : ℝ) < 5 * Q / 4 + 1 := Nat.ceil_lt_add_one (by positivity)
      have h2 : 7 * Q / 4 - 1 < (⌊7 * Q / 4⌋₊ : ℝ) := Nat.sub_one_lt_floor _
      have h3 : ⌈5 * Q / 4⌉₊ ≤ ⌊7 * Q / 4⌋₊ + 1 := by
        have : (⌈5 * Q / 4⌉₊ : ℝ) ≤ ⌊7 * Q / 4⌋₊ + 1 := by linarith
        exact_mod_cast this
      rw [Nat.cast_sub h3]; push_cast; linarith
    have hsub : ∀ n ∈ I, n - 1 ∈ range D ∧ φ ((((n - 1 : ℕ) : ℝ) + 1) / Q) = 1 := by
      intro n hn
      rw [hI, mem_Icc] at hn
      have hn1 : 5 * Q / 4 ≤ n := Nat.ceil_le.mp hn.1
      have hn2 : (n : ℝ) ≤ 7 * Q / 4 := Nat.le_floor_iff (by positivity) |>.mp hn.2
      have hn0 : 1 ≤ n := by
        have : (1 : ℝ) ≤ n := by linarith
        exact_mod_cast this
      have hcast : (((n - 1 : ℕ) : ℝ) + 1) = n := by rw [Nat.cast_sub hn0]; push_cast; ring
      refine ⟨mem_range.mpr ?_, ?_⟩
      · have : (n : ℝ) ≤ D := by linarith
        have : n ≤ D := by exact_mod_cast this
        omega
      · rw [hcast]
        apply φ.one_of_mem_closedBall
        rw [mem_closedBall, Real.dist_eq, abs_le]
        constructor
        · rw [le_sub_iff_add_le, le_div_iff₀ hQ0]; show (-(1 / 4) + 3 / 2) * Q ≤ n; linarith
        · rw [sub_le_iff_le_add, div_le_iff₀ hQ0]; show (n : ℝ) ≤ (1 / 4 + 3 / 2) * Q; linarith
    calc Q / 4 ≤ Q / 2 - 1 := by linarith
      _ ≤ (I.card : ℝ) := hcardI
      _ = ∑ n ∈ I, φ ((((n - 1 : ℕ) : ℝ) + 1) / Q) := by
          rw [sum_congr rfl fun n hn => (hsub n hn).2]; simp
      _ ≤ S := by
          rw [hS]
          refine sum_le_sum_of_injOn (fun n => n - 1) ?_ ?_ (fun n _ => le_rfl)
            (fun _ _ _ => φ.nonneg)
          · intro a ha b hb hab
            simp only at hab
            have ha1 : 1 ≤ a := by
              have := (mem_Icc.mp ha).1
              have : (1 : ℝ) ≤ a := by
                have := Nat.ceil_le.mp this; linarith
              exact_mod_cast this
            have hb1 : 1 ≤ b := by
              have := (mem_Icc.mp hb).1
              have : (1 : ℝ) ≤ b := by
                have := Nat.ceil_le.mp this; linarith
              exact_mod_cast this
            omega
          · intro k hk
            rw [mem_image] at hk
            obtain ⟨n, hn, rfl⟩ := hk
            exact (hsub n hn).1
  have hS0 : 0 < S := by linarith
  refine ⟨fun y => S⁻¹ * φ (Q⁻¹ * y), ⟨by linarith, ?_, ?_, ?_⟩, ?_⟩
  · exact contDiff_const.mul (φ.contDiff.comp (contDiff_const.mul contDiff_id))
  · intro y hy
    rw [show φ (Q⁻¹ * y) = 0 from ?_, mul_zero]
    apply Function.notMem_support.mp
    rw [φ.support_eq, mem_ball, Real.dist_eq, not_lt]
    show 1 / 2 ≤ |Q⁻¹ * y - 3 / 2|
    rcases hy with h | h
    · have : Q⁻¹ * y < 1 := by rw [inv_mul_lt_iff₀ hQ0]; linarith
      rw [abs_of_neg (by linarith)]; linarith
    · have : 2 < Q⁻¹ * y := by rw [lt_inv_mul_iff₀ hQ0]; linarith
      rw [abs_of_pos (by linarith)]; linarith
  · intro j hj y
    have e : iteratedDeriv j (fun y => S⁻¹ * φ (Q⁻¹ * y)) y =
        S⁻¹ * (Q⁻¹ ^ j * iteratedDeriv j φ (Q⁻¹ * y)) := by
      rw [iteratedDeriv_const_mul_field,
        iteratedDeriv_comp_const_mul (φ.contDiff (n := (j : ℕ∞)))]
    rw [e, abs_mul, abs_mul, abs_inv, abs_of_pos hS0, abs_pow, abs_inv, abs_of_pos hQ0]
    have hb := hCφ j hj (Q⁻¹ * y)
    have hC0 : 0 ≤ Cφ := (abs_nonneg _).trans hb
    calc S⁻¹ * (Q⁻¹ ^ j * |iteratedDeriv j φ (Q⁻¹ * y)|) ≤ (Q / 4)⁻¹ * (Q⁻¹ ^ j * Cφ) := by
          gcongr
      _ = 4 * Cφ / Q ^ (j + 1) := by rw [inv_pow, pow_succ]; field_simp
  · show ∑ k ∈ range D, S⁻¹ * φ (Q⁻¹ * ((k : ℝ) + 1)) = 1
    rw [← mul_sum]
    have : ∑ i ∈ range D, φ (Q⁻¹ * ((i : ℝ) + 1)) = S := by
      rw [hS]; exact sum_congr rfl fun i _ => by congr 1; rw [div_eq_inv_mul]
    rw [this]
    exact inv_mul_cancel₀ hS0.ne'

end FourSquaresCaps
