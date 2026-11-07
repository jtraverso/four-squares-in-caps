/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.NumberTheory.SumFourSquares

/-!
# Quadratic Gauss sums

`gaussQ a c = Σ_{b mod q} e((a b² + c b)/q)` with the standard additive character of `ZMod q`.
`norm_sq_gaussQ_le`: `‖gaussQ a c‖² ≤ 2 q` for a unit `a` (square the sum, substitute `x = y + h`
and use the orthogonality of the character).
-/

@[expose] public section

namespace FourSquaresCaps

open ZMod Finset

variable {q : ℕ} [NeZero q]

/-- The quadratic Gauss sum `Σ_{b mod q} e((a b² + c b)/q)`. -/
noncomputable def gaussQ (a c : ZMod q) : ℂ := ∑ b : ZMod q, stdAddChar (a * b ^ 2 + c * b)

/-- Orthogonality of the standard additive character. -/
theorem sum_stdAddChar_mul (t : ZMod q) :
    ∑ y : ZMod q, (stdAddChar (t * y) : ℂ) = if t = 0 then (q : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · exact AddChar.sum_eq_zero_of_ne_one (isPrimitive_stdAddChar q h)

/-- `‖G‖² = q · Σ_{h : 2 a h = 0} e((a h² + c h)/q)`. -/
theorem gaussQ_mul_conj (a c : ZMod q) :
    gaussQ a c * (starRingEnd ℂ) (gaussQ a c) =
      (q : ℂ) * ∑ h : ZMod q, if 2 * a * h = 0 then (stdAddChar (a * h ^ 2 + c * h) : ℂ)
        else 0 := by
  simp only [gaussQ, map_sum, ← AddChar.map_neg_eq_conj, sum_mul_sum]
  -- substitute `x = y + h`
  have hsub : ∀ y : ZMod q, ∑ x : ZMod q, (stdAddChar (a * x ^ 2 + c * x) : ℂ) *
      stdAddChar (-(a * y ^ 2 + c * y)) =
      ∑ h : ZMod q, (stdAddChar (a * h ^ 2 + c * h) : ℂ) * stdAddChar (2 * a * h * y) := by
    intro y
    refine Fintype.sum_equiv (Equiv.subRight y) _ _ fun x => ?_
    rw [show (Equiv.subRight y) x = x - y from rfl]
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [sum_comm]
  simp_rw [hsub]
  rw [sum_comm]
  simp_rw [← mul_sum, sum_stdAddChar_mul]
  rw [mul_sum]
  refine sum_congr rfl fun h _ => ?_
  split_ifs <;> ring

/-- Elements killed by `2`. -/
theorem card_two_mul_eq_zero_le :
    (univ.filter fun h : ZMod q => 2 * h = 0).card ≤ 2 := by
  classical
  have hsub : (univ.filter fun h : ZMod q => 2 * h = 0) ⊆ {0, ((q / 2 : ℕ) : ZMod q)} := by
    intro h hh
    simp only [mem_filter, mem_univ, true_and] at hh
    simp only [mem_insert, mem_singleton]
    have h2 : ((2 * h.val : ℕ) : ZMod q) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
      push_cast
      exact hh
    have hv : q ∣ 2 * h.val := (ZMod.natCast_eq_zero_iff _ _).mp h2
    have hlt := ZMod.val_lt h
    obtain ⟨k, hk⟩ := hv
    have hk2 : k < 2 := by
      by_contra hk2
      push Not at hk2
      have : q * 2 ≤ q * k := Nat.mul_le_mul_left q hk2
      omega
    interval_cases k
    · left
      have : h.val = 0 := by omega
      exact (ZMod.val_eq_zero h).mp this
    · right
      have : h.val = q / 2 := by omega
      rw [← this, ZMod.natCast_zmod_val]
  calc _ ≤ ({0, ((q / 2 : ℕ) : ZMod q)} : Finset (ZMod q)).card := card_le_card hsub
    _ ≤ 2 := card_le_two

/-- **Gauss sums.** `‖G(a, c; q)‖² ≤ 2 q` for a unit `a`. -/
theorem norm_sq_gaussQ_le (a c : ZMod q) (ha : IsUnit a) : ‖gaussQ a c‖ ^ 2 ≤ 2 * q := by
  classical
  have h1 : (‖gaussQ a c‖ ^ 2 : ℝ) = ‖gaussQ a c * (starRingEnd ℂ) (gaussQ a c)‖ := by
    rw [norm_mul, Complex.norm_conj, sq]
  rw [h1, gaussQ_mul_conj, norm_mul, Complex.norm_natCast]
  have h2 : ‖∑ h : ZMod q, if 2 * a * h = 0 then (stdAddChar (a * h ^ 2 + c * h) : ℂ) else 0‖ ≤
      (univ.filter fun h : ZMod q => 2 * h = 0).card := by
    refine (norm_sum_le _ _).trans ?_
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
    refine sum_le_sum fun h _ => ?_
    have hiff : 2 * a * h = 0 ↔ 2 * h = 0 := by
      constructor
      · intro hh
        have : a * (2 * h) = 0 := by rw [← hh]; ring
        exact (ha.mul_right_eq_zero).mp this
      · intro hh; rw [mul_comm 2 a, mul_assoc, hh, mul_zero]
    split_ifs with hA hB hB
    · simp [AddChar.norm_apply]
    · exact absurd (hiff.mp hA) hB
    · simp
    · simp
  calc (q : ℝ) * ‖∑ h : ZMod q, if 2 * a * h = 0 then (stdAddChar (a * h ^ 2 + c * h) : ℂ)
        else 0‖ ≤ q * (univ.filter fun h : ZMod q => 2 * h = 0).card :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ q * 2 := mul_le_mul_of_nonneg_left (by exact_mod_cast card_two_mul_eq_zero_le)
        (by positivity)
    _ = 2 * q := by ring

/-- **Completing the square.** If `2 a` is a unit with inverse `u`, then
`G(a, c) = e(−a k²) G(a, 0)` with `k = c u`. -/
theorem gaussQ_eq_mul (a c u : ZMod q) (hu : 2 * a * u = 1) :
    gaussQ a c = stdAddChar (-(a * (c * u) ^ 2)) * gaussQ a 0 := by
  simp only [gaussQ, mul_sum, zero_mul, add_zero]
  refine Fintype.sum_equiv (Equiv.addRight (c * u)) _ _ fun b => ?_
  rw [show (Equiv.addRight (c * u)) b = b + c * u from rfl, ← AddChar.map_add_eq_mul]
  congr 1
  linear_combination (-(c * b)) * hu

/-- For `2 a` a unit, `‖G(a, c)‖² = q`. -/
theorem norm_sq_gaussQ_eq (a c : ZMod q) (h2a : IsUnit (2 * a)) : ‖gaussQ a c‖ ^ 2 = q := by
  classical
  have h1 : (‖gaussQ a c‖ ^ 2 : ℝ) = ‖gaussQ a c * (starRingEnd ℂ) (gaussQ a c)‖ := by
    rw [norm_mul, Complex.norm_conj, sq]
  rw [h1, gaussQ_mul_conj]
  have hsum : (∑ h : ZMod q, if 2 * a * h = 0 then (stdAddChar (a * h ^ 2 + c * h) : ℂ)
      else 0) = 1 := by
    rw [Finset.sum_eq_single (0 : ZMod q)]
    · simp
    · intro h _ hh
      have : 2 * a * h ≠ 0 := fun h0 => hh ((h2a.mul_right_eq_zero).mp h0)
      simp [this]
    · simp
  rw [hsum, mul_one, Complex.norm_natCast]

/-- Quaternion multiplication on `(ZMod q)⁴`. -/
def qmul (α x : Fin 4 → ZMod q) : Fin 4 → ZMod q :=
  ![α 0 * x 0 - α 1 * x 1 - α 2 * x 2 - α 3 * x 3,
    α 0 * x 1 + α 1 * x 0 + α 2 * x 3 - α 3 * x 2,
    α 0 * x 2 - α 1 * x 3 + α 2 * x 0 + α 3 * x 1,
    α 0 * x 3 + α 1 * x 2 - α 2 * x 1 + α 3 * x 0]

/-- The conjugate quaternion. -/
def qconj (α : Fin 4 → ZMod q) : Fin 4 → ZMod q := ![α 0, -α 1, -α 2, -α 3]

/-- The norm `Σ xᵢ²`. -/
def qnorm (x : Fin 4 → ZMod q) : ZMod q := ∑ i, x i ^ 2

omit [NeZero q] in
theorem qnorm_qmul (α x : Fin 4 → ZMod q) : qnorm (qmul α x) = qnorm α * qnorm x := by
  simp [qnorm, qmul, Fin.sum_univ_four]
  ring

omit [NeZero q] in
theorem qmul_qconj_qmul (α x : Fin 4 → ZMod q) : qmul (qconj α) (qmul α x) = qnorm α • x := by
  ext i
  fin_cases i <;> simp [qmul, qconj, qnorm, Fin.sum_univ_four] <;> ring

omit [NeZero q] in
theorem qmul_qmul_qconj (α x : Fin 4 → ZMod q) : qmul α (qmul (qconj α) x) = qnorm α • x := by
  ext i
  fin_cases i <;> simp [qmul, qconj, qnorm, Fin.sum_univ_four] <;> ring

omit [NeZero q] in
theorem qmul_smul (α x : Fin 4 → ZMod q) (t : ZMod q) : qmul α (t • x) = t • qmul α x := by
  ext i
  fin_cases i <;> simp [qmul] <;> ring

omit [NeZero q] in
/-- An additive character turns sums into products. -/
theorem addChar_sum {ι : Type*} (ψ : AddChar (ZMod q) ℂ) (s : Finset ι) (f : ι → ZMod q) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- The fourth power of `G(a, 0)` as a sum over `(ZMod q)⁴`. -/
theorem gaussQ_pow_four (a : ZMod q) :
    gaussQ a 0 ^ 4 = ∑ x : Fin 4 → ZMod q, (stdAddChar (a * qnorm x) : ℂ) := by
  simp only [gaussQ, zero_mul, add_zero, qnorm, mul_sum]
  rw [← Fin.prod_const, Fintype.prod_sum]
  refine Fintype.sum_congr _ _ fun x => ?_
  rw [addChar_sum]

/-- **`G(a, 0)⁴` does not depend on the unit `a`.** -/
theorem gaussQ_pow_four_eq (a : ZMod q) (ha : IsUnit a) :
    gaussQ a 0 ^ 4 = gaussQ (1 : ZMod q) 0 ^ 4 := by
  classical
  -- a quaternion of norm `a`
  obtain ⟨w, x, y, z, hwxyz⟩ := Nat.sum_four_squares a.val
  set α : Fin 4 → ZMod q := ![(w : ZMod q), x, y, z]
  have hα : qnorm α = a := by
    have : ((w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 : ℕ) : ZMod q) = a := by
      rw [hwxyz, ZMod.natCast_zmod_val]
    simp only [qnorm, Fin.sum_univ_four, α]
    simpa using this
  obtain ⟨u, hu⟩ := ha
  -- left multiplication by `α` is a bijection
  let e : (Fin 4 → ZMod q) ≃ (Fin 4 → ZMod q) :=
    { toFun := qmul α
      invFun := fun y => ((u⁻¹ : (ZMod q)ˣ) : ZMod q) • qmul (qconj α) y
      left_inv := fun x => by
        simp only
        rw [qmul_qconj_qmul, hα, ← hu, smul_smul, Units.inv_mul, one_smul]
      right_inv := fun y => by
        simp only
        rw [qmul_smul, qmul_qmul_qconj, hα, ← hu, smul_smul, Units.inv_mul, one_smul] }
  rw [gaussQ_pow_four, gaussQ_pow_four]
  refine (Fintype.sum_equiv e _ _ fun x => ?_)
  simp only [one_mul, e, Equiv.coe_fn_mk, qnorm_qmul, hα]

end FourSquaresCaps
