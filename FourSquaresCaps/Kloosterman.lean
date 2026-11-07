/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.GaussSum

/-!
# The complete exponential sums of the delta method

`S_q(m, c) = ∑_{a ∈ (ZMod q)ˣ} e_q(−m a) ∏ᵢ G_q(a, cᵢ)` for `c ∈ (ZMod q)⁴`.

* `norm_expSumS_le`: the trivial bound `‖S_q(m, c)‖ ≤ φ(q) (2q)²`.
* `expSumS_eq`: for odd `q` (with `2 w = 1`), completing the square in each Gauss sum gives
  `S_q(m, c) = G_q(1, 0)⁴ · ∑_{x unit} e_q(B x + A x⁻¹)` with `A = −m`, `B = −w²|c|²`, a
  Kloosterman sum with first coefficient `−m`.
* `norm_gaussQ_one_pow_four`: `‖G_q(1, 0)⁴‖ = q²` for odd `q`.
-/

@[expose] public section

namespace FourSquaresCaps

open ZMod Finset

variable {q : ℕ} [NeZero q]

/-- The complete exponential sum `S_q(m, c) = ∑_{a unit} e_q(−m a) ∏ᵢ G_q(a, cᵢ)`. -/
noncomputable def expSumS (m : ZMod q) (c : Fin 4 → ZMod q) : ℂ :=
  ∑ a : (ZMod q)ˣ, stdAddChar (-(m * (a : ZMod q))) * ∏ i, gaussQ (a : ZMod q) (c i)

theorem norm_gaussQ_le (a c : ZMod q) (ha : IsUnit a) : ‖gaussQ a c‖ ≤ Real.sqrt (2 * q) := by
  rw [← Real.sqrt_sq (norm_nonneg _)]
  exact Real.sqrt_le_sqrt (norm_sq_gaussQ_le a c ha)

/-- **Trivial bound.** `‖S_q(m, c)‖ ≤ φ(q) (2q)²`. -/
theorem norm_expSumS_le (m : ZMod q) (c : Fin 4 → ZMod q) :
    ‖expSumS m c‖ ≤ q.totient * (2 * q) ^ 2 := by
  unfold expSumS
  have hterm : ∀ a : (ZMod q)ˣ,
      ‖(stdAddChar (-(m * (a : ZMod q))) : ℂ) * ∏ i, gaussQ (a : ZMod q) (c i)‖ ≤ (2 * q) ^ 2 := by
    intro a
    rw [norm_mul, AddChar.norm_apply, one_mul, norm_prod]
    have hs : Real.sqrt (2 * q) ^ 4 = (2 * q) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by positivity)]
    calc ∏ i, ‖gaussQ (a : ZMod q) (c i)‖ ≤ ∏ _i : Fin 4, Real.sqrt (2 * q) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => norm_gaussQ_le _ _ a.isUnit
      _ = (2 * q) ^ 2 := by rw [prod_const, card_univ, Fintype.card_fin, hs]
  calc ‖∑ a : (ZMod q)ˣ, (stdAddChar (-(m * (a : ZMod q))) : ℂ) * ∏ i, gaussQ (a : ZMod q) (c i)‖
      ≤ ∑ a : (ZMod q)ˣ, ((2 : ℝ) * q) ^ 2 := (norm_sum_le _ _).trans (sum_le_sum fun a _ => hterm a)
    _ = q.totient * (2 * q) ^ 2 := by
      rw [sum_const, card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]

/-- **Kloosterman form for odd `q`.** If `2 w = 1` in `ZMod q`, then
`S_q(m, c) = G_q(1, 0)⁴ · ∑_{x unit} e_q(−w²|c|² x − m x⁻¹)`. -/
theorem expSumS_eq (w : ZMod q) (hw : 2 * w = 1) (m : ZMod q) (c : Fin 4 → ZMod q) :
    expSumS m c = gaussQ (1 : ZMod q) 0 ^ 4 *
      ∑ x : (ZMod q)ˣ, (stdAddChar (-(w ^ 2 * ∑ i, c i ^ 2) * (x : ZMod q) +
        -m * ((x⁻¹ : (ZMod q)ˣ) : ZMod q)) : ℂ) := by
  unfold expSumS
  rw [mul_sum]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun a => ?_
  simp only [Equiv.inv_apply, inv_inv]
  set ai : ZMod q := ((a⁻¹ : (ZMod q)ˣ) : ZMod q) with hai
  have haai : (a : ZMod q) * ai = 1 := by simp [ai]
  have hG : ∀ i, gaussQ (a : ZMod q) (c i) =
      stdAddChar (-(w ^ 2 * c i ^ 2 * ai)) * gaussQ (a : ZMod q) 0 := by
    intro i
    rw [gaussQ_eq_mul (a : ZMod q) (c i) (w * ai)
      (by linear_combination ((a : ZMod q) * ai) * hw + haai)]
    rw [show (a : ZMod q) * (c i * (w * ai)) ^ 2 = w ^ 2 * c i ^ 2 * ai by
      linear_combination (w ^ 2 * c i ^ 2 * ai) * haai]
  calc (stdAddChar (-(m * (a : ZMod q))) : ℂ) * ∏ i, gaussQ (a : ZMod q) (c i)
      = stdAddChar (-(m * (a : ZMod q))) * (stdAddChar (∑ i, -(w ^ 2 * c i ^ 2 * ai)) *
          gaussQ (a : ZMod q) 0 ^ 4) := by
        rw [prod_congr rfl (fun i _ => hG i), prod_mul_distrib, prod_const, card_univ,
          Fintype.card_fin, addChar_sum]
    _ = gaussQ (1 : ZMod q) 0 ^ 4 *
          (stdAddChar (-(m * (a : ZMod q))) * stdAddChar (∑ i, -(w ^ 2 * c i ^ 2 * ai))) := by
        rw [gaussQ_pow_four_eq _ a.isUnit]; ring
    _ = _ := by
        rw [← AddChar.map_add_eq_mul]
        congr 2
        simp only [Fin.sum_univ_four]
        ring

/-- For odd `q`, `‖G_q(1, 0)⁴‖ = q²`. -/
theorem norm_gaussQ_one_pow_four (h2 : IsUnit (2 : ZMod q)) :
    ‖gaussQ (1 : ZMod q) 0 ^ 4‖ = (q : ℝ) ^ 2 := by
  have h := norm_sq_gaussQ_eq (1 : ZMod q) 0 (by simpa using h2)
  rw [norm_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h]

/-- For odd `q`: `‖S_q(m, c)‖ = q² ‖K‖` with the Kloosterman sum `K` of `expSumS_eq`. -/
theorem norm_expSumS_eq (w : ZMod q) (hw : 2 * w = 1) (m : ZMod q) (c : Fin 4 → ZMod q) :
    ‖expSumS m c‖ = (q : ℝ) ^ 2 *
      ‖∑ x : (ZMod q)ˣ, (stdAddChar (-(w ^ 2 * ∑ i, c i ^ 2) * (x : ZMod q) +
        -m * ((x⁻¹ : (ZMod q)ˣ) : ZMod q)) : ℂ)‖ := by
  have h2 : IsUnit (2 : ZMod q) := isUnit_iff_exists_inv.mpr ⟨w, hw⟩
  rw [expSumS_eq w hw, norm_mul, norm_gaussQ_one_pow_four h2]

end FourSquaresCaps
