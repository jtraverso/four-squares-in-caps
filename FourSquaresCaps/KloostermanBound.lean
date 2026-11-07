/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.Twisted
public import rml.weil.contracts

/-!
# Weil's bound for `S_q(m, c)`

* `norm_expSumS_squarefree_le`: for squarefree odd `q` and `m` a unit mod `q`,
  `‖S_q(m, c)‖ ≤ q² · 2^{ω(q)} √q` (Weil's bound for Kloosterman sums, from the registered Weil
  Bounds Toolkit, `RML.ExpSum.Weil.squarefreeUnitNumerator_bound`).
* `norm_expSumS_mul_le`: for `q = q₀ q₁` with `q₁` squarefree, odd, coprime to `q₀` and to `m`,
  `‖S_q(m, c)‖ ≤ φ(q₀) (2 q₀)² · q₁² 2^{ω(q₁)} √q₁` (twisted multiplicativity, trivial bound on
  `q₀`).
-/

@[expose] public section

namespace FourSquaresCaps

open ZMod Finset

/-- **Weil's bound for `S_q`.** Squarefree odd `q`, `m` a unit. -/
theorem norm_expSumS_squarefree_le {q : ℕ} [NeZero q] (hsq : Squarefree q)
    (h2 : IsUnit (2 : ZMod q)) (m : ZMod q) (hm : IsUnit m) (c : Fin 4 → ZMod q) :
    ‖expSumS m c‖ ≤ (q : ℝ) ^ 2 * ((2 : ℝ) ^ q.primeFactors.card * Real.sqrt q) := by
  obtain ⟨w, hw⟩ := h2.exists_right_inv
  rw [norm_expSumS_eq w hw]
  gcongr
  exact RML.ExpSum.Weil.squarefreeUnitNumerator_bound hsq (-m) (-(w ^ 2 * ∑ i, c i ^ 2)) hm.neg

/-- **Bound for `S_q` with a squarefree part.** -/
theorem norm_expSumS_mul_le {q₀ q₁ : ℕ} [NeZero q₀] [NeZero q₁] (hcop : q₀.Coprime q₁)
    (hsq : Squarefree q₁) (hodd : Odd q₁) (m : ℤ) (hm : IsCoprime m (q₁ : ℤ))
    (c : Fin 4 → ℤ) :
    ‖expSumS (q := q₀ * q₁) (m : ZMod (q₀ * q₁)) (fun i => (c i : ZMod (q₀ * q₁)))‖ ≤
      (q₀.totient * (2 * q₀) ^ 2) *
        ((q₁ : ℝ) ^ 2 * ((2 : ℝ) ^ q₁.primeFactors.card * Real.sqrt q₁)) := by
  obtain ⟨s', r', hb⟩ : IsCoprime (q₁ : ℤ) (q₀ : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr hcop.symm
  rw [expSumS_mul hcop r' s' hb m c, norm_mul]
  refine mul_le_mul (norm_expSumS_le _ _) ?_ (norm_nonneg _) (by positivity)
  refine norm_expSumS_squarefree_le hsq ?_ _ ?_ _
  · obtain ⟨k, hk⟩ := hodd
    refine isUnit_iff_exists_inv.mpr ⟨-(k : ZMod q₁), ?_⟩
    have : ((2 * k + 1 : ℕ) : ZMod q₁) = 0 := by rw [← hk]; exact ZMod.natCast_self q₁
    push_cast at this
    linear_combination -this
  · obtain ⟨u, v, huv⟩ := hm
    refine isUnit_iff_exists_inv.mpr ⟨(u : ZMod q₁), ?_⟩
    have := congrArg (Int.cast : ℤ → ZMod q₁) huv
    push_cast at this
    rw [ZMod.natCast_self, mul_zero, add_zero] at this
    linear_combination this

end FourSquaresCaps
