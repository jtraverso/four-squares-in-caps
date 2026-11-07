/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.FourSquaresDenseProof

/-!
# Proofs of the statements in `FourSquaresCapsChallenge.lean`

The proofs are in `FourSquaresCaps/` (namespace `FourSquaresCaps`).

* Jacobi (`JacobiField`, `JacobiSeries`, `JacobiCount`): the two finite identities of
  Andrews–Ekhad–Zeilberger, proved by WZ telescoping in any field, transported to `ℚ⟦X⟧` through
  its fraction field, and read modulo `X^{N+1}`.
* Caps (`GaussSum` … `FinalH2`): the delta method with Gaussian weights (exact formula through the
  theta transformation), Fourier bounds for the cut-off weight, the Weil bound for Kloosterman
  sums (from the Weil Bounds Toolkit, PALOMAR-2026-11-03-000018), and a comparison of centers on
  the sphere, which reduces the theorem to a linear lower bound for `r₄(m)` given by Jacobi.
-/

@[expose] public section

namespace FourSquaresInCaps

/-- **Jacobi's four-square theorem, odd case.** -/
theorem jacobi_four_squares_odd (N : ℕ) (hN : Odd N) :
    Nat.card {x : Fin 4 → ℤ // ∑ i, x i ^ 2 = N} = 8 * ∑ d ∈ N.divisors, d :=
  FourSquaresCaps.Jacobi.card_sum_four_sq_odd N hN

/-- **Four squares in caps.** For a unit vector `q ∈ ℝ⁴` and `δ > 0`, every large odd `m` is
`β₀² + β₁² + β₂² + β₃²` with `β ∈ ℤ⁴` and `|βᵢ − √m qᵢ| ≤ δ √m`. -/
theorem four_squares_in_caps (q : Fin 4 → ℝ) (hq : ∑ i, q i ^ 2 = 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m → Odd m →
      ∃ β : Fin 4 → ℤ, ∑ i, β i ^ 2 = (m : ℤ) ∧
        ∀ i, |(β i : ℝ) - Real.sqrt m * q i| ≤ δ * Real.sqrt m :=
  FourSquaresCaps.fourSquaresDense q hq δ hδ

end FourSquaresInCaps
