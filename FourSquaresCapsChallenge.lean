/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.NumberTheory.Divisors

/-!
# Four squares in caps, and Jacobi's four-square theorem for odd `N`

* `jacobi_four_squares_odd`: for odd `N`, the number of `x ∈ ℤ⁴` with `x₀² + x₁² + x₂² + x₃² = N`
  is `8 σ(N)` (C. G. J. Jacobi, 1829; proof of G. E. Andrews, S. B. Ekhad and D. Zeilberger,
  Amer. Math. Monthly 100 (1993)).
* `four_squares_in_caps`: the integer points on the sphere `x₀² + x₁² + x₂² + x₃² = m`, `m` odd,
  meet every cap of fixed angular radius once `m` is large (the four-variable case of the
  equidistribution of lattice points on spheres; Kloosterman's method, here via the
  Duke–Friedlander–Iwaniec delta method and the Weil bound for Kloosterman sums).
-/

@[expose] public section

namespace FourSquaresInCaps

/-- **Jacobi's four-square theorem, odd case.** -/
theorem jacobi_four_squares_odd (N : ℕ) (hN : Odd N) :
    Nat.card {x : Fin 4 → ℤ // ∑ i, x i ^ 2 = N} = 8 * ∑ d ∈ N.divisors, d := by
  sorry

/-- **Four squares in caps.** For a unit vector `q ∈ ℝ⁴` and `δ > 0`, every large odd `m` is
`β₀² + β₁² + β₂² + β₃²` with `β ∈ ℤ⁴` and `|βᵢ − √m qᵢ| ≤ δ √m`. -/
theorem four_squares_in_caps (q : Fin 4 → ℝ) (hq : ∑ i, q i ^ 2 = 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m → Odd m →
      ∃ β : Fin 4 → ℤ, ∑ i, β i ^ 2 = (m : ℤ) ∧
        ∀ i, |(β i : ℝ) - Real.sqrt m * q i| ≤ δ * Real.sqrt m := by
  sorry

end FourSquaresInCaps
