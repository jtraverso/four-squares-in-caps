/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Four squares in caps: the statement

`FourSquaresDense`: for every unit vector `q ∈ ℝ⁴` and `δ > 0`, every large odd `m` is
`β₀² + β₁² + β₂² + β₃²` with `β ∈ ℤ⁴` and `|βᵢ − √m qᵢ| ≤ δ √m`.
-/

@[expose] public section

namespace FourSquaresCaps

/-- **Four squares in caps.** -/
def FourSquaresDense : Prop :=
  ∀ q : Fin 4 → ℝ, ∑ i, q i ^ 2 = 1 → ∀ δ > 0, ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m → Odd m →
    ∃ β : Fin 4 → ℤ, ∑ i, β i ^ 2 = (m : ℤ) ∧
      ∀ i, |(β i : ℝ) - Real.sqrt m * q i| ≤ δ * Real.sqrt m

end FourSquaresCaps
