# Mathlib definitions used in FourSquaresCapsChallenge.lean

Verbatim excerpts of the Mathlib definitions used by the statements in `FourSquaresCapsChallenge.lean`, at the
pinned Mathlib revision `c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`, repository
https://github.com/leanprover-community/mathlib4). Mathlib is released under the Apache-2.0
licence. Each excerpt gives the file and line at that revision; the complete source is at
`https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/<file>`.

These excerpts are provided so that the meaning of every imported notion used by the
Challenge can be audited without fetching Mathlib. The notation `∑ x ∈ s, f x` is `Finset.sum s f`; `Nat`, `Int`, `Fin`, `ℝ` and `^` on `ℕ` exponents are core or Mathlib basics.

## Finset.prod / Finset.sum (notation `∑ i, f i`, the additive version via `to_additive`)

`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`, line 68:

```lean
protected def prod [CommMonoid M] (s : Finset ι) (f : ι → M) : M :=
  (s.1.map f).prod
```

## Nat.card

`Mathlib/SetTheory/Cardinal/Finite.lean`, line 39:

```lean
/-- `Nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `Nat.card α = 0`. -/
protected def card (α : Type*) : ℕ :=
  toNat (mk α)
```

## Nat.divisors

`Mathlib/NumberTheory/Divisors.lean`, line 51:

```lean
/-- `divisors n` is the `Finset` of divisors of `n`. By convention, we set `divisors 0 = ∅`. -/
def divisors : Finset ℕ := {d ∈ Ico 1 (n + 1) | d ∣ n}
```

## Odd

`Mathlib/Algebra/Ring/Parity.lean`, line 98:

```lean
/-- An element `a` of a semiring is odd if there exists `k` such `a = 2*k + 1`. -/
def Odd (a : α) : Prop := ∃ k, a = 2 * k + 1
```

## Real.sqrt

`Mathlib/Analysis/Real/Sqrt.lean`, line 109:

```lean
/-- The square root of a real number. This returns 0 for negative inputs.

This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`. -/
@[irreducible] noncomputable def sqrt (x : ℝ) : ℝ :=
  NNReal.sqrt (Real.toNNReal x)
```

## mabs / abs (notation `|a|`, the additive version via `to_additive`)

`Mathlib/Algebra/Order/Group/Unbundled/Abs.lean`, line 35:

```lean
/-- `mabs a`, denoted `|a|ₘ`, is the absolute value of `a`. -/
@[to_additive (attr := grind) /-- `abs a`, denoted `|a|`, is the absolute value of `a` -/]
def mabs (a : α) : α := a ⊔ a⁻¹
```
