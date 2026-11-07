# Four squares in caps, and Jacobi's four-square theorem for odd N, in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A Lean 4 / Mathlib proof of two classical results on sums of four squares. Neither is in Mathlib,
which has Lagrange's four squares theorem (existence only).

## Statements (`FourSquaresCapsChallenge.lean`, namespace `FourSquaresInCaps`)

```lean
/-- Jacobi's four-square theorem, odd case: r₄(N) = 8 σ(N). -/
theorem jacobi_four_squares_odd (N : ℕ) (hN : Odd N) :
    Nat.card {x : Fin 4 → ℤ // ∑ i, x i ^ 2 = N} = 8 * ∑ d ∈ N.divisors, d

/-- Four squares in caps. -/
theorem four_squares_in_caps (q : Fin 4 → ℝ) (hq : ∑ i, q i ^ 2 = 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m → Odd m →
      ∃ β : Fin 4 → ℤ, ∑ i, β i ^ 2 = (m : ℤ) ∧
        ∀ i, |(β i : ℝ) - Real.sqrt m * q i| ≤ δ * Real.sqrt m
```

## Proof of Jacobi's theorem (`JacobiField`, `JacobiSeries`, `JacobiCount`)

After G. E. Andrews, S. B. Ekhad, D. Zeilberger, *A short proof of Jacobi's formula for the number
of representations of an integer as a sum of four squares*, Amer. Math. Monthly 100 (1993)
(arXiv:math/9206203). With `H_n = ∏_{j ≤ n} (1+q^j)/(1−q^j)`:

1. `JacobiField.lean`: in any field and for any `q` with `1 ± q^j ≠ 0`, Lemma (a)
   `∑_{|k| ≤ n} 4(−q)^k/(1+q^k)² H_n² H_{n+k} H_{n−k} = 1` and Lemma (b)
   `∑_{k ≤ n} 2(−q^{n+1})^k H_k/((1+q^k) H_n) = ∑_{|k| ≤ n} (−q)^{k²}`, by WZ telescoping. The
   sums are folded to `k ≥ 0`, and the paper's certificate for (a), which is singular at
   `k = −n−1`, is used in an equivalent removable form.
2. `JacobiSeries.lean`: transport to `ℚ⟦X⟧` through its fraction field. This gives identity (3),
   `θ_n⁴ = U_n⁴ W_n`, with `U_n ≡ 1` and `W_n ≡ 1 + 8 ∑_{k ≤ n} (−1)^k X^k/(1+X^k)²` modulo
   `X^{n+1}`. No limits are taken.
3. `JacobiCount.lean`: the coefficient of `X^N`. For odd `N`, `(−1)^k X^k/(1+X^k)²` contributes
   `−N/k` when `k ∣ N`, and the theta side counts the representations with sign `(−1)^N`.

## Proof of the caps theorem (`GaussSum` … `FinalH2`)

This is the Duke–Friedlander–Iwaniec delta method, in the form of D. R. Heath-Brown, *A new form
of the circle method…*, J. reine angew. Math. 481 (1996), with Gaussian weights.

* `GaussSum`, `Kloosterman`, `Twisted`, `KloostermanBound`, `Decomp`, `DecompSum`: quadratic Gauss
  sums, the exponential sums `S_q(m, c)` and their twisted multiplicativity, and a bound for
  `|S_q|` through a decomposition `q = q₀ q₁` with `q₁` squarefree. The bound uses the Weil bound for Kloosterman sums with squarefree
  modulus, imported from the Weil Bounds Toolkit (PALOMAR-2026-11-03-000018,
  `rml.weil.contracts`) as a lake dependency.
* `Delta`, `DFIWeight`, `DFIFourier`, `DFIL1`, `FourierBound`, `Integrals`, `Bumps`: the delta
  expansion with a smooth weight `ω`, the cut-off weight `h_q(u) = η(u/T) Δ_q(u)`, and the decay
  of its Fourier transform.
* `Theta`, `Assembly`, `Lattice`, `MainFormula`: an exact formula for the Gaussian-weighted count,
  through the theta transformation (Poisson summation).
* `ErrorTerm`, `ErrorIntegrals`, `ErrorBound`, `ErrorTotal`, `ArithSums`, `DivisorBound`: the
  `c ≠ 0` part is `O(m^{7/8} log⁴ m)`.
* `MainSplit`, `Covering`, `FinalH2`: the main term (`c = 0`) depends on the center of the cap only
  through its norm. So the counts at two centers of the same norm differ by at most twice the
  error. A grid of centers on the sphere and pigeonhole then reduce the theorem to
  `r₄(m) ≥ c·m` for odd `m` (`fourSquaresDense_of_reps`), which Jacobi's theorem provides
  (`FourSquaresDenseProof`).

## Building

Lean `v4.35.0-rc3`, Mathlib `v4.35.0-rc3` (c55e6e7), Weil Bounds Toolkit @ 0f3e4c3:

```
lake exe cache get
lake build
```

Axioms of both theorems: `propext`, `Classical.choice`, `Quot.sound`.
