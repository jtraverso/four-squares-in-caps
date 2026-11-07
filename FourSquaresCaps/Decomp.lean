/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.KloostermanBound
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.Nat.Squarefree

/-!
# The decomposition `q = q₀ q₁` for Weil's bound

`GoodDecomp M q q₀ q₁`: `q = q₀ q₁`, coprime, `q₁` squarefree and coprime to `M`, and every
prime of `q₀` divides `M` or divides `q₀` twice. Every `q` has one (`exists_goodDecomp`).
`norm_expSumS_le_decomp`: `‖S_q(m, c)‖ ≤ φ(q₀)(2q₀)² · q₁² 2^{ω(q₁)} √q₁` for `M = 2|m|`.
-/

@[expose] public section

namespace FourSquaresCaps

/-- The decomposition. -/
def GoodDecomp (M q q₀ q₁ : ℕ) : Prop :=
  q = q₀ * q₁ ∧ q₀.Coprime q₁ ∧ Squarefree q₁ ∧ q₁.Coprime M ∧
    ∀ p, p.Prime → p ∣ q₀ → p ∣ M ∨ p ^ 2 ∣ q₀

theorem exists_goodDecomp (M : ℕ) : ∀ q, ∃ q₀ q₁, GoodDecomp M q q₀ q₁ := by
  refine Nat.recOnPrimeCoprime ?_ ?_ ?_
  · refine ⟨0, 1, by simp, by simp, squarefree_one, Nat.coprime_one_left M,
      fun p _ _ => Or.inr (dvd_zero _)⟩
  · intro p n hp
    by_cases h : n = 1 ∧ ¬ p ∣ M
    · obtain ⟨rfl, hpM⟩ := h
      refine ⟨1, p, by simp, Nat.coprime_one_left p, hp.prime.squarefree,
        (Nat.Prime.coprime_iff_not_dvd hp).mpr hpM, fun p' hp' h1 => ?_⟩
      exact absurd (Nat.le_of_dvd one_pos h1) (by have := hp'.two_le; omega)
    · refine ⟨p ^ n, 1, by simp, Nat.coprime_one_right _, squarefree_one,
        Nat.coprime_one_left M, fun p' hp' hdvd => ?_⟩
      have hpp : p' = p := (Nat.prime_dvd_prime_iff_eq hp' hp).mp (hp'.dvd_of_dvd_pow hdvd)
      subst hpp
      by_cases hM : p' ∣ M
      · exact Or.inl hM
      · right
        have hn : n ≠ 1 := fun h1 => h ⟨h1, hM⟩
        have hn0 : n ≠ 0 := by
          rintro rfl
          simp at hdvd
          exact hp'.one_lt.ne' hdvd
        exact pow_dvd_pow p' (by omega)
  · intro a b _ _ hab ⟨a₀, a₁, ha, ha01, ha1, ha1M, ha0⟩ ⟨b₀, b₁, hb, hb01, hb1, hb1M, hb0⟩
    have hca : a₀.Coprime b₁ := (Nat.Coprime.coprime_dvd_left (Dvd.intro _ ha.symm)
      (Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ hb.symm) hab))
    have hcb : b₀.Coprime a₁ := (Nat.Coprime.coprime_dvd_left (Dvd.intro _ hb.symm)
      (Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ ha.symm) hab.symm))
    have hc11 : a₁.Coprime b₁ := (Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ ha.symm)
      (Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ hb.symm) hab))
    refine ⟨a₀ * b₀, a₁ * b₁, by rw [ha, hb]; ring, ?_, ?_, ?_, ?_⟩
    · exact Nat.coprime_mul_iff_left.mpr ⟨Nat.Coprime.mul_right ha01 hca,
        Nat.Coprime.mul_right hcb hb01⟩
    · exact (Nat.squarefree_mul_iff.mpr ⟨hc11, ha1, hb1⟩)
    · exact Nat.coprime_mul_iff_left.mpr ⟨ha1M, hb1M⟩
    · intro p hp hdvd
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
      · rcases ha0 p hp h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (dvd_mul_of_dvd_left h' _)
      · rcases hb0 p hp h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (dvd_mul_of_dvd_right h' _)

/-- **Weil's bound through the decomposition.** -/
theorem norm_expSumS_le_decomp (m : ℤ) {q q₀ q₁ : ℕ} (hd : GoodDecomp (2 * m.natAbs) q q₀ q₁)
    [NeZero q] (c : Fin 4 → ℤ) :
    ‖expSumS (q := q) (m : ZMod q) (fun i => (c i : ZMod q))‖ ≤
      (q₀.totient * (2 * q₀) ^ 2) *
        ((q₁ : ℝ) ^ 2 * ((2 : ℝ) ^ q₁.primeFactors.card * Real.sqrt q₁)) := by
  obtain ⟨hq, hcop, hsq, hM, -⟩ := hd
  have hq0 : q₀ ≠ 0 := fun h => NeZero.ne q (by rw [hq, h, zero_mul])
  have hq1 : q₁ ≠ 0 := fun h => NeZero.ne q (by rw [hq, h, mul_zero])
  have : NeZero q₀ := ⟨hq0⟩
  have : NeZero q₁ := ⟨hq1⟩
  have hodd : Odd q₁ := by
    rw [Nat.odd_iff]
    have : ¬ 2 ∣ q₁ := fun h2 => by
      have := Nat.Coprime.coprime_dvd_left h2 hM
      exact absurd (Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 _) this) (by norm_num)
    omega
  have hm : IsCoprime m (q₁ : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    have := Nat.Coprime.coprime_dvd_right (dvd_mul_left m.natAbs 2) hM
    simpa [Int.gcd, Nat.Coprime] using this
  subst hq
  exact norm_expSumS_mul_le hcop hsq hodd m hm c

end FourSquaresCaps
