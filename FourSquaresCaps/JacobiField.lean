/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# The Andrews–Ekhad–Zeilberger identities in a field

Following G. E. Andrews, S. B. Ekhad, D. Zeilberger, *A short proof of Jacobi's formula for the
number of representations of an integer as a sum of four squares*, Amer. Math. Monthly 100 (1993),
we prove, in any field `K` and for any `q : K` with `1 - q^j ≠ 0` (`j ≥ 1`) and `1 + q^j ≠ 0`,
the two finite identities (Lemma (a), (b) of the paper) by WZ telescoping, folded to `k ≥ 0`:

* (a) `F n 0 + 2 ∑_{k=1}^{n} F n k = 1`, `F n k = 4(-1)^k q^k/(1+q^k)^2 H_n^2 H_{n+k} H_{n-k}`;
* (b) `∑_{k=0}^{n} 2(-1)^k q^{(n+1)k}/(1+q^k) H_k/H_n = 1 + 2 ∑_{k=1}^{n} (-1)^k q^{k^2}`,

where `H_n = ∏_{j=1}^{n} (1+q^j)/(1-q^j)`.
-/

@[expose] public section

namespace FourSquaresCaps.Jacobi

open Finset

variable {K : Type*} [Field K]

/-- `H_n = ∏_{j=1}^{n} (1+q^j)/(1-q^j)`. -/
def Hf (q : K) : ℕ → K
  | 0 => 1
  | m + 1 => Hf q m * ((1 + q ^ (m + 1)) / (1 - q ^ (m + 1)))

/-- Standing hypotheses on `q`. -/
structure Good (q : K) : Prop where
  sub : ∀ j, 1 ≤ j → 1 - q ^ j ≠ 0
  add : ∀ j, 1 + q ^ j ≠ 0

variable {q : K}

theorem Good.two (hq : Good q) : (2 : K) ≠ 0 := by
  have := hq.add 0; rwa [pow_zero, one_add_one_eq_two] at this

theorem Hf_succ (q : K) (m : ℕ) :
    Hf q (m + 1) = Hf q m * ((1 + q ^ (m + 1)) / (1 - q ^ (m + 1))) := rfl

theorem Hf_ne_zero (hq : Good q) : ∀ m, Hf q m ≠ 0
  | 0 => one_ne_zero
  | m + 1 => by
    rw [Hf_succ]
    exact mul_ne_zero (Hf_ne_zero hq m)
      (div_ne_zero (hq.add _) (hq.sub _ (by omega)))

/-! ### Lemma (a) -/

/-- The summand of (a), for `k ≤ n`. -/
def Fa (q : K) (n k : ℕ) : K :=
  4 * (-1) ^ k * q ^ k / (1 + q ^ k) ^ 2 * Hf q n ^ 2 * Hf q (n + k) * Hf q (n - k)

/-- The WZ certificate of (a). -/
def Ga (q : K) (n k : ℕ) : K :=
  4 * (-1) ^ k * q ^ (n + 1) * (1 + q ^ (2 * n + 2)) * Hf q n ^ 2 * Hf q (n - k) *
    Hf q (n + k + 1) / ((1 - q ^ (n + 1)) ^ 3 * (1 + q ^ (n + 1)))

/-- The folded left side of (a). -/
def Sa (q : K) (n : ℕ) : K := Fa q n 0 + 2 * ∑ i ∈ range n, Fa q n (i + 1)

theorem rat_I0 (A : K) (h1 : 1 - A ≠ 0) (h2 : 1 + A ≠ 0) :
    ((1 + A) / (1 - A)) ^ 4 - 1 =
      2 * (4 * A * (1 + A ^ 2) * ((1 + A) / (1 - A)) / ((1 - A) ^ 3 * (1 + A))) := by
  field_simp
  ring

theorem rat_Ik (B C : K) (hB : 1 + B ≠ 0) (hA1 : 1 - B * C ≠ 0) (hA2 : 1 + B * C ≠ 0)
    (hAB : 1 - B ^ 2 * C ≠ 0) (hC : 1 - C ≠ 0) :
    B / (1 + B) ^ 2 * (((1 + B * C) / (1 - B * C)) ^ 2 * ((1 + B ^ 2 * C) / (1 - B ^ 2 * C)) *
        ((1 + C) / (1 - C)) - 1) =
      B * C * (1 + (B * C) ^ 2) / ((1 - B * C) ^ 3 * (1 + B * C)) *
        ((1 + B ^ 2 * C) / (1 - B ^ 2 * C) + (1 + C) / (1 - C)) := by
  field_simp
  ring

theorem rat_In (A : K) (h1 : 1 - A ≠ 0) (h2 : 1 + A ≠ 0) :
    ((1 + A) / (1 - A)) ^ 2 * ((1 + A ^ 2) / (1 - A ^ 2)) / (1 + A) ^ 2 =
      (1 + A ^ 2) / ((1 - A) ^ 3 * (1 + A)) := by
  have : 1 - A ^ 2 = (1 - A) * (1 + A) := by ring
  rw [this]
  field_simp

theorem Good.four (hq : Good q) : (4 : K) ≠ 0 := by
  rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero hq.two hq.two

theorem four_div_sq (hq : Good q) : (4 : K) / (1 + 1) ^ 2 = 1 := by
  rw [one_add_one_eq_two, show (2 : K) ^ 2 = 4 by norm_num]; exact div_self hq.four

theorem step_I0 (hq : Good q) (n : ℕ) : Fa q (n + 1) 0 - Fa q n 0 = 2 * Ga q n 0 := by
  have h1 := hq.sub (n + 1) (by omega)
  have h2 := hq.add (n + 1)
  have e := rat_I0 (q ^ (n + 1)) h1 h2
  unfold Fa Ga
  simp only [pow_zero, mul_one, Nat.sub_zero, add_zero]
  rw [four_div_sq hq, Hf_succ, show 2 * n + 2 = 2 * (n + 1) by ring, pow_mul']
  set r := (1 + q ^ (n + 1)) / (1 - q ^ (n + 1))
  set H := Hf q n
  linear_combination H ^ 4 * e

theorem step_Ik (hq : Good q) (m j : ℕ) :
    Fa q (m + (j + 1) + 1) (j + 1) - Fa q (m + (j + 1)) (j + 1) =
      Ga q (m + (j + 1)) (j + 1) - Ga q (m + (j + 1)) j := by
  unfold Fa Ga
  rw [show m + (j + 1) + 1 + (j + 1) = m + (j + 1) + (j + 1) + 1 by omega,
    show m + (j + 1) + 1 - (j + 1) = m + 1 by omega, show m + (j + 1) - (j + 1) = m by omega,
    show m + (j + 1) - j = m + 1 by omega, show m + (j + 1) + j + 1 = m + (j + 1) + (j + 1) by omega,
    Hf_succ q (m + (j + 1)), Hf_succ q (m + (j + 1) + (j + 1)), Hf_succ q m]
  have hA : q ^ (m + (j + 1) + 1) = q ^ (j + 1) * q ^ (m + 1) := by
    rw [← pow_add]; congr 1; omega
  have hAB : q ^ (m + (j + 1) + (j + 1) + 1) = (q ^ (j + 1)) ^ 2 * q ^ (m + 1) := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  have hA2 : q ^ (2 * (m + (j + 1)) + 2) = (q ^ (j + 1) * q ^ (m + 1)) ^ 2 := by
    rw [← hA, ← pow_mul]; congr 1; ring
  rw [hA, hAB, hA2]
  have e := rat_Ik (q ^ (j + 1)) (q ^ (m + 1)) (hq.add _) (by rw [← hA]; exact hq.sub _ (by omega))
    (by rw [← hA]; exact hq.add _) (by rw [← hAB]; exact hq.sub _ (by omega))
    (hq.sub _ (by omega))
  set B := q ^ (j + 1)
  set C := q ^ (m + 1)
  linear_combination 4 * (-1) ^ (j + 1) * Hf q (m + (j + 1)) ^ 2 * Hf q (m + (j + 1) + (j + 1)) *
    Hf q m * e

theorem step_In (hq : Good q) (n : ℕ) : Fa q (n + 1) (n + 1) = -Ga q n n := by
  unfold Fa Ga
  rw [Nat.sub_self, Nat.sub_self, show n + 1 + (n + 1) = n + n + 1 + 1 by omega,
    Hf_succ q (n + n + 1), Hf_succ q n]
  have hA2 : q ^ (n + n + 1 + 1) = (q ^ (n + 1)) ^ 2 := by rw [← pow_mul]; congr 1; ring
  have hA2' : q ^ (2 * n + 2) = (q ^ (n + 1)) ^ 2 := by rw [← pow_mul]; congr 1; ring
  rw [hA2, hA2']
  have e := rat_In (q ^ (n + 1)) (hq.sub _ (by omega)) (hq.add _)
  set A := q ^ (n + 1)
  linear_combination 4 * (-1) ^ (n + 1) * A * Hf q n ^ 2 * Hf q (n + n + 1) * Hf q 0 * e

theorem lemma_a (hq : Good q) : ∀ n, Sa q n = 1
  | 0 => by
    unfold Sa Fa
    simp only [range_zero, sum_empty, mul_zero, add_zero, pow_zero, mul_one, Nat.sub_zero, Hf]
    rw [four_div_sq hq, one_pow, mul_one]
  | n + 1 => by
    rw [← lemma_a hq n]
    unfold Sa
    rw [sum_range_succ, step_In hq n]
    have hstep : ∀ i ∈ range n, Fa q (n + 1) (i + 1) =
        Fa q n (i + 1) + (Ga q n (i + 1) - Ga q n i) := by
      intro i hi
      obtain ⟨m, rfl⟩ : ∃ m, n = m + (i + 1) := ⟨n - (i + 1), by rw [mem_range] at hi; omega⟩
      rw [← step_Ik hq m i]; ring
    rw [sum_congr rfl hstep, sum_add_distrib, sum_range_sub (fun i => Ga q n i)]
    have h0 := step_I0 hq n
    linear_combination h0

/-! ### Lemma (b) -/

/-- The summand of (b). -/
def Fb (q : K) (n k : ℕ) : K :=
  2 * (-1) ^ k * q ^ ((n + 1) * k) / (1 + q ^ k) * Hf q k / Hf q n

/-- The WZ certificate of (b). -/
def Gb (q : K) (n k : ℕ) : K :=
  2 * (-1) ^ (k + 1) * q ^ ((n + 1) * (k + 1)) * Hf q k / ((1 + q ^ (n + 1)) * Hf q n)

/-- Truncated theta function `∑_{|k| ≤ n} (-1)^k q^{k^2}`. -/
def thetaF (q : K) (n : ℕ) : K := 1 + 2 * ∑ i ∈ range n, (-1) ^ (i + 1) * q ^ ((i + 1) ^ 2)

theorem stepb_0 (hq : Good q) (n : ℕ) : Fb q (n + 1) 0 - Fb q n 0 = Gb q n 0 := by
  unfold Fb Gb
  simp only [mul_zero, pow_zero, mul_one, zero_add, pow_one, Hf_succ]
  have := Hf_ne_zero hq n
  have h1 := hq.sub (n + 1) (by omega)
  have h2 := hq.add (n + 1)
  have h22 := hq.add 0
  rw [pow_zero] at h22
  simp only [Hf]
  field_simp
  ring

theorem stepb_k (hq : Good q) (n j : ℕ) :
    Fb q (n + 1) (j + 1) - Fb q n (j + 1) = Gb q n (j + 1) - Gb q n j := by
  unfold Fb Gb
  rw [show (n + 1 + 1) * (j + 1) = (n + 1) * (j + 1) + (j + 1) by ring,
    show (n + 1) * (j + 1 + 1) = (n + 1) * (j + 1) + (n + 1) by ring, pow_add, pow_add,
    Hf_succ q n, Hf_succ q j]
  have := Hf_ne_zero hq n
  have := Hf_ne_zero hq j
  have h1 := hq.sub (n + 1) (by omega)
  have h2 := hq.add (n + 1)
  have h3 := hq.sub (j + 1) (by omega)
  have h4 := hq.add (j + 1)
  set D := q ^ ((n + 1) * (j + 1))
  field_simp
  ring

theorem stepb_top (hq : Good q) (n : ℕ) :
    Fb q (n + 1) (n + 1) + Gb q n n = 2 * ((-1) ^ (n + 1) * q ^ ((n + 1) ^ 2)) := by
  unfold Fb Gb
  rw [show (n + 1 + 1) * (n + 1) = (n + 1) ^ 2 + (n + 1) by ring,
    show (n + 1) * (n + 1) = (n + 1) ^ 2 by ring, pow_add]
  have := Hf_ne_zero hq n
  have := Hf_ne_zero hq (n + 1)
  have h2 := hq.add (n + 1)
  field_simp
  ring

theorem lemma_b (hq : Good q) : ∀ n, ∑ k ∈ range (n + 1), Fb q n k = thetaF q n
  | 0 => by
    unfold Fb thetaF
    simp only [zero_add, range_one, sum_singleton, mul_zero, pow_zero, mul_one, Hf,
      range_zero, sum_empty, add_zero]
    have h22 := hq.add 0
    rw [pow_zero] at h22
    field_simp
    ring
  | n + 1 => by
    have ih := lemma_b hq n
    unfold thetaF at ih ⊢
    rw [sum_range_succ (fun i => (-1) ^ (i + 1) * q ^ ((i + 1) ^ 2)), sum_range_succ]
    have hstep : ∀ k ∈ range (n + 1), Fb q (n + 1) k =
        Fb q n k + (Gb q n k - if k = 0 then 0 else Gb q n (k - 1)) := by
      intro k _
      rcases k with _ | j
      · rw [if_pos rfl, sub_zero, ← stepb_0 hq n]; ring
      · rw [if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel]
        rw [← stepb_k hq n j]; ring
    rw [sum_congr rfl hstep, sum_add_distrib, ih]
    have htel : ∑ k ∈ range (n + 1), (Gb q n k - if k = 0 then 0 else Gb q n (k - 1)) =
        Gb q n n := by
      rw [sum_range_succ']
      rw [if_pos rfl, sub_zero]
      have : ∀ i ∈ range n, (Gb q n (i + 1) - if i + 1 = 0 then 0 else Gb q n (i + 1 - 1)) =
          Gb q n (i + 1) - Gb q n i := fun i _ => by
        rw [if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel]
      rw [sum_congr rfl this, sum_range_sub (fun i => Gb q n i)]; ring
    rw [htel]
    linear_combination stepb_top hq n

end FourSquaresCaps.Jacobi
