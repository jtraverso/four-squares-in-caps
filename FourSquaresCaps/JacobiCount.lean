/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.JacobiSeries
public import FourSquaresCaps.Covering

/-!
# Jacobi's four-square theorem for odd `N`

From `dvd_theta4_sub` (identity (3) of Andrews–Ekhad–Zeilberger modulo `X^{N+1}`) we read off the
coefficient of `X^N`, obtaining for odd `N`
`#{x ∈ ℤ^4 : ∑ x_i^2 = N} = 8 ∑_{d ∣ N} N/d = 8 σ(N)`, hence `≥ 8N`.
-/

@[expose] public section

namespace FourSquaresCaps.Jacobi

open Finset PowerSeries

local notation "R" => PowerSeries ℚ

noncomputable section

/-! ### Coefficients of `(-1)^k X^k/(1+X^k)^2` -/

/-- The coefficient function of `Ek k`. -/
def cE (k N : ℕ) : ℚ := if k ∣ N then (-1) ^ (k + N / k + 1) * ((N / k : ℕ) : ℚ) else 0

theorem cE_mul (k j : ℕ) (hk : 1 ≤ k) : cE k (k * j) = (-1) ^ (k + j + 1) * (j : ℚ) := by
  unfold cE
  rw [if_pos (dvd_mul_right k j), Nat.mul_div_cancel_left j (by omega)]

theorem cE_not_dvd {k N : ℕ} (h : ¬ k ∣ N) : cE k N = 0 := by
  unfold cE; rw [if_neg h]

theorem cE_rec (k N : ℕ) (hk : 1 ≤ k) :
    cE k N + 2 * (if k ≤ N then cE k (N - k) else 0) + (if 2 * k ≤ N then cE k (N - 2 * k) else 0) =
      (-1) ^ k * (if N = k then 1 else 0) := by
  by_cases hd : k ∣ N
  · obtain ⟨j, rfl⟩ := hd
    rcases j with _ | _ | j
    · rw [mul_zero, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      unfold cE; simp
    · simp only [zero_add, mul_one]
      simp only [le_refl, ite_true, mul_one, Nat.sub_self]
      try rw [if_neg (show ¬ 2 * k ≤ k by omega), add_zero]
      have e0 : cE k 0 = 0 := by unfold cE; simp
      have e1 := cE_mul k 1 hk
      rw [mul_one] at e1
      rw [e0, e1]; push_cast; ring
    · have h1 : k * (j + 1 + 1) - k = k * (j + 1) := by
        rw [show k * (j + 1 + 1) = k * (j + 1) + k by ring]; omega
      have h2 : k * (j + 1 + 1) - 2 * k = k * j := by
        rw [show k * (j + 1 + 1) = k * j + 2 * k by ring]; omega
      have hne : k * (j + 1 + 1) ≠ k := by
        intro h
        have : k * (j + 1 + 1) = k * 1 := by rw [h, mul_one]
        have := Nat.eq_of_mul_eq_mul_left (by omega) this
        omega
      rw [if_pos (by nlinarith), if_pos (by nlinarith), if_neg hne, h1, h2, cE_mul k _ hk,
        cE_mul k _ hk, cE_mul k _ hk]
      push_cast; ring
  · rw [cE_not_dvd hd]
    have hne : N ≠ k := by rintro rfl; exact hd dvd_rfl
    rw [if_neg hne]
    have e1 : (if k ≤ N then cE k (N - k) else 0) = 0 := by
      split_ifs with h
      · exact cE_not_dvd fun h' => hd (by
          have := Nat.dvd_add h' (dvd_refl k); rwa [Nat.sub_add_cancel h] at this)
      · rfl
    have e2 : (if 2 * k ≤ N then cE k (N - 2 * k) else 0) = 0 := by
      split_ifs with h
      · exact cE_not_dvd fun h' => hd (by
          have := Nat.dvd_add h' (dvd_mul_left k 2); rwa [Nat.sub_add_cancel h] at this)
      · rfl
    rw [e1, e2]; ring

theorem two_eq_C : (2 : R) = C (2 : ℚ) := by rw [map_ofNat]

theorem Ek_eq (k : ℕ) (hk : 1 ≤ k) : Ek k = PowerSeries.mk (cE k) := by
  have key : PowerSeries.mk (cE k) * (1 + X ^ k) ^ 2 = (-1) ^ k * X ^ k := by
    have e : PowerSeries.mk (cE k) * (1 + X ^ k) ^ 2 = PowerSeries.mk (cE k) +
        C (2 : ℚ) * (PowerSeries.mk (cE k) * X ^ k) + PowerSeries.mk (cE k) * X ^ (2 * k) := by
      rw [← two_eq_C, pow_mul]; ring
    rw [e]
    ext N
    have hneg : ((-1 : R) ^ k) = C ((-1 : ℚ) ^ k) := by simp
    rw [map_add, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mul_X_pow', hneg, coeff_C_mul,
      coeff_X_pow, coeff_mk]
    have := cE_rec k N hk
    split_ifs at this ⊢ <;> (try simp only [coeff_mk] at *) <;> linarith
  unfold Ek
  have hc := cc_one_add_sq k
  rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ hc, mul_one]

theorem coeff_Tp (n N : ℕ) (hN : 1 ≤ N) :
    coeff N (Tp n) = 8 * ∑ i ∈ range n, cE (i + 1) N := by
  unfold Tp
  rw [show (8 : R) = C (8 : ℚ) by rw [map_ofNat], map_add, coeff_C_mul, coeff_one, if_neg (by omega),
    zero_add, map_sum]
  congr 1
  exact sum_congr rfl fun i _ => by rw [Ek_eq _ (by omega), coeff_mk]

/-- For odd `N ≤ n`, the coefficient of `X^N` in `Tp n` is `-8 ∑_{d ∣ N} N/d`. -/
theorem coeff_Tp_odd (n N : ℕ) (hN : Odd N) (hNn : N ≤ n) :
    coeff N (Tp n) = -(8 * ∑ d ∈ N.divisors, ((N / d : ℕ) : ℚ)) := by
  have hN1 : 1 ≤ N := hN.pos
  rw [coeff_Tp n N hN1]
  have hsum : ∑ i ∈ range n, cE (i + 1) N = ∑ d ∈ Ico 1 (n + 1), cE d N := by
    rw [sum_Ico_eq_sum_range]; exact sum_congr rfl fun i _ => by rw [add_comm]
  have hsplit : ∑ d ∈ Ico 1 (n + 1), cE d N = ∑ d ∈ N.divisors, cE d N := by
    symm
    apply sum_subset
    · intro d hd
      rw [Nat.mem_divisors] at hd
      have := Nat.le_of_dvd (by omega) hd.1
      have := Nat.pos_of_dvd_of_pos hd.1 (by omega)
      rw [mem_Ico]; omega
    · intro d _ hd
      rw [Nat.mem_divisors, not_and_or, not_not] at hd
      rcases hd with hd | hd
      · exact cE_not_dvd hd
      · omega
  rw [hsum, hsplit, ← neg_mul, mul_comm (-8 : ℚ), mul_comm (8 : ℚ), sum_mul, sum_mul]
  refine sum_congr rfl fun d hd => ?_
  have hdN := Nat.dvd_of_mem_divisors hd
  unfold cE
  rw [if_pos hdN]
  have hdo : Odd d := hN.of_dvd_nat hdN
  have hqo : Odd (N / d) := hN.of_dvd_nat (Nat.div_dvd_of_dvd hdN)
  have : Odd (d + N / d + 1) := by
    obtain ⟨a, ha⟩ := hdo; obtain ⟨b, hb⟩ := hqo; exact ⟨a + b + 1, by omega⟩
  rw [this.neg_one_pow]; ring

/-! ### The theta side -/

theorem sum_Icc_natAbs {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∀ n : ℕ, ∑ k ∈ Icc (-(n : ℤ)) n, g k.natAbs = g 0 + 2 • ∑ i ∈ range n, g (i + 1)
  | 0 => by simp
  | n + 1 => by
    have hI : Icc (-((n + 1 : ℕ) : ℤ)) (n + 1 : ℕ) =
        insert (-((n : ℤ) + 1)) (insert ((n : ℤ) + 1) (Icc (-(n : ℤ)) n)) := by
      ext x; simp only [mem_Icc, mem_insert]; push_cast; omega
    rw [hI, sum_insert (by simp only [mem_insert, mem_Icc]; omega),
      sum_insert (by simp only [mem_Icc]; omega), sum_Icc_natAbs g n, sum_range_succ]
    have h1 : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    have h2 : ((n : ℤ) + 1).natAbs = n + 1 := by omega
    rw [h1, h2, smul_add, two_nsmul (g (n + 1))]
    abel

/-- The summand of the theta series. -/
def gθ (a : ℕ) : R := (-1) ^ a * X ^ (a ^ 2)

theorem thetaP_eq_sum (n : ℕ) : thetaP n = ∑ k ∈ Icc (-(n : ℤ)) n, gθ k.natAbs := by
  rw [sum_Icc_natAbs gθ n, thetaP, nsmul_eq_mul]
  simp [gθ]

theorem neg_one_pow_sq (a : ℕ) : (-1 : ℚ) ^ (a ^ 2) = (-1) ^ a := by
  rcases Nat.even_or_odd a with h | h
  · rw [h.neg_one_pow, (Nat.even_pow.mpr ⟨h, two_ne_zero⟩).neg_one_pow]
  · rw [h.neg_one_pow, (h.pow (n := 2)).neg_one_pow]

/-- The box of side `n`. -/
def box (n : ℕ) : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Icc (-(n : ℤ)) n

theorem coeff_thetaP_four (n N : ℕ) :
    coeff N (thetaP n ^ 4) =
      (-1 : ℚ) ^ N * (((box n).filter (fun x => ∑ i, (x i).natAbs ^ 2 = N)).card : ℚ) := by
  rw [thetaP_eq_sum, ← Fin.prod_const, prod_univ_sum, map_sum]
  have hterm : ∀ x ∈ box n, coeff N (∏ i : Fin 4, gθ (x i).natAbs) =
      if ∑ i, (x i).natAbs ^ 2 = N then (-1 : ℚ) ^ N else 0 := by
    intro x _
    have : ∏ i : Fin 4, gθ (x i).natAbs =
        C ((-1 : ℚ) ^ (∑ i, (x i).natAbs)) * X ^ (∑ i, (x i).natAbs ^ 2) := by
      unfold gθ
      rw [prod_mul_distrib, prod_pow_eq_pow_sum, prod_pow_eq_pow_sum]
      simp
    rw [this, coeff_C_mul, coeff_X_pow]
    by_cases h : ∑ i, (x i).natAbs ^ 2 = N
    · rw [if_pos h.symm, if_pos h, mul_one, ← h, ← prod_pow_eq_pow_sum, ← prod_pow_eq_pow_sum]
      exact prod_congr rfl fun i _ => (neg_one_pow_sq _).symm
    · rw [if_neg (Ne.symm h), if_neg h, mul_zero]
  unfold box at hterm
  rw [sum_congr rfl hterm, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_comm]
  rfl

theorem filter_box_eq_reps (n N : ℕ) (hN : N ≤ n) :
    (box n).filter (fun x => ∑ i, (x i).natAbs ^ 2 = N) = reps N := by
  ext x
  have hcast : (∑ i, (x i).natAbs ^ 2 = N) ↔ ∑ i, x i ^ 2 = (N : ℤ) := by
    constructor
    · intro h
      have : ((∑ i, (x i).natAbs ^ 2 : ℕ) : ℤ) = N := by rw [h]
      push_cast at this
      simpa [Int.natAbs_sq] using this
    · intro h
      have : ((∑ i, (x i).natAbs ^ 2 : ℕ) : ℤ) = N := by
        push_cast; simpa [Int.natAbs_sq] using h
      exact_mod_cast this
  rw [mem_filter, hcast, mem_reps]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have hx : x ∈ reps N := (mem_reps N x).mpr h
    unfold reps at hx
    rw [mem_filter, Fintype.mem_piFinset] at hx
    unfold box
    rw [Fintype.mem_piFinset]
    intro i
    have := hx.1 i
    rw [mem_Icc] at this ⊢
    constructor <;> omega

/-! ### Jacobi's theorem for odd `N` -/

theorem reps_card_odd (N : ℕ) (hN : Odd N) :
    ((reps N).card : ℚ) = 8 * ∑ d ∈ N.divisors, ((N / d : ℕ) : ℚ) := by
  have hdvd := dvd_theta4_sub N
  rw [X_pow_dvd_iff] at hdvd
  have h := hdvd N (by omega)
  rw [map_sub, sub_eq_zero, coeff_thetaP_four, coeff_Tp_odd N N hN le_rfl,
    filter_box_eq_reps N N le_rfl, hN.neg_one_pow] at h
  linarith

theorem reps_card_ge (N : ℕ) (hN : Odd N) : 8 * (N : ℚ) ≤ (reps N).card := by
  rw [reps_card_odd N hN]
  have h1 : (1 : ℕ) ∈ N.divisors := Nat.mem_divisors.mpr ⟨one_dvd N, by have := hN.pos; omega⟩
  have : ((N / 1 : ℕ) : ℚ) ≤ ∑ d ∈ N.divisors, ((N / d : ℕ) : ℚ) :=
    single_le_sum (f := fun d => ((N / d : ℕ) : ℚ)) (fun _ _ => by positivity) h1
  rw [Nat.div_one] at this
  linarith

end

end FourSquaresCaps.Jacobi

namespace FourSquaresCaps.Jacobi

/-- **Jacobi's four-square theorem for odd `N`**: `r₄(N) = 8 σ(N)`. -/
theorem card_sum_four_sq_odd (N : ℕ) (hN : Odd N) :
    Nat.card {x : Fin 4 → ℤ // ∑ i, x i ^ 2 = N} = 8 * ∑ d ∈ N.divisors, d := by
  have e : Nat.card {x : Fin 4 → ℤ // ∑ i, x i ^ 2 = N} = (reps N).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => (mem_reps N x).symm)
  rw [e]
  have h := reps_card_odd N hN
  have hs : ∑ d ∈ N.divisors, ((N / d : ℕ) : ℚ) = ((∑ d ∈ N.divisors, d : ℕ) : ℚ) := by
    have h0 : ∑ d ∈ N.divisors, N / d = ∑ d ∈ N.divisors, d := Nat.sum_div_divisors N id
    rw [← h0, Nat.cast_sum]
  rw [hs] at h
  exact_mod_cast h

end FourSquaresCaps.Jacobi
