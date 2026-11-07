/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.Decomp
public import FourSquaresCaps.ArithSums
public import FourSquaresCaps.DivisorBound

/-!
# Averaging Weil's saving over the moduli

`sum_decomp_le`: if `g q` is the squarefree part `q₁` of a decomposition `GoodDecomp M q q₀ q₁`, then
`∑_{q ≤ Y} 2^{ω(q₁)}/√q₁ ≤ 2√Y (1 + log Y) · σ_{-1/2}(M) · ∑_{a ≤ Y} σ_{-1/2}(a)/a`.
The proof writes `q₀ = a² u b` with `u ∣ M`, `b ∣ a`.
-/

@[expose] public section

namespace FourSquaresCaps

open Finset Real

theorem two_pow_card_primeFactors_le (n : ℕ) (hn : n ≠ 0) :
    (2 : ℝ) ^ n.primeFactors.card ≤ n.divisors.card := by
  have : (n.primeFactors.powerset).card ≤ n.divisors.card := by
    refine card_le_card_of_injOn (fun S => ∏ p ∈ S, p) (fun S hS => ?_) ?_
    · rw [mem_coe, mem_powerset] at hS
      rw [mem_coe, Nat.mem_divisors]
      refine ⟨?_, hn⟩
      calc ∏ p ∈ S, p ∣ ∏ p ∈ n.primeFactors, p := prod_dvd_prod_of_subset _ _ _ hS
        _ ∣ n := Nat.prod_primeFactors_dvd n
    · intro S hS T hT hST
      rw [mem_coe, mem_powerset] at hS hT
      have hS' : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hS hp)
      have hT' : ∀ p ∈ T, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hT hp)
      simp only at hST
      rw [← Nat.primeFactors_prod hS', ← Nat.primeFactors_prod hT', hST]
  rw [card_powerset] at this
  exact_mod_cast this

/-- The parametrization of `q₀`. -/
theorem exists_tuple {M q q₀ q₁ : ℕ} (hd : GoodDecomp M q q₀ q₁) (hq : q ≠ 0) :
    ∃ u a b : ℕ, u ∣ M ∧ b ∣ a ∧ 0 < a ∧ q₀ = a ^ 2 * u * b := by
  obtain ⟨hq01, -, -, -, hgood⟩ := hd
  have hq0 : q₀ ≠ 0 := fun h => hq (by rw [hq01, h, zero_mul])
  obtain ⟨a, t, hat, hsq⟩ := exists_sq_mul_squarefree q₀
  have ha : a ≠ 0 := fun h => hq0 (by rw [← hat, h]; simp)
  set u := Nat.gcd t M with hu
  have hut : u ∣ t := Nat.gcd_dvd_left t M
  set b := t / u with hb
  have htub : t = u * b := (Nat.mul_div_cancel' hut).symm
  refine ⟨u, a, b, Nat.gcd_dvd_right t M, ?_, Nat.pos_of_ne_zero ha, ?_⟩
  · -- every prime of `b` divides `a`
    have hbsq : Squarefree b := hsq.squarefree_of_dvd ⟨u, by rw [htub, mul_comm]⟩
    rw [← Nat.prod_primeFactors_of_squarefree hbsq]
    refine prod_primes_dvd a (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpb := Nat.dvd_of_mem_primeFactors hp
    have hpt : p ∣ t := htub ▸ dvd_mul_of_dvd_right hpb u
    have hpM : ¬ p ∣ M := by
      intro hpM
      have hpu : p ∣ u := Nat.dvd_gcd hpt hpM
      have : p * p ∣ t := htub ▸ Nat.mul_dvd_mul hpu hpb
      exact hpp.one_lt.ne' (Nat.isUnit_iff.mp (hsq p this))
    have hpq0 : p ∣ q₀ := hat ▸ dvd_mul_of_dvd_right hpt _
    rcases hgood p hpp hpq0 with h | h
    · exact absurd h hpM
    · by_contra hpa
      have hcop : (p ^ 2).Coprime (a ^ 2) :=
        Nat.Coprime.pow 2 2 ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hpa)
      have : p ^ 2 ∣ t := hcop.dvd_of_dvd_mul_left (hat ▸ h)
      rw [sq] at this
      exact hpp.one_lt.ne' (Nat.isUnit_iff.mp (hsq p this))
  · rw [← hat, htub]; ring

/-- The inner sum over `n`: `∑_{n ≤ Y, k n ≤ Y} τ(n)/√n ≤ 2 √Y/√k (1 + log Y)`. -/
theorem sum_inner_le (Y k : ℕ) (hk : 0 < k) :
    ∑ n ∈ Icc 1 Y, (if k * n ≤ Y then (n.divisors.card : ℝ) / Real.sqrt n else 0) ≤
      2 * (Real.sqrt Y / Real.sqrt k) * (1 + Real.log Y) := by
  rw [← sum_filter]
  have hset : (Icc 1 Y).filter (fun n => k * n ≤ Y) = Icc 1 (Y / k) := by
    ext n
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, (Nat.le_div_iff_mul_le hk).mpr (by linarith)⟩
    · rintro ⟨h1, h2⟩
      have := (Nat.le_div_iff_mul_le hk).mp h2
      exact ⟨⟨h1, le_trans (Nat.le_mul_of_pos_left n hk) (by linarith)⟩, by linarith⟩
  rw [hset]
  refine (sum_card_divisors_div_sqrt_le (Y / k)).trans ?_
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : Real.sqrt (Y / k : ℕ) ≤ Real.sqrt Y / Real.sqrt k := by
    rw [← Real.sqrt_div' _ hk'.le]; exact Real.sqrt_le_sqrt Nat.cast_div_le
  have h2 : 1 + Real.log (Y / k : ℕ) ≤ 1 + Real.log Y := by
    rcases Nat.eq_zero_or_pos (Y / k) with h | h
    · rw [h, Nat.cast_zero, Real.log_zero]
      have : 0 ≤ Real.log Y := Real.log_natCast_nonneg Y
      linarith
    · have : ((Y / k : ℕ) : ℝ) ≤ Y := by exact_mod_cast Nat.div_le_self Y k
      have := Real.log_le_log (by exact_mod_cast h) this
      linarith
  have h3 : 0 ≤ 1 + Real.log (Y / k : ℕ) := by
    have := Real.log_natCast_nonneg (Y / k); linarith
  calc 2 * Real.sqrt (Y / k : ℕ) * (1 + Real.log (Y / k : ℕ))
      ≤ 2 * (Real.sqrt Y / Real.sqrt k) * (1 + Real.log Y) := by gcongr

/-- **Averaged Weil saving.** -/
theorem sum_decomp_le (M Y : ℕ) (hM : M ≠ 0) (g : ℕ → ℕ)
    (hg : ∀ q, q ≠ 0 → ∃ q₀, GoodDecomp M q q₀ (g q)) :
    ∑ q ∈ Icc 1 Y, (2 : ℝ) ^ (g q).primeFactors.card / Real.sqrt (g q) ≤
      2 * Real.sqrt Y * (1 + Real.log Y) * sigmaHalf M *
        ∑ a ∈ Icc 1 Y, sigmaHalf a / a := by
  classical
  have hex : ∀ q ∈ Icc 1 Y, ∃ t : ℕ × ℕ × ℕ, t.1 ∣ M ∧ t.2.2 ∣ t.2.1 ∧ 0 < t.2.1 ∧
      q = t.2.1 ^ 2 * t.1 * t.2.2 * g q := by
    intro q hq
    have hq0 : q ≠ 0 := by simp only [mem_Icc] at hq; omega
    obtain ⟨q₀, hd⟩ := hg q hq0
    obtain ⟨u, a, b, hu, hb, ha, h0⟩ := exists_tuple hd hq0
    exact ⟨(u, a, b), hu, hb, ha, hd.1.trans (by rw [h0])⟩
  choose! T hT using hex
  set F : ℕ → ℝ := fun n => (n.divisors.card : ℝ) / Real.sqrt n with hF
  have hF0 : ∀ n, 0 ≤ F n := fun n => by simp only [hF]; positivity
  -- pointwise: `2^ω ≤ τ`
  have hpt : ∀ q ∈ Icc 1 Y, (2 : ℝ) ^ (g q).primeFactors.card / Real.sqrt (g q) ≤ F (g q) := by
    intro q hq
    have hgq : g q ≠ 0 := by
      intro h0
      have := (hT q hq).2.2.2
      rw [h0, mul_zero] at this
      simp only [mem_Icc] at hq; omega
    exact div_le_div_of_nonneg_right (two_pow_card_primeFactors_le _ hgq) (Real.sqrt_nonneg _)
  refine (sum_le_sum hpt).trans ?_
  set S := (M.divisors ×ˢ (Icc 1 Y ×ˢ (Icc 1 Y ×ˢ Icc 1 Y))).filter
    (fun t : ℕ × ℕ × ℕ × ℕ => t.2.2.1 ∣ t.2.1 ∧ t.2.1 ^ 2 * t.1 * t.2.2.1 * t.2.2.2 ≤ Y) with hS
  have hinj : ∑ q ∈ Icc 1 Y, F (g q) ≤ ∑ t ∈ S, F t.2.2.2 := by
    refine sum_le_sum_of_injOn (fun q => ((T q).1, (T q).2.1, (T q).2.2, g q)) ?_ ?_
      (fun q _ => le_rfl) (fun t _ _ => hF0 _)
    · intro q hq q' hq' h
      simp only [Prod.mk.injEq] at h
      rw [(hT q hq).2.2.2, (hT q' hq').2.2.2, h.1, h.2.1, h.2.2.1, h.2.2.2]
    · intro t ht
      simp only [mem_image] at ht
      obtain ⟨q, hq, rfl⟩ := ht
      obtain ⟨hu, hb, ha, hqe⟩ := hT q hq
      have hqY : q ≤ Y := (mem_Icc.mp hq).2
      have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
      have hpos : 0 < (T q).2.1 ^ 2 * (T q).1 * (T q).2.2 * g q := by omega
      have hu0 : 0 < (T q).1 := by
        rcases Nat.eq_zero_or_pos (T q).1 with h | h
        · rw [h] at hpos; simp at hpos
        · exact h
      have hb0 : 0 < (T q).2.2 := by
        rcases Nat.eq_zero_or_pos (T q).2.2 with h | h
        · rw [h] at hpos; simp at hpos
        · exact h
      have hg0 : 0 < g q := by
        rcases Nat.eq_zero_or_pos (g q) with h | h
        · rw [h] at hpos; simp at hpos
        · exact h
      have hle1 : (T q).2.1 ≤ q := by
        calc (T q).2.1 ≤ (T q).2.1 ^ 2 := Nat.le_self_pow (by norm_num) _
          _ ≤ (T q).2.1 ^ 2 * (T q).1 := Nat.le_mul_of_pos_right _ hu0
          _ ≤ (T q).2.1 ^ 2 * (T q).1 * (T q).2.2 := Nat.le_mul_of_pos_right _ hb0
          _ ≤ (T q).2.1 ^ 2 * (T q).1 * (T q).2.2 * g q := Nat.le_mul_of_pos_right _ hg0
          _ = q := hqe.symm
      have hle2 : (T q).2.2 ≤ q := by
        calc (T q).2.2 ≤ (T q).2.1 ^ 2 * (T q).1 * (T q).2.2 :=
              Nat.le_mul_of_pos_left _ (Nat.mul_pos (by positivity) hu0)
          _ ≤ (T q).2.1 ^ 2 * (T q).1 * (T q).2.2 * g q := Nat.le_mul_of_pos_right _ hg0
          _ = q := hqe.symm
      have hle3 : g q ≤ q := by
        calc g q ≤ (T q).2.1 ^ 2 * (T q).1 * (T q).2.2 * g q :=
              Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos (by positivity) hu0) hb0)
          _ = q := hqe.symm
      simp only [hS, mem_filter, mem_product, Nat.mem_divisors, mem_Icc]
      refine ⟨⟨⟨hu, hM⟩, ⟨ha, by omega⟩, ⟨hb0, by omega⟩, ⟨hg0, by omega⟩⟩, hb, ?_⟩
      rw [← hqe]; exact hqY
  refine hinj.trans ?_
  set K := 2 * Real.sqrt Y * (1 + Real.log Y) with hK
  have hK0 : 0 ≤ K := by
    have := Real.log_natCast_nonneg Y; positivity
  have key : ∑ t ∈ S, F t.2.2.2 ≤ ∑ u ∈ M.divisors, ∑ a ∈ Icc 1 Y,
      K * ((Real.sqrt u)⁻¹ * (sigmaHalf a / a)) := by
    rw [hS, sum_filter, sum_product]
    refine sum_le_sum fun u hu => ?_
    have hu0 : 0 < u := Nat.pos_of_mem_divisors hu
    rw [sum_product]
    refine sum_le_sum fun a ha => ?_
    have ha0 : 0 < a := (mem_Icc.mp ha).1
    have haY : a ≤ Y := (mem_Icc.mp ha).2
    rw [sum_product]
    have hu' : (0 : ℝ) < u := by exact_mod_cast hu0
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha0
    have hinner : ∀ b ∈ Icc 1 Y,
        (∑ n ∈ Icc 1 Y, if b ∣ a ∧ a ^ 2 * u * b * n ≤ Y then F n else 0) ≤
        if b ∣ a then K * ((a : ℝ)⁻¹ * (Real.sqrt u)⁻¹ * (Real.sqrt b)⁻¹) else 0 := by
      intro b hb
      have hb0 : 0 < b := (mem_Icc.mp hb).1
      have hb' : (0 : ℝ) < b := by exact_mod_cast hb0
      split_ifs with hba
      · simp only [hba, true_and]
        have hk : 0 < a ^ 2 * u * b := by positivity
        refine (sum_inner_le Y (a ^ 2 * u * b) hk).trans (le_of_eq ?_)
        have : Real.sqrt ((a ^ 2 * u * b : ℕ) : ℝ) = a * Real.sqrt u * Real.sqrt b := by
          push_cast
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq ha'.le]
        rw [this, hK]
        field_simp
      · simp [hba]
    refine (sum_le_sum hinner).trans (le_of_eq ?_)
    rw [← sum_filter]
    have hdiv : (Icc 1 Y).filter (· ∣ a) = a.divisors := by
      ext b
      simp only [mem_filter, mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨_, hb⟩; exact ⟨hb, ha0.ne'⟩
      · rintro ⟨hb, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hb ha0, le_trans (Nat.le_of_dvd ha0 hb) haY⟩, hb⟩
    rw [hdiv]
    unfold sigmaHalf
    rw [div_eq_mul_inv, sum_mul, mul_sum, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    ring
  refine key.trans (le_of_eq ?_)
  unfold sigmaHalf
  rw [mul_assoc, sum_mul_sum, mul_sum]
  refine sum_congr rfl fun u _ => ?_
  rw [mul_sum]

/-- `∑_{a ≤ N} σ_{-1/2}(a)/a ≤ (1 + log N)²`. -/
theorem sum_sigmaHalf_div_le (N : ℕ) :
    ∑ a ∈ Icc 1 N, sigmaHalf a / a ≤ (1 + Real.log N) ^ 2 := by
  classical
  have h1 : ∑ a ∈ Icc 1 N, sigmaHalf a / a =
      ∑ a ∈ Icc 1 N, ∑ d ∈ a.divisors, (Real.sqrt d)⁻¹ * (a : ℝ)⁻¹ := by
    refine sum_congr rfl fun a _ => ?_
    unfold sigmaHalf; rw [div_eq_mul_inv, sum_mul]
  rw [h1]
  have h2 : ∑ a ∈ Icc 1 N, ∑ d ∈ a.divisors, (Real.sqrt d)⁻¹ * (a : ℝ)⁻¹ ≤
      ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 (N / d), (d : ℝ)⁻¹ * (e : ℝ)⁻¹ := by
    rw [sum_sigma', sum_sigma']
    refine sum_le_sum_of_injOn (fun x => (⟨x.2, x.1 / x.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_
      (fun x hx => ?_) (fun _ _ _ => by positivity)
    · intro x hx y hy hxy
      simp only [Sigma.mk.injEq] at hxy
      obtain ⟨h1, h2⟩ := hxy
      simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_Icc, Nat.mem_divisors] at hx hy
      have e1 := Nat.div_mul_cancel hx.2.1
      have e2 := Nat.div_mul_cancel hy.2.1
      have : x.1 = y.1 := by
        rw [← e1, ← e2]
        have h2' : x.1 / x.2 = y.1 / y.2 := by simpa using h2
        rw [h2', show x.2 = y.2 from h1]
      exact Sigma.ext this (heq_of_eq h1)
    · intro z hz
      simp only [mem_image, mem_sigma, mem_Icc, Nat.mem_divisors] at hz ⊢
      obtain ⟨x, ⟨⟨h1n, hnN⟩, hd, -⟩, rfl⟩ := hz
      have hd0 : 0 < x.2 := Nat.pos_of_dvd_of_pos hd (by omega)
      have hle : x.2 ≤ x.1 := Nat.le_of_dvd (by omega) hd
      refine ⟨⟨hd0, le_trans hle hnN⟩, ?_, ?_⟩
      · exact Nat.div_pos hle hd0
      · exact Nat.div_le_div_right hnN
    · simp only [mem_sigma, mem_Icc, Nat.mem_divisors] at hx
      obtain ⟨⟨h1n, -⟩, hd, -⟩ := hx
      have hd0 : 0 < x.2 := Nat.pos_of_dvd_of_pos hd (by omega)
      have hd' : (1 : ℝ) ≤ x.2 := by exact_mod_cast hd0
      have he := Nat.div_mul_cancel hd
      have hx1 : ((x.1 : ℕ) : ℝ) = (x.1 / x.2 : ℕ) * x.2 := by exact_mod_cast he.symm
      simp only
      rw [hx1, mul_inv]
      have hs : (Real.sqrt x.2)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (by rw [Real.one_le_sqrt]; exact hd')
      have hp : 0 ≤ ((x.1 / x.2 : ℕ) : ℝ)⁻¹ * (x.2 : ℝ)⁻¹ := by positivity
      calc (Real.sqrt x.2)⁻¹ * (((x.1 / x.2 : ℕ) : ℝ)⁻¹ * (x.2 : ℝ)⁻¹)
          ≤ 1 * (((x.1 / x.2 : ℕ) : ℝ)⁻¹ * (x.2 : ℝ)⁻¹) := mul_le_mul_of_nonneg_right hs hp
        _ = (x.2 : ℝ)⁻¹ * ((x.1 / x.2 : ℕ) : ℝ)⁻¹ := by ring
  refine h2.trans ?_
  calc ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 (N / d), (d : ℝ)⁻¹ * (e : ℝ)⁻¹
      ≤ ∑ d ∈ Icc 1 N, (d : ℝ)⁻¹ * (1 + Real.log N) := by
        refine sum_le_sum fun d hd => ?_
        rw [← mul_sum]
        refine mul_le_mul_of_nonneg_left ((sum_harmonic_le _).trans ?_) (by positivity)
        rcases Nat.eq_zero_or_pos (N / d) with h | h
        · rw [h, Nat.cast_zero, Real.log_zero]
          have := Real.log_natCast_nonneg N; linarith
        · have : ((N / d : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N d
          have := Real.log_le_log (by exact_mod_cast h) this
          linarith
    _ = (∑ d ∈ Icc 1 N, (d : ℝ)⁻¹) * (1 + Real.log N) := by rw [sum_mul]
    _ ≤ (1 + Real.log N) * (1 + Real.log N) := by
        have := Real.log_natCast_nonneg N
        exact mul_le_mul_of_nonneg_right (sum_harmonic_le N) (by linarith)
    _ = (1 + Real.log N) ^ 2 := by ring

end FourSquaresCaps
