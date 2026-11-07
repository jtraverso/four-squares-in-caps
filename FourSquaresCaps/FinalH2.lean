/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.Covering
public import FourSquaresCaps.Bumps
public import FourSquaresCaps.Statement

/-!
# Four squares in caps, assuming many representations

`fourSquaresDense_of_reps`: if `r₄(m) ≥ c m` for all large odd `m` (true with `c = 8` by Jacobi's
four-square theorem), then `FourSquaresDense`.
-/

@[expose] public section

namespace FourSquaresCaps

open Finset Real

/-- `(1 + log y)⁴ ≤ 65⁴ y^{1/16}` for `y ≥ 1`. -/
theorem one_add_log_pow_le (y : ℝ) (hy : 1 ≤ y) :
    (1 + Real.log y) ^ 4 ≤ 65 ^ 4 * y ^ (1 / 16 : ℝ) := by
  have hy0 : 0 < y := by linarith
  have h1 : Real.log y ≤ y ^ (1 / 64 : ℝ) / (1 / 64) := Real.log_le_rpow_div hy0.le (by norm_num)
  have h2 : 1 ≤ y ^ (1 / 64 : ℝ) := Real.one_le_rpow hy (by norm_num)
  have h3 : 1 + Real.log y ≤ 65 * y ^ (1 / 64 : ℝ) := by
    have : y ^ (1 / 64 : ℝ) / (1 / 64) = 64 * y ^ (1 / 64 : ℝ) := by field_simp
    linarith
  have hl : 0 ≤ 1 + Real.log y := by have := Real.log_nonneg hy; linarith
  calc (1 + Real.log y) ^ 4 ≤ (65 * y ^ (1 / 64 : ℝ)) ^ 4 := pow_le_pow_left₀ hl h3 4
    _ = 65 ^ 4 * y ^ (1 / 16 : ℝ) := by
        rw [mul_pow, show (y ^ (1 / 64 : ℝ)) ^ 4 = y ^ (1 / 16 : ℝ) by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num]

/-- **The asymptotic comparison.** `K m^{7/8} (1 + log 4m)⁴ < c m` for large `m`. -/
theorem eventually_lt (K c : ℝ) (hc : 0 < c) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      K * (m : ℝ) ^ (7 / 8 : ℝ) * (1 + Real.log (4 * m)) ^ 4 < c * m := by
  set K' := max K 0 * 65 ^ 4 * 4 ^ (1 / 16 : ℝ) / c with hK'
  refine ⟨⌈K' ^ (16 : ℝ)⌉₊ + 1, fun m hm => ?_⟩
  have hm1 : (1 : ℝ) ≤ m := by
    have : 1 ≤ m := by omega
    exact_mod_cast this
  have hm0 : (0 : ℝ) < m := by linarith
  have hlog := one_add_log_pow_le (4 * m) (by linarith)
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have hK'0 : 0 ≤ K' := by rw [hK']; positivity
  -- `m^{1/16} > K'`
  have hmK : K' < (m : ℝ) ^ (1 / 16 : ℝ) := by
    have h1 : K' ^ (16 : ℝ) < m := by
      have := Nat.lt_of_ceil_lt (show ⌈K' ^ (16 : ℝ)⌉₊ < m by omega)
      exact this
    calc K' = (K' ^ (16 : ℝ)) ^ (1 / 16 : ℝ) := by
          rw [← Real.rpow_mul hK'0]; norm_num
      _ < (m : ℝ) ^ (1 / 16 : ℝ) :=
          Real.rpow_lt_rpow (by positivity) h1 (by norm_num)
  have e1 : (4 * (m : ℝ)) ^ (1 / 16 : ℝ) = 4 ^ (1 / 16 : ℝ) * (m : ℝ) ^ (1 / 16 : ℝ) :=
    Real.mul_rpow (by norm_num) hm0.le
  have e2 : (m : ℝ) ^ (7 / 8 : ℝ) * (m : ℝ) ^ (1 / 16 : ℝ) * (m : ℝ) ^ (1 / 16 : ℝ) = m := by
    rw [← Real.rpow_add hm0, ← Real.rpow_add hm0]; norm_num
  calc K * (m : ℝ) ^ (7 / 8 : ℝ) * (1 + Real.log (4 * m)) ^ 4
      ≤ max K 0 * (m : ℝ) ^ (7 / 8 : ℝ) * (65 ^ 4 * (4 * m) ^ (1 / 16 : ℝ)) := by
        gcongr
        exact le_max_left _ _
    _ = (K' * c) * ((m : ℝ) ^ (7 / 8 : ℝ) * (m : ℝ) ^ (1 / 16 : ℝ)) := by
        rw [e1, hK']; field_simp
    _ < ((m : ℝ) ^ (1 / 16 : ℝ) * c) * ((m : ℝ) ^ (7 / 8 : ℝ) * (m : ℝ) ^ (1 / 16 : ℝ)) := by
        gcongr
    _ = c * ((m : ℝ) ^ (7 / 8 : ℝ) * (m : ℝ) ^ (1 / 16 : ℝ) * (m : ℝ) ^ (1 / 16 : ℝ)) := by ring
    _ = c * m := by rw [e2]

theorem errXi_nonneg (X δ' : ℝ) (hX0 : 0 < X) (hδ0 : 0 < δ') (hlog : 0 ≤ Real.log (4 * X ^ 2)) :
    0 ≤ errXi X (4 * X ^ 2) (δ' * X) X := by
  unfold errXi
  refine add_nonneg (add_nonneg (by positivity) ?_) ?_
  · exact div_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
  · exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity))
      hX0.le

theorem errXi_le (m : ℕ) (hm : 1 ≤ m) (δ' : ℝ) (hδ0 : 0 < δ') (hδ1 : δ' ≤ 1) :
    errXi (Real.sqrt m) (4 * Real.sqrt m ^ 2) (δ' * Real.sqrt m) (Real.sqrt m) ≤
      551000 * Real.sqrt m * (1 + Real.log (4 * m)) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set X := Real.sqrt m with hX
  have hX0 : 0 < X := Real.sqrt_pos.mpr (by linarith)
  have hX2 : X ^ 2 = m := Real.sq_sqrt (by linarith)
  rw [← hX2]
  have hlog : 0 ≤ Real.log (4 * X ^ 2) := Real.log_nonneg (by rw [hX2]; linarith)
  unfold errXi
  have h1 : 8000 * (12 * (4 * X ^ 2) / X + 4 * X) = 416000 * X := by
    field_simp; ring
  have h2 : 32000 * (δ' * X) ^ 4 * (4 + 2 * Real.log (4 * X ^ 2)) / X ^ 3 ≤
      32000 * X * (4 + 2 * Real.log (4 * X ^ 2)) := by
    have hd4 : δ' ^ 4 ≤ 1 := pow_le_one₀ hδ0.le hδ1
    have e : 32000 * (δ' * X) ^ 4 * (4 + 2 * Real.log (4 * X ^ 2)) / X ^ 3 =
        32000 * X * (4 + 2 * Real.log (4 * X ^ 2)) * δ' ^ 4 := by field_simp
    rw [e]
    have : 0 ≤ 32000 * X * (4 + 2 * Real.log (4 * X ^ 2)) := by
      apply mul_nonneg (by positivity); linarith
    nlinarith
  have h3 : 2048 * (3 + 2 * Real.log (4 * X ^ 2)) * X ^ 2 / X =
      2048 * X * (3 + 2 * Real.log (4 * X ^ 2)) := by
    field_simp
  rw [h1, h3]
  nlinarith [h2, mul_nonneg hX0.le hlog]

theorem eps_le (CE : ℝ) (hCE : 0 ≤ CE) (m : ℕ) (hm : 1 ≤ m) (δ' : ℝ) (hδ0 : 0 < δ')
    (hδ1 : δ' ≤ 1) (g : ℕ → ℕ)
    (hg : ∀ q, q ≠ 0 → ∃ q₀, GoodDecomp (2 * (m : ℤ).natAbs) q q₀ (g q)) :
    2 * (4 * CE * errXi (Real.sqrt m) (4 * Real.sqrt m ^ 2) (δ' * Real.sqrt m) (Real.sqrt m) *
      ∑ q ∈ Icc 1 ⌊2 * Real.sqrt m⌋₊, (2 : ℝ) ^ (g q).primeFactors.card / Real.sqrt (g q)) ≤
    (8 * 551000 * 2 * Real.sqrt 2 * 4 ^ 17 * 2 ^ (1 / 8 : ℝ) * CE) *
      (m : ℝ) ^ (7 / 8 : ℝ) * (1 + Real.log (4 * m)) ^ 4 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  set X := Real.sqrt m with hX
  have hX0 : 0 < X := Real.sqrt_pos.mpr hm0
  have hX2 : X ^ 2 = m := Real.sq_sqrt hm0.le
  have hlog : 0 ≤ Real.log (4 * m) := Real.log_nonneg (by linarith)
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hS := sum_w_le (m : ℤ) hmz ⌊2 * X⌋₊ g hg
  set Y := ⌊2 * X⌋₊ with hY
  have hYle : (Y : ℝ) ≤ 2 * X := Nat.floor_le (by positivity)
  have hXm : X ≤ m := by
    rw [hX, Real.sqrt_le_left (by linarith)]; nlinarith
  have hsX : Real.sqrt X = (m : ℝ) ^ (1 / 4 : ℝ) := by
    rw [hX, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hm0.le]; norm_num
  have hsY : Real.sqrt Y ≤ Real.sqrt 2 * (m : ℝ) ^ (1 / 4 : ℝ) := by
    have : Real.sqrt Y ≤ Real.sqrt (2 * X) := Real.sqrt_le_sqrt hYle
    refine this.trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by norm_num), hsX]
  have hlY : 1 + Real.log Y ≤ 1 + Real.log (4 * m) := by
    rcases Nat.eq_zero_or_pos Y with h | h
    · rw [h, Nat.cast_zero, Real.log_zero]; linarith
    · have : (Y : ℝ) ≤ 4 * m := by linarith
      have := Real.log_le_log (by exact_mod_cast h) this
      linarith
  have hlY0 : 0 ≤ 1 + Real.log Y := by have := Real.log_natCast_nonneg Y; linarith
  have hnat : ((2 * (m : ℤ).natAbs : ℕ) : ℝ) = 2 * m := by push_cast; simp
  rw [hnat] at hS
  have h2m : (2 * (m : ℝ)) ^ (1 / 8 : ℝ) = 2 ^ (1 / 8 : ℝ) * (m : ℝ) ^ (1 / 8 : ℝ) :=
    Real.mul_rpow (by norm_num) hm0.le
  have hXi := errXi_le m hm δ' hδ0 hδ1
  rw [← hX] at hXi
  have hS' : ∑ q ∈ Icc 1 Y, (2 : ℝ) ^ (g q).primeFactors.card / Real.sqrt (g q) ≤
      2 * (Real.sqrt 2 * (m : ℝ) ^ (1 / 4 : ℝ)) * (1 + Real.log (4 * m)) ^ 3 *
        (4 ^ 17 * (2 ^ (1 / 8 : ℝ) * (m : ℝ) ^ (1 / 8 : ℝ))) := by
    refine hS.trans ?_
    rw [h2m]
    gcongr
  have hXrp : X = (m : ℝ) ^ (1 / 2 : ℝ) := by rw [hX, Real.sqrt_eq_rpow]
  have hexp : (m : ℝ) ^ (1 / 2 : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ) * (m : ℝ) ^ (1 / 8 : ℝ) =
      (m : ℝ) ^ (7 / 8 : ℝ) := by
    rw [← Real.rpow_add hm0, ← Real.rpow_add hm0]; norm_num
  have hΞ0 : 0 ≤ errXi X (4 * X ^ 2) (δ' * X) X :=
    errXi_nonneg X δ' hX0 hδ0 (Real.log_nonneg (by rw [hX2]; linarith))
  have hsum0 : 0 ≤ ∑ q ∈ Icc 1 Y, (2 : ℝ) ^ (g q).primeFactors.card / Real.sqrt (g q) :=
    sum_nonneg fun q _ => by positivity
  calc 2 * (4 * CE * errXi X (4 * X ^ 2) (δ' * X) X *
        ∑ q ∈ Icc 1 Y, (2 : ℝ) ^ (g q).primeFactors.card / Real.sqrt (g q))
      ≤ 2 * (4 * CE * (551000 * X * (1 + Real.log (4 * m))) *
        (2 * (Real.sqrt 2 * (m : ℝ) ^ (1 / 4 : ℝ)) * (1 + Real.log (4 * m)) ^ 3 *
          (4 ^ 17 * (2 ^ (1 / 8 : ℝ) * (m : ℝ) ^ (1 / 8 : ℝ))))) := by
        gcongr
    _ = (8 * 551000 * 2 * Real.sqrt 2 * 4 ^ 17 * 2 ^ (1 / 8 : ℝ) * CE) *
          ((m : ℝ) ^ (1 / 2 : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ) * (m : ℝ) ^ (1 / 8 : ℝ)) *
          (1 + Real.log (4 * m)) ^ 4 := by rw [hXrp]; ring
    _ = _ := by rw [hexp]

/-- The numerical choice of `δ'`: with `N = 150/δ₁²`, `δ' = δ₁/N`, `K = ⌈2/δ'⌉`,
`e^{−π N²} ≤ e^{−π} / (2 (2K+1)⁴)`. -/
theorem kappa_bound (δ₁ : ℝ) (h0 : 0 < δ₁) (h1 : δ₁ ≤ 1) :
    Real.exp (-π * (150 / δ₁ ^ 2) ^ 2) ≤
      Real.exp (-π) / (2 * (2 * ⌈2 / (δ₁ / (150 / δ₁ ^ 2))⌉₊ + 1 : ℝ) ^ 4) := by
  set N := 150 / δ₁ ^ 2 with hN
  have hN0 : 0 < N := by positivity
  have hd2 : δ₁ ^ 2 ≤ 1 := by nlinarith
  have hNbig : 150 ≤ N := by rw [hN, le_div_iff₀ (by positivity)]; nlinarith
  set δ' := δ₁ / N with hδ'
  have hδ'0 : 0 < δ' := by positivity
  set K := ⌈2 / δ'⌉₊ with hK
  have hKle : (K : ℝ) ≤ 2 / δ' + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hB : (2 * K + 1 : ℝ) ≤ 7 * N / δ₁ := by
    have e : 2 / δ' = 2 * N / δ₁ := by rw [hδ']; field_simp
    have hNd : 1 ≤ N / δ₁ := by
      rw [le_div_iff₀ h0]; nlinarith
    have hK' : (K : ℝ) ≤ 2 * N / δ₁ + 1 := by rw [← e]; exact hKle
    have e3 : 4 * N / δ₁ = 2 * (2 * N / δ₁) := by ring
    have : (2 * K + 1 : ℝ) ≤ 4 * N / δ₁ + 3 := by rw [e3]; linarith
    have e2 : 7 * N / δ₁ = 4 * N / δ₁ + 3 * (N / δ₁) := by ring
    rw [e2]; nlinarith
  have hB4 : (2 * K + 1 : ℝ) ^ 4 ≤ 2401 * N ^ 4 / δ₁ ^ 4 := by
    calc (2 * K + 1 : ℝ) ^ 4 ≤ (7 * N / δ₁) ^ 4 := pow_le_pow_left₀ (by positivity) hB 4
      _ = 2401 * N ^ 4 / δ₁ ^ 4 := by ring
  -- `N⁴/δ₁⁴ = N⁶/22500`
  have hNδ : N ^ 4 / δ₁ ^ 4 = N ^ 6 / 22500 := by
    have : δ₁ ^ 4 = 22500 / N ^ 2 := by rw [hN]; field_simp; ring
    rw [this]; field_simp
  -- `e^{π(N²−1)} ≥ π³ N⁶ / 48`
  have hpi : 3 < π := Real.pi_gt_three
  have hx : 0 ≤ π * (N ^ 2 - 1) := mul_nonneg pi_pos.le (by nlinarith)
  have hexp := Real.pow_div_factorial_le_exp _ hx 3
  have hfact : (Nat.factorial 3 : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hfact] at hexp
  have hN2 : N ^ 2 / 2 ≤ N ^ 2 - 1 := by nlinarith
  have hcube : (π * (N ^ 2 / 2)) ^ 3 ≤ (π * (N ^ 2 - 1)) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) 3
  have key : 2 * (2 * K + 1 : ℝ) ^ 4 ≤ Real.exp (π * (N ^ 2 - 1)) := by
    calc 2 * (2 * K + 1 : ℝ) ^ 4 ≤ 2 * (2401 * N ^ 4 / δ₁ ^ 4) := by gcongr
      _ = 4802 * N ^ 6 / 22500 := by
          rw [show 2 * (2401 * N ^ 4 / δ₁ ^ 4) = 4802 * (N ^ 4 / δ₁ ^ 4) by ring, hNδ]; ring
      _ ≤ (π * (N ^ 2 / 2)) ^ 3 / 6 := by
          have : (27 : ℝ) ≤ π ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) hpi.le 3]
          rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
          have : (π * (N ^ 2 / 2)) ^ 3 = π ^ 3 * N ^ 6 / 8 := by ring
          rw [this]
          have hN6 : 0 ≤ N ^ 6 := by positivity
          nlinarith
      _ ≤ (π * (N ^ 2 - 1)) ^ 3 / 6 := by gcongr
      _ ≤ Real.exp (π * (N ^ 2 - 1)) := hexp
  rw [le_div_iff₀ (by positivity)]
  calc Real.exp (-π * N ^ 2) * (2 * (2 * K + 1 : ℝ) ^ 4)
      ≤ Real.exp (-π * N ^ 2) * Real.exp (π * (N ^ 2 - 1)) := by gcongr
    _ = Real.exp (-π) := by rw [← Real.exp_add]; congr 1; ring

set_option maxHeartbeats 1000000 in
-- the final assembly elaborates many large terms
/-- **Four squares in caps, assuming many representations.** -/
theorem fourSquaresDense_of_reps
    (hr : ∃ c > 0, ∃ M₁ : ℕ, ∀ m : ℕ, M₁ ≤ m → Odd m → c * m ≤ ((reps m).card : ℝ)) :
    FourSquaresDense := by
  classical
  obtain ⟨c, hc, M₁, hM₁⟩ := hr
  obtain ⟨Cω, hCω⟩ := exists_DFIOmega
  obtain ⟨η, E, hη⟩ := exists_DFIEta
  intro q hq δ hδ
  set δ₁ := min δ 1 with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min hδ (by norm_num)
  have hδ₁1 : δ₁ ≤ 1 := min_le_right _ _
  set N := 150 / δ₁ ^ 2 with hN
  have hN0 : 0 < N := by positivity
  set δ' := δ₁ / N with hδ'
  have hδ'0 : 0 < δ' := by positivity
  have hδ'1 : δ' ≤ 1 := by
    rw [hδ', div_le_one hN0, hN, le_div_iff₀ (by positivity)]; nlinarith [pow_le_one₀ hδ₁0.le hδ₁1 (n := 3)]
  set K := ⌈2 / δ'⌉₊ with hK
  have hK2 : 2 ≤ K := by
    have : (2 : ℝ) ≤ 2 / δ' := by rw [le_div_iff₀ hδ'0]; nlinarith
    have := Nat.le_ceil (2 / δ')
    have : (2 : ℝ) ≤ K := by linarith
    exact_mod_cast this
  set κ := Real.exp (-π) / (2 * (2 * K + 1 : ℝ) ^ 4) with hκ
  have hκ0 : 0 < κ := by positivity
  have hkb : Real.exp (-π * N ^ 2) ≤ κ := kappa_bound δ₁ hδ₁0 hδ₁1
  have hE0 : 0 ≤ E := (abs_nonneg _).trans (hη.bound 0 (by norm_num) 0)
  -- constants
  obtain ⟨M₂, hM₂⟩ := eventually_lt
    (8 * 551000 * 2 * Real.sqrt 2 * 4 ^ 17 * 2 ^ (1 / 8 : ℝ) * (Cω * E)) (c * κ) (by positivity)
  refine ⟨max (max M₁ M₂) 16, fun m hm hodd => ?_⟩
  have hm16 : 16 ≤ m := le_trans (le_max_right _ _) hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hm0 : (0 : ℝ) < m := by linarith
  set X := Real.sqrt m with hX
  have hX0 : 0 < X := Real.sqrt_pos.mpr hm0
  have hX2 : X ^ 2 = m := Real.sq_sqrt hm0.le
  have hX4 : 4 ≤ X := by
    rw [hX, Real.le_sqrt (by norm_num) hm0.le]
    have : (16 : ℝ) ≤ m := by exact_mod_cast hm16
    linarith
  set D : ℕ := 3 * m + 3 with hD
  have hDQ : 2 * X ≤ D := by
    have : X ≤ m := by rw [hX, Real.sqrt_le_left (by linarith)]; nlinarith
    push_cast [hD]; linarith
  have hDT : 4 * X ^ 2 / 2 ≤ D := by rw [hX2]; push_cast [hD]; linarith
  obtain ⟨ω, hω, hsum⟩ := hCω X hX4 D hDQ
  have hC0 : 0 ≤ Cω := hω.C_nonneg
  obtain ⟨g0, g, hg⟩ : ∃ g0 g : ℕ → ℕ, ∀ q, GoodDecomp (2 * (m : ℤ).natAbs) q (g0 q) (g q) := by
    choose g0 g hg using exists_goodDecomp (2 * (m : ℤ).natAbs)
    exact ⟨g0, g, hg⟩
  set A : Fin 4 → ℝ := fun i => X * q i with hA
  have hAsq : ∑ i, A i ^ 2 = X ^ 2 := by
    simp only [hA, mul_pow, ← mul_sum, hq, mul_one]
  have hAabs : ∀ i, |A i| ≤ X := by
    intro i
    have hqi : q i ^ 2 ≤ 1 := by
      rw [← hq]; exact single_le_sum (f := fun j => q j ^ 2) (fun j _ => sq_nonneg _) (mem_univ i)
    have : |q i| ≤ 1 := by rw [← abs_one, ← sq_le_sq]; simpa using hqi
    simp only [hA, abs_mul, abs_of_pos hX0]
    nlinarith
  set L := δ' * X with hL
  have hL0 : 0 < L := by positivity
  set ε := 2 * (4 * (Cω * E) * errXi X (4 * X ^ 2) L X *
    ∑ q ∈ Icc 1 ⌊2 * X⌋₊, (2 : ℝ) ^ (g q).primeFactors.card / Real.sqrt (g q)) with hε
  -- the box count
  have hbox := box_count_ge m A L (δ₁ * X) ε hL0 (by positivity) (centers X K)
    (by
      obtain ⟨A', hA', -⟩ := grid_cover X hX0 K hK2 (fun _ => X / 2)
        (by simp; rw [show (4 : ℝ) * (X / 2) ^ 2 = X ^ 2 by ring])
      exact ⟨A', hA'⟩)
    (fun x hx => by
      have hxs : ∑ i, ((x i : ℤ) : ℝ) ^ 2 = X ^ 2 := by
        rw [hX2]; have := (mem_reps m x).mp hx; exact_mod_cast this
      obtain ⟨A', hA', hd⟩ := grid_cover X hX0 K hK2 (fun i => (x i : ℝ)) hxs
      refine ⟨A', hA', hd.trans ?_⟩
      have : 2 * X / K ≤ L := by
        rw [hL, div_le_iff₀ (by positivity)]
        have hKd : 2 / δ' ≤ K := Nat.le_ceil _
        rw [div_le_iff₀ hδ'0] at hKd
        nlinarith
      exact pow_le_pow_left₀ (by positivity) this 2)
    (fun A' hA' => by
      have h := countW_sub_le A A' (by rw [hAsq, centers_sq X K A' hA']) L hL0 (m : ℤ) hω hη D
        hDQ hDT hsum X hX0 hAabs (centers_abs X hX0.le K A' hA')
        g (fun q _ => ⟨g0 q, hg q⟩)
      exact h)
  -- lower bound
  have hcard := hM₁ m (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm) hodd
  have hcenters : ((centers X K).card : ℝ) ≤ (2 * K + 1) ^ 4 := card_centers_le X K
  have hcpos : (0 : ℝ) < (centers X K).card := by
    obtain ⟨A', hA', -⟩ := grid_cover X hX0 K hK2 (fun _ => X / 2)
      (by simp; rw [show (4 : ℝ) * (X / 2) ^ 2 = X ^ 2 by ring])
    exact_mod_cast (Finset.card_pos.mpr ⟨A', hA'⟩)
  have hR : Real.exp (-π * (δ₁ * X) ^ 2 / L ^ 2) = Real.exp (-π * N ^ 2) := by
    congr 1; rw [hL, hδ']; field_simp
  have hbracket : κ ≤ Real.exp (-π) / (centers X K).card - Real.exp (-π * (δ₁ * X) ^ 2 / L ^ 2) := by
    rw [hR]
    have h1 : Real.exp (-π) / (2 * K + 1 : ℝ) ^ 4 ≤ Real.exp (-π) / (centers X K).card :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le hcpos hcenters
    have h2 : Real.exp (-π) / (2 * K + 1 : ℝ) ^ 4 = 2 * κ := by rw [hκ]; field_simp
    linarith
  -- the error is small
  have hεle := eps_le (Cω * E) (by positivity) m (by omega) δ' hδ'0 hδ'1 g (fun q _ => ⟨g0 q, hg q⟩)
  have hlt := hM₂ m (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm)
  have hpos : (0 : ℝ) < ((reps m).filter (fun x => ∀ i, |(x i : ℝ) - A i| ≤ δ₁ * X)).card := by
    have hcardnn : (0 : ℝ) ≤ (reps m).card := by positivity
    have : c * m * κ ≤ ((reps m).card : ℝ) *
        (Real.exp (-π) / (centers X K).card - Real.exp (-π * (δ₁ * X) ^ 2 / L ^ 2)) := by
      calc c * m * κ ≤ ((reps m).card : ℝ) * κ := by gcongr
        _ ≤ _ := by gcongr
    have hε' : ε < c * κ * m := lt_of_le_of_lt hεle hlt
    have e : c * κ * m = c * m * κ := by ring
    linarith
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by exact_mod_cast hpos)
  rw [mem_filter] at hx
  refine ⟨x, (mem_reps m x).mp hx.1, fun i => ?_⟩
  have := hx.2 i
  simp only [hA] at this
  calc |(x i : ℝ) - Real.sqrt m * q i| = |(x i : ℝ) - X * q i| := by rw [hX]
    _ ≤ δ₁ * X := this
    _ ≤ δ * Real.sqrt m := by rw [hX]; gcongr; exact min_le_left _ _

end FourSquaresCaps
