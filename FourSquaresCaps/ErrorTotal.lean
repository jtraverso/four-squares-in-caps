/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.ErrorBound
public import FourSquaresCaps.DecompSum

/-!
# Assembling the error term

* `hW_eq_zero_of_large`: for `T ≤ 4Q²` and `q > 2Q`, the weight `h_q` vanishes identically.
* `norm_expSumS_le_four`: `‖S_q(m, c)‖ ≤ 4 q³ 2^{ω(q₁)} / √q₁`.
-/

@[expose] public section

namespace FourSquaresCaps

open Finset

theorem hW_eq_zero_of_large {ω η : ℝ → ℝ} {Q C E : ℝ} (h : DFIOmega ω Q C) (hη : DFIEta η E)
    (D q : ℕ) {T : ℝ} (hT0 : 0 < T) (hTQ : T ≤ 4 * Q ^ 2) (hq : 2 * Q < q) (u : ℝ) :
    hW ω η D q T u = 0 := by
  have hQ : 0 < Q := lt_of_lt_of_le one_pos h.one_le
  have hq0 : (0 : ℝ) < q := by linarith
  rcases lt_or_ge (T / 2) |u| with hu | hu
  · exact hW_eq_zero hη D q hT0 u hu
  · unfold hW
    rw [show deltaW ω D q u = 0 from ?_, mul_zero]
    unfold deltaW
    refine sum_eq_zero fun r _ => ?_
    have hr : (1 : ℝ) ≤ (r : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) r; linarith
    have hc : (q : ℝ) ≤ q * ((r : ℝ) + 1) := le_mul_of_one_le_right hq0.le hr
    have hc0 : (0 : ℝ) < q * ((r : ℝ) + 1) := by positivity
    rw [h.zero_out _ (Or.inr (by linarith)), h.zero_out _ (Or.inl ?_), sub_zero, mul_zero]
    rw [div_lt_iff₀ hc0]
    nlinarith

theorem norm_expSumS_le_four (m : ℤ) {q q₀ q₁ : ℕ} (hd : GoodDecomp (2 * m.natAbs) q q₀ q₁)
    [NeZero q] (c : Fin 4 → ℤ) :
    ‖expSumS (q := q) (m : ZMod q) (fun i => (c i : ZMod q))‖ ≤
      4 * (q : ℝ) ^ 3 * ((2 : ℝ) ^ q₁.primeFactors.card / Real.sqrt q₁) := by
  refine (norm_expSumS_le_decomp m hd c).trans (le_of_eq_of_le rfl ?_)
  obtain ⟨hq, -, -, -, -⟩ := hd
  have hq0 : q₀ ≠ 0 := fun h0 => NeZero.ne q (by rw [hq, h0, zero_mul])
  have hq1 : q₁ ≠ 0 := fun h0 => NeZero.ne q (by rw [hq, h0, mul_zero])
  have hq1' : (0 : ℝ) < q₁ := by exact_mod_cast Nat.pos_of_ne_zero hq1
  have hs : 0 < Real.sqrt q₁ := Real.sqrt_pos.mpr hq1'
  have htot : (q₀.totient : ℝ) ≤ q₀ := by exact_mod_cast Nat.totient_le q₀
  have hsq : Real.sqrt q₁ ^ 2 = q₁ := Real.sq_sqrt hq1'.le
  rw [hq]
  push_cast
  have h2 : (0 : ℝ) ≤ 2 ^ q₁.primeFactors.card := by positivity
  calc (q₀.totient : ℝ) * (2 * q₀) ^ 2 * ((q₁ : ℝ) ^ 2 * (2 ^ q₁.primeFactors.card * Real.sqrt q₁))
      ≤ q₀ * (2 * q₀) ^ 2 * ((q₁ : ℝ) ^ 2 * (2 ^ q₁.primeFactors.card * Real.sqrt q₁)) := by
        gcongr
    _ = 4 * ((q₀ : ℝ) * q₁) ^ 3 * (2 ^ q₁.primeFactors.card / Real.sqrt q₁) := by
        field_simp
        rw [show Real.sqrt q₁ ^ 2 = (q₁ : ℝ) from hsq]
        ring

/-- The `q`-independent constant of the error. -/
noncomputable def errXi (Q T L Amax : ℝ) : ℝ :=
  8000 * (12 * T / Q + 4 * Q) + 32000 * L ^ 4 * (4 + 2 * Real.log T) / Q ^ 3 +
    2048 * (3 + 2 * Real.log T) * Amax ^ 2 / Q

/-- **The bracket.** -/
theorem bracket_le (C E Q T L Amax B0 B1 B4 : ℝ) (q : ℕ) (hCE : 0 ≤ C * E) (hQ : 1 ≤ Q)
    (hq1 : 1 ≤ q) (hqQ : (q : ℝ) ≤ 2 * Q) (hT0 : 0 ≤ T) (hΛ : 0 ≤ 3 + 2 * Real.log T)
    (hB0 : B0 = 6 * C * E * T / (q * Q)) (hB1 : B1 ≤ C * E * (3 + 2 * Real.log T) / (q * Q))
    (hB10 : 0 ≤ B1) (hB4 : B4 * (q * Q) ^ 4 ≤ C * E) (hB40 : 0 ≤ B4) :
    (q : ℝ) ^ 3 * (8000 * max B0 (B4 * (q * Q) ^ 4) / (q * Q) +
      32000 * L ^ 4 * max (B1 / (q * Q)) (B4 * (q * Q) ^ 2) / (q * Q) +
      2048 * B1 * Amax ^ 2 / q ^ 2) ≤ C * E * errXi Q T L Amax := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hQ0 : 0 < Q := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  set Λ := 3 + 2 * Real.log T with hΛdef
  set a := (q : ℝ) * Q with ha_def
  have ha : 0 < a := by positivity
  have hB00 : 0 ≤ B0 := by
    rw [hB0]; exact div_nonneg (by have := mul_nonneg hCE hT0; nlinarith) ha.le
  have m1 : max B0 (B4 * a ^ 4) ≤ B0 + C * E := max_le (by linarith) (by linarith)
  have m2 : max (B1 / a) (B4 * a ^ 2) ≤ C * E * (Λ + 1) / a ^ 2 := by
    refine max_le ?_ ?_
    · calc B1 / a ≤ C * E * Λ / a / a := div_le_div_of_nonneg_right hB1 ha.le
        _ ≤ C * E * (Λ + 1) / a ^ 2 := by
          rw [div_div, ← sq]; gcongr; linarith
    · calc B4 * a ^ 2 = B4 * a ^ 4 / a ^ 2 := by field_simp
        _ ≤ C * E / a ^ 2 := div_le_div_of_nonneg_right hB4 (by positivity)
        _ ≤ C * E * (Λ + 1) / a ^ 2 :=
          div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hCE hΛ]) (by positivity)
  have T1 : (q : ℝ) ^ 3 * (8000 * max B0 (B4 * a ^ 4) / a) ≤
      C * E * (8000 * (12 * T / Q + 4 * Q)) := by
    calc (q : ℝ) ^ 3 * (8000 * max B0 (B4 * a ^ 4) / a)
        ≤ (q : ℝ) ^ 3 * (8000 * (B0 + C * E) / a) := by gcongr
      _ = C * E * (8000 * (6 * T * q / Q ^ 2 + q ^ 2 / Q)) := by
          rw [hB0, ha_def]; field_simp
      _ ≤ C * E * (8000 * (12 * T / Q + 4 * Q)) := by
          have a1 : 6 * T * q / Q ^ 2 ≤ 12 * T / Q := by
            rw [div_le_div_iff₀ (by positivity) hQ0]; nlinarith [mul_nonneg hT0 hQ0.le]
          have a2 : (q : ℝ) ^ 2 / Q ≤ 4 * Q := by
            rw [div_le_iff₀ hQ0]; nlinarith
          apply mul_le_mul_of_nonneg_left _ hCE
          linarith
  have T2 : (q : ℝ) ^ 3 * (32000 * L ^ 4 * max (B1 / a) (B4 * a ^ 2) / a) ≤
      C * E * (32000 * L ^ 4 * (4 + 2 * Real.log T) / Q ^ 3) := by
    calc (q : ℝ) ^ 3 * (32000 * L ^ 4 * max (B1 / a) (B4 * a ^ 2) / a)
        ≤ (q : ℝ) ^ 3 * (32000 * L ^ 4 * (C * E * (Λ + 1) / a ^ 2) / a) := by gcongr
      _ = C * E * (32000 * L ^ 4 * (4 + 2 * Real.log T) / Q ^ 3) := by
          rw [ha_def, hΛdef]; field_simp; ring
  have T3 : (q : ℝ) ^ 3 * (2048 * B1 * Amax ^ 2 / q ^ 2) ≤
      C * E * (2048 * (3 + 2 * Real.log T) * Amax ^ 2 / Q) := by
    calc (q : ℝ) ^ 3 * (2048 * B1 * Amax ^ 2 / q ^ 2) = 2048 * q * B1 * Amax ^ 2 := by
          field_simp
      _ ≤ 2048 * q * (C * E * Λ / a) * Amax ^ 2 := by gcongr
      _ = C * E * (2048 * (3 + 2 * Real.log T) * Amax ^ 2 / Q) := by
          rw [ha_def, hΛdef]; field_simp
  unfold errXi
  rw [mul_add, mul_add]
  nlinarith [T1, T2, T3]

open Complex Real FourierTransform in
/-- **Total error.** -/
theorem error_total_le (A : Fin 4 → ℝ) (L : ℝ) (hL0 : 0 < L) (m : ℤ)
    {ω η : ℝ → ℝ} {Q C E : ℝ} (h : DFIOmega ω Q C) (hη : DFIEta η E) (D : ℕ)
    (Amax : ℝ) (hAmax : 0 < Amax) (hA : ∀ i, |A i| ≤ Amax)
    (g : ℕ → ℕ) (hg : ∀ q, q ≠ 0 → ∃ q₀, GoodDecomp (2 * m.natAbs) q q₀ (g q)) :
    ‖∑ k ∈ range D, ∫ τ, 𝓕 (fun u => (hW ω η D (k + 1) (4 * Q ^ 2) u : ℂ)) τ *
        (cexp (-(2 * π * I * (τ : ℂ) * m)) *
          (1 / (((k + 1 : ℕ) : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * τ)) ^ (1 / 2 : ℂ)) ^ 4 *
          ∑' c : Fin 4 → ℤ, (if c = 0 then 0 else
            expSumS (m : ZMod (k + 1)) (fun i => (c i : ZMod (k + 1))) *
              ∏ i, mTerm (A i) L τ (k + 1) (c i)))‖ ≤
      4 * (C * E) * errXi Q (4 * Q ^ 2) L Amax *
        ∑ q ∈ Icc 1 ⌊2 * Q⌋₊, (2 : ℝ) ^ (g q).primeFactors.card / Real.sqrt (g q) := by
  classical
  have hQ : 1 ≤ Q := h.one_le
  have hQ0 : 0 < Q := by linarith
  have hC := h.C_nonneg
  have hE : 0 ≤ E := (abs_nonneg _).trans (hη.bound 0 (by norm_num) 0)
  have hCE : 0 ≤ C * E := mul_nonneg hC hE
  set T := 4 * Q ^ 2 with hT
  have hT0 : 0 < T := by positivity
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by nlinarith)
  have hΞ : 0 ≤ errXi Q T L Amax := by unfold errXi; positivity
  set w : ℕ → ℝ := fun q => (2 : ℝ) ^ (g q).primeFactors.card / Real.sqrt (g q) with hw
  have hw0 : ∀ q, 0 ≤ w q := fun q => by simp only [hw]; positivity
  have hk : ∀ k ∈ range D, ‖∫ τ, 𝓕 (fun u => (hW ω η D (k + 1) T u : ℂ)) τ *
        (cexp (-(2 * π * I * (τ : ℂ) * m)) *
          (1 / (((k + 1 : ℕ) : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * τ)) ^ (1 / 2 : ℂ)) ^ 4 *
          ∑' c : Fin 4 → ℤ, (if c = 0 then 0 else
            expSumS (m : ZMod (k + 1)) (fun i => (c i : ZMod (k + 1))) *
              ∏ i, mTerm (A i) L τ (k + 1) (c i)))‖ ≤
      if ((k + 1 : ℕ) : ℝ) ≤ 2 * Q then 4 * (C * E) * errXi Q T L Amax * w (k + 1) else 0 := by
    intro k _
    have hq1 : 1 ≤ k + 1 := by omega
    have hqR : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hq1
    obtain ⟨q₀, hd⟩ := hg (k + 1) (by omega)
    have hS : ∀ c : Fin 4 → ℤ,
        ‖expSumS (m : ZMod (k + 1)) (fun i => (c i : ZMod (k + 1)))‖ ≤
        4 * ((k + 1 : ℕ) : ℝ) ^ 3 * w (k + 1) := fun c => norm_expSumS_le_four m hd c
    set F := 𝓕 (fun u => (hW ω η D (k + 1) T u : ℂ)) with hFdef
    split_ifs with hqQ
    · have h2 : 2 * (((k + 1 : ℕ) : ℝ) * Q) ≤ T := by rw [hT]; nlinarith
      have hF := fun τ => norm_fourier_hW_le h hη D (k + 1) hq1 h2 τ
      set a := ((k + 1 : ℕ) : ℝ) * Q with ha_def
      have ha : 0 < a := by positivity
      have h2pi : 0 < 2 * π := by positivity
      have hF1 : ∀ τ, |τ| * ‖F τ‖ ≤
          6 * C * E / a * (3 + 2 * Real.log (T / (2 * a))) / (2 * π) := by
        intro τ
        rw [le_div_iff₀ h2pi]
        have := (hF τ).2.1
        linarith
      have hF4 : ∀ τ, τ ^ 4 * ‖F τ‖ ≤ 656 * C * E / a ^ 4 / (2 * π) ^ 4 := by
        intro τ
        rw [le_div_iff₀ (by positivity)]
        have := (hF τ).2.2
        rw [mul_pow, pow_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ τ ^ 4)] at this
        linarith
      have he := error_q_le A L hL0 (k + 1) m Amax hAmax hA _ hS F _ _ _ a ha
        (fun τ => (hF τ).1) hF1 hF4
      refine he.trans ?_
      have hpi3 : 3 < π := Real.pi_gt_three
      have hlog1 : Real.log (T / (2 * a)) ≤ Real.log T :=
        Real.log_le_log (by positivity) (div_le_self hT0.le (by nlinarith))
      have hlog0 : 0 ≤ Real.log (T / (2 * a)) :=
        Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith)
      have hCEa : 0 ≤ 6 * C * E / a := div_nonneg (by nlinarith) ha.le
      have hB1 : 6 * C * E / a * (3 + 2 * Real.log (T / (2 * a))) / (2 * π) ≤
          C * E * (3 + 2 * Real.log T) / a := by
        rw [div_le_iff₀ h2pi]
        have h6 : 6 ≤ 2 * π := by linarith
        calc 6 * C * E / a * (3 + 2 * Real.log (T / (2 * a))) ≤
            6 * C * E / a * (3 + 2 * Real.log T) :=
              mul_le_mul_of_nonneg_left (by linarith) hCEa
          _ = 6 * (C * E * (3 + 2 * Real.log T) / a) := by ring
          _ ≤ 2 * π * (C * E * (3 + 2 * Real.log T) / a) := by
              apply mul_le_mul_of_nonneg_right h6
              exact div_nonneg (mul_nonneg hCE (by linarith)) ha.le
          _ = C * E * (3 + 2 * Real.log T) / a * (2 * π) := by ring
      have hB10 : 0 ≤ 6 * C * E / a * (3 + 2 * Real.log (T / (2 * a))) / (2 * π) :=
        div_nonneg (mul_nonneg hCEa (by linarith)) h2pi.le
      have hB4 : 656 * C * E / a ^ 4 / (2 * π) ^ 4 * a ^ 4 ≤ C * E := by
        have h656 : 656 ≤ (2 * π) ^ 4 := by
          have : (6 : ℝ) ^ 4 ≤ (2 * π) ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
          linarith
        have e : 656 * C * E / a ^ 4 / (2 * π) ^ 4 * a ^ 4 = 656 * (C * E) / (2 * π) ^ 4 := by
          field_simp
        rw [e, div_le_iff₀ (by positivity)]
        nlinarith
      have hB40 : 0 ≤ 656 * C * E / a ^ 4 / (2 * π) ^ 4 :=
        div_nonneg (div_nonneg (by nlinarith) (by positivity)) (by positivity)
      have hb := bracket_le C E Q T L Amax (6 * C * E * T / a)
        (6 * C * E / a * (3 + 2 * Real.log (T / (2 * a))) / (2 * π))
        (656 * C * E / a ^ 4 / (2 * π) ^ 4) (k + 1) hCE hQ hq1 hqQ hT0.le (by linarith) rfl
        hB1 hB10 hB4 hB40
      calc 4 * ((k + 1 : ℕ) : ℝ) ^ 3 * w (k + 1) *
            (8000 * max (6 * C * E * T / a) (656 * C * E / a ^ 4 / (2 * π) ^ 4 * a ^ 4) / a +
              32000 * L ^ 4 * max (6 * C * E / a * (3 + 2 * Real.log (T / (2 * a))) /
                (2 * π) / a) (656 * C * E / a ^ 4 / (2 * π) ^ 4 * a ^ 2) / a +
              2048 * (6 * C * E / a * (3 + 2 * Real.log (T / (2 * a))) / (2 * π)) * Amax ^ 2 /
                ((k + 1 : ℕ) : ℝ) ^ 2)
          = 4 * w (k + 1) * (((k + 1 : ℕ) : ℝ) ^ 3 *
            (8000 * max (6 * C * E * T / a) (656 * C * E / a ^ 4 / (2 * π) ^ 4 * a ^ 4) / a +
              32000 * L ^ 4 * max (6 * C * E / a * (3 + 2 * Real.log (T / (2 * a))) /
                (2 * π) / a) (656 * C * E / a ^ 4 / (2 * π) ^ 4 * a ^ 2) / a +
              2048 * (6 * C * E / a * (3 + 2 * Real.log (T / (2 * a))) / (2 * π)) * Amax ^ 2 /
                ((k + 1 : ℕ) : ℝ) ^ 2)) := by ring
        _ ≤ 4 * w (k + 1) * (C * E * errXi Q T L Amax) :=
            mul_le_mul_of_nonneg_left hb (by have := hw0 (k + 1); positivity)
        _ = 4 * (C * E) * errXi Q T L Amax * w (k + 1) := by ring
    · push Not at hqQ
      have hz : ∀ u, hW ω η D (k + 1) T u = 0 :=
        fun u => hW_eq_zero_of_large h hη D (k + 1) hT0 (le_of_eq hT) hqQ u
      have hF0 : ∀ τ, ‖F τ‖ = 0 := by
        intro τ
        refine le_antisymm ((norm_fourier_le_integral _ τ).trans (le_of_eq ?_)) (norm_nonneg _)
        simp [hz]
      refine (MeasureTheory.norm_integral_le_of_norm_le (g := fun _ => (0 : ℝ))
        (MeasureTheory.integrable_zero _ _ _) (Filter.Eventually.of_forall fun τ => ?_)).trans
        (by simp)
      rw [norm_mul, hF0, zero_mul]
  refine (norm_sum_le _ _).trans ((sum_le_sum hk).trans ?_)
  rw [← sum_filter, mul_sum]
  refine sum_le_sum_of_injOn (fun k => k + 1) (fun a _ b _ hab => by simpa using hab) ?_
    (fun k _ => le_rfl) (fun q _ _ => by have := hw0 q; positivity)
  intro q hq
  simp only [mem_image, mem_filter, mem_range] at hq
  obtain ⟨k, ⟨_, hkQ⟩, rfl⟩ := hq
  simp only [mem_Icc]
  refine ⟨by omega, Nat.le_floor ?_⟩
  exact_mod_cast hkQ

/-- **The arithmetic factor.** -/
theorem sum_w_le (m : ℤ) (hm : m ≠ 0) (Y : ℕ) (g : ℕ → ℕ)
    (hg : ∀ q, q ≠ 0 → ∃ q₀, GoodDecomp (2 * m.natAbs) q q₀ (g q)) :
    ∑ q ∈ Icc 1 Y, (2 : ℝ) ^ (g q).primeFactors.card / Real.sqrt (g q) ≤
      2 * Real.sqrt Y * (1 + Real.log Y) ^ 3 * (4 ^ 17 * ((2 * m.natAbs : ℕ) : ℝ) ^ (1 / 8 : ℝ)) := by
  have hM : 2 * m.natAbs ≠ 0 := by have := Int.natAbs_ne_zero.mpr hm; omega
  have h1 := sum_decomp_le (2 * m.natAbs) Y hM g hg
  have h2 := sum_sigmaHalf_div_le Y
  have h3 := sigmaHalf_le (2 * m.natAbs) hM
  have hl : 0 ≤ 1 + Real.log Y := by have := Real.log_natCast_nonneg Y; linarith
  have hs : 0 ≤ sigmaHalf (2 * m.natAbs) := by
    unfold sigmaHalf; exact Finset.sum_nonneg fun _ _ => by positivity
  have hsum0 : 0 ≤ ∑ a ∈ Icc 1 Y, sigmaHalf a / a := Finset.sum_nonneg fun a _ => by
    unfold sigmaHalf; exact div_nonneg (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
  calc _ ≤ 2 * Real.sqrt Y * (1 + Real.log Y) * sigmaHalf (2 * m.natAbs) *
        ∑ a ∈ Icc 1 Y, sigmaHalf a / a := h1
    _ ≤ 2 * Real.sqrt Y * (1 + Real.log Y) * (4 ^ 17 * ((2 * m.natAbs : ℕ) : ℝ) ^ (1 / 8 : ℝ)) *
        (1 + Real.log Y) ^ 2 := by gcongr
    _ = _ := by ring

end FourSquaresCaps
