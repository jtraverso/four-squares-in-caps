/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.Delta
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Pointwise bounds for the DFI weight

`ω` is smooth, vanishes off `[Q, 2Q]`, and `|ω^{(j)}| ≤ C Q^{-1-j}` for `j ≤ 4`.
For `t > 0`: `∑_r (q r)^{-1-j} |ω^{(j)}(t/(q r))| ≤ 3 C 2^j t^{-j} / (q Q)`, and the sum vanishes
for `t < q Q` (`sum_omega_deriv_le`, `sum_omega_deriv_eq_zero`).
-/

@[expose] public section

namespace FourSquaresCaps

open Finset

/-- Hypotheses on the DFI bump `ω`. -/
structure DFIOmega (ω : ℝ → ℝ) (Q C : ℝ) : Prop where
  one_le : 1 ≤ Q
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω
  zero_out : ∀ y, y < Q ∨ 2 * Q < y → ω y = 0
  bound : ∀ j ≤ 4, ∀ y, |iteratedDeriv j ω y| ≤ C / Q ^ (j + 1)

namespace DFIOmega

variable {ω : ℝ → ℝ} {Q C : ℝ}

theorem deriv_zero_out (h : DFIOmega ω Q C) (j : ℕ) (y : ℝ) (hy : y < Q ∨ 2 * Q < y) :
    iteratedDeriv j ω y = 0 := by
  have hev : ω =ᶠ[nhds y] fun _ => 0 := by
    rcases hy with hy | hy
    · filter_upwards [Iio_mem_nhds hy] with z hz using h.zero_out z (Or.inl hz)
    · filter_upwards [Ioi_mem_nhds hy] with z hz using h.zero_out z (Or.inr hz)
  rw [(hev.iteratedDeriv j).eq_of_nhds]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · simp

theorem C_nonneg (h : DFIOmega ω Q C) : 0 ≤ C := by
  have := h.bound 0 (by norm_num) 0
  have hQ : 0 < Q ^ (0 + 1) := by have := h.one_le; positivity
  have := (abs_nonneg _).trans this
  exact (div_nonneg_iff.mp this).elim (fun h => h.1) fun h => absurd h.2 (not_le.mpr hQ)

/-- `ω(|u|/c) = ω(u/c) + ω(−u/c)` for `c > 0`. -/
theorem comp_abs (h : DFIOmega ω Q C) (u c : ℝ) (hc : 0 < c) :
    ω (|u| / c) = ω (u / c) + ω (-u / c) := by
  have hQ : 0 < Q := lt_of_lt_of_le one_pos h.one_le
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu, h.zero_out (-u / c) (Or.inl (by
      have : -u / c ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hc.le
      linarith)), add_zero]
  · rw [abs_of_neg hu, h.zero_out (u / c) (Or.inl (by
      have : u / c < 0 := div_neg_of_neg_of_pos hu hc
      linarith)), zero_add]

end DFIOmega

/-- Integers `r + 1` in `[a/2, a]`: at most `a/2 + 1`. -/
theorem card_filter_le (D : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    (((range D).filter (fun r : ℕ => a / 2 ≤ (r : ℝ) + 1 ∧ (r : ℝ) + 1 ≤ a)).card : ℝ) ≤
      a / 2 + 1 := by
  set S := (range D).filter (fun r : ℕ => a / 2 ≤ (r : ℝ) + 1 ∧ (r : ℝ) + 1 ≤ a)
  have hsub : S.map ⟨(· + 1), add_left_injective 1⟩ ⊆ Icc ⌈a / 2⌉₊ ⌊a⌋₊ := by
    intro x hx
    simp only [mem_map, Function.Embedding.coeFn_mk, S, mem_filter, mem_range] at hx
    obtain ⟨r, ⟨_, h1, h2⟩, rfl⟩ := hx
    simp only [mem_Icc]
    constructor
    · exact Nat.ceil_le.mpr (by push_cast; linarith)
    · exact Nat.le_floor (by push_cast; linarith)
  have hc := card_le_card hsub
  rw [card_map, Nat.card_Icc] at hc
  have hfl : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha
  have hce : a / 2 ≤ (⌈a / 2⌉₊ : ℝ) := Nat.le_ceil _
  calc (S.card : ℝ) ≤ ((⌊a⌋₊ + 1 - ⌈a / 2⌉₊ : ℕ) : ℝ) := by exact_mod_cast hc
    _ ≤ a / 2 + 1 := by
        rcases le_or_gt ⌈a / 2⌉₊ (⌊a⌋₊ + 1) with hle | hlt
        · rw [Nat.cast_sub hle]; push_cast; linarith
        · rw [Nat.sub_eq_zero_of_le hlt.le]; push_cast; linarith

/-- **Pointwise bound.** For `t > 0`, `q ≥ 1`, `j ≤ 4`:
`∑_{r<D} (q(r+1))^{-1-j} |ω^{(j)}(t/(q(r+1)))| ≤ 3 C 2^j / (t^j q Q)`. -/
theorem sum_omega_deriv_le {ω : ℝ → ℝ} {Q C : ℝ} (h : DFIOmega ω Q C) (D q : ℕ) (hq : 1 ≤ q)
    (j : ℕ) (hj : j ≤ 4) (t : ℝ) (ht : 0 < t) :
    ∑ r ∈ range D, ((q : ℝ) * ((r : ℝ) + 1))⁻¹ ^ (j + 1) *
        |iteratedDeriv j ω (t / ((q : ℝ) * ((r : ℝ) + 1)))| ≤
      3 * C * 2 ^ j / (t ^ j * (q * Q)) := by
  have hQ : 0 < Q := lt_of_lt_of_le one_pos h.one_le
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hC := h.C_nonneg
  set a := t / (q * Q) with ha
  have ha0 : 0 < a := by positivity
  set S := (range D).filter (fun r : ℕ => a / 2 ≤ (r : ℝ) + 1 ∧ (r : ℝ) + 1 ≤ a)
  -- terms outside `S` vanish
  have hout : ∀ r ∈ range D, r ∉ S → ((q : ℝ) * ((r : ℝ) + 1))⁻¹ ^ (j + 1) *
      |iteratedDeriv j ω (t / ((q : ℝ) * ((r : ℝ) + 1)))| = 0 := by
    intro r hr hrS
    have hc : (0 : ℝ) < q * ((r : ℝ) + 1) := by positivity
    simp only [S, mem_filter, hr, true_and, not_and_or, not_le] at hrS
    rw [h.deriv_zero_out j _ ?_, abs_zero, mul_zero]
    rcases hrS with h1 | h1
    · right
      rw [lt_div_iff₀ hc]
      have : (r : ℝ) + 1 < t / (q * Q) / 2 := h1
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2), lt_div_iff₀ (by positivity)] at this
      nlinarith
    · left
      rw [div_lt_iff₀ hc]
      have : t / (q * Q) < (r : ℝ) + 1 := h1
      rw [div_lt_iff₀ (by positivity)] at this
      nlinarith
  -- terms in `S` are at most `C 2^{1+j} / t^{1+j}`
  have hin : ∀ r ∈ S, ((q : ℝ) * ((r : ℝ) + 1))⁻¹ ^ (j + 1) *
      |iteratedDeriv j ω (t / ((q : ℝ) * ((r : ℝ) + 1)))| ≤ C * 2 ^ (j + 1) / t ^ (j + 1) := by
    intro r hr
    simp only [S, mem_filter] at hr
    have hc : (0 : ℝ) < q * ((r : ℝ) + 1) := by positivity
    have hcge : t / (2 * Q) ≤ q * ((r : ℝ) + 1) := by
      have := hr.2.1
      rw [ha, div_div, div_le_iff₀ (by positivity)] at this
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hinv : (q * ((r : ℝ) + 1))⁻¹ ≤ 2 * Q / t := by
      rw [inv_le_comm₀ hc (by positivity), inv_div]; exact hcge
    calc ((q : ℝ) * ((r : ℝ) + 1))⁻¹ ^ (j + 1) * |iteratedDeriv j ω (t / ((q : ℝ) * ((r : ℝ) + 1)))|
        ≤ (2 * Q / t) ^ (j + 1) * (C / Q ^ (j + 1)) := by
          gcongr
          · exact h.bound j hj _
      _ = C * 2 ^ (j + 1) / t ^ (j + 1) := by
          rw [div_pow, mul_pow]; field_simp
  rw [← sum_filter_add_sum_filter_not (range D) (fun r : ℕ => a / 2 ≤ (r : ℝ) + 1 ∧ (r : ℝ) + 1 ≤ a)]
  have hz : ∑ r ∈ (range D).filter (fun r : ℕ => ¬ (a / 2 ≤ (r : ℝ) + 1 ∧ (r : ℝ) + 1 ≤ a)),
      ((q : ℝ) * ((r : ℝ) + 1))⁻¹ ^ (j + 1) *
        |iteratedDeriv j ω (t / ((q : ℝ) * ((r : ℝ) + 1)))| = 0 := by
    refine sum_eq_zero fun r hr => ?_
    rw [mem_filter] at hr
    exact hout r hr.1 (fun h' => hr.2 (mem_filter.mp h').2)
  rw [hz, add_zero]
  calc ∑ r ∈ S, ((q : ℝ) * ((r : ℝ) + 1))⁻¹ ^ (j + 1) *
        |iteratedDeriv j ω (t / ((q : ℝ) * ((r : ℝ) + 1)))|
      ≤ ∑ r ∈ S, C * 2 ^ (j + 1) / t ^ (j + 1) := sum_le_sum hin
    _ = S.card * (C * 2 ^ (j + 1) / t ^ (j + 1)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (3 / 2 * a) * (C * 2 ^ (j + 1) / t ^ (j + 1)) := by
        gcongr
        rcases le_or_gt 1 a with h1 | h1
        · have := card_filter_le D a ha0.le; linarith
        · -- no integer `r + 1 ≤ a < 1`
          have : S = ∅ := by
            apply eq_empty_of_forall_notMem
            intro r hr
            simp only [S, mem_filter] at hr
            have : (1 : ℝ) ≤ (r : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) r; linarith
            linarith [hr.2.2]
          rw [this, card_empty, Nat.cast_zero]; positivity
    _ = 3 * C * 2 ^ j / (t ^ j * (q * Q)) := by
        rw [ha]; field_simp; ring

/-- The sum vanishes for `t < q Q`. -/
theorem sum_omega_deriv_eq_zero {ω : ℝ → ℝ} {Q C : ℝ} (h : DFIOmega ω Q C) (D q : ℕ) (hq : 1 ≤ q)
    (j : ℕ) (t : ℝ) (ht : t < q * Q) :
    ∑ r ∈ range D, ((q : ℝ) * ((r : ℝ) + 1))⁻¹ ^ (j + 1) *
        |iteratedDeriv j ω (t / ((q : ℝ) * ((r : ℝ) + 1)))| = 0 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  refine sum_eq_zero fun r _ => ?_
  have hc : (0 : ℝ) < q * ((r : ℝ) + 1) := by positivity
  rw [h.deriv_zero_out j _ (Or.inl ?_), abs_zero, mul_zero]
  rw [div_lt_iff₀ hc]
  have : (q : ℝ) ≤ q * ((r : ℝ) + 1) := le_mul_of_one_le_right hq'.le (by
    have := Nat.cast_nonneg (α := ℝ) r; linarith)
  have hQ : 0 < Q := lt_of_lt_of_le one_pos h.one_le
  nlinarith

/-- The `u`-dependent part of `Δ_q`: `B(u) = ∑_r c_r⁻¹ (ω(u/c_r) + ω(−u/c_r))`, `c_r = q (r+1)`. -/
noncomputable def bW (ω : ℝ → ℝ) (D q : ℕ) (u : ℝ) : ℝ :=
  ∑ r ∈ range D, ((q : ℝ) * ((r : ℝ) + 1))⁻¹ *
    (ω (((q : ℝ) * ((r : ℝ) + 1))⁻¹ * u) + ω (-((q : ℝ) * ((r : ℝ) + 1))⁻¹ * u))

/-- The constant part `A = ∑_r c_r⁻¹ ω(c_r)`. -/
noncomputable def aW (ω : ℝ → ℝ) (D q : ℕ) : ℝ :=
  ∑ r ∈ range D, ((q : ℝ) * ((r : ℝ) + 1))⁻¹ * ω ((q : ℝ) * ((r : ℝ) + 1))

theorem deltaW_eq {ω : ℝ → ℝ} {Q C : ℝ} (h : DFIOmega ω Q C) (D q : ℕ) (hq : 1 ≤ q) (u : ℝ) :
    deltaW ω D q u = aW ω D q - bW ω D q u := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  unfold deltaW aW bW
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun r _ => ?_
  have hc : (0 : ℝ) < q * ((r : ℝ) + 1) := by positivity
  rw [h.comp_abs u _ hc, mul_sub]
  congr 2
  rw [div_eq_inv_mul, neg_div, div_eq_inv_mul, neg_mul]

theorem contDiff_bW {ω : ℝ → ℝ} {Q C : ℝ} (h : DFIOmega ω Q C) (D q : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bW ω D q) := by
  unfold bW
  refine ContDiff.sum fun r _ => contDiff_const.mul ?_
  exact (h.smooth.comp (contDiff_const.mul contDiff_id)).add
    (h.smooth.comp (contDiff_const.mul contDiff_id))

theorem iteratedDeriv_bW {ω : ℝ → ℝ} {Q C : ℝ} (h : DFIOmega ω Q C) (D q : ℕ) (j : ℕ) (u : ℝ) :
    iteratedDeriv j (bW ω D q) u = ∑ r ∈ range D, ((q : ℝ) * ((r : ℝ) + 1))⁻¹ *
      (((q : ℝ) * ((r : ℝ) + 1))⁻¹ ^ j *
          iteratedDeriv j ω (((q : ℝ) * ((r : ℝ) + 1))⁻¹ * u) +
        (-((q : ℝ) * ((r : ℝ) + 1))⁻¹) ^ j *
          iteratedDeriv j ω (-((q : ℝ) * ((r : ℝ) + 1))⁻¹ * u)) := by
  have hsm : ∀ c : ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => ω (c * u)) :=
    fun c => h.smooth.comp (contDiff_const.mul contDiff_id)
  have hj : ((j : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  unfold bW
  rw [iteratedDeriv_fun_sum fun r _ =>
    (contDiff_const.mul ((hsm _).add (hsm _))).contDiffAt.of_le hj]
  refine sum_congr rfl fun r _ => ?_
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_add ((hsm _).contDiffAt.of_le hj)
    ((hsm _).contDiffAt.of_le hj), iteratedDeriv_comp_const_mul (h.smooth.of_le hj),
    iteratedDeriv_comp_const_mul (h.smooth.of_le hj)]

/-- `|B^{(j)}(u)| ≤ ∑_r c_r^{-1-j} |ω^{(j)}(|u|/c_r)|`. -/
theorem abs_iteratedDeriv_bW_le {ω : ℝ → ℝ} {Q C : ℝ} (h : DFIOmega ω Q C) (D q : ℕ) (hq : 1 ≤ q)
    (j : ℕ) (u : ℝ) :
    |iteratedDeriv j (bW ω D q) u| ≤ ∑ r ∈ range D, ((q : ℝ) * ((r : ℝ) + 1))⁻¹ ^ (j + 1) *
      |iteratedDeriv j ω (|u| / ((q : ℝ) * ((r : ℝ) + 1)))| := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ : 0 < Q := lt_of_lt_of_le one_pos h.one_le
  rw [iteratedDeriv_bW h]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r _ => ?_)
  have hc : (0 : ℝ) < q * ((r : ℝ) + 1) := by positivity
  set c := (q : ℝ) * ((r : ℝ) + 1)
  have hci : 0 < c⁻¹ := inv_pos.mpr hc
  rcases le_or_gt 0 u with hu | hu
  · have hz : iteratedDeriv j ω (-c⁻¹ * u) = 0 := h.deriv_zero_out j _ (Or.inl (by
      have : -c⁻¹ * u ≤ 0 := by nlinarith
      linarith))
    rw [hz, mul_zero, add_zero, abs_of_nonneg hu, abs_mul, abs_mul, abs_of_pos hci, abs_pow,
      abs_of_pos hci, ← mul_assoc, ← pow_succ', div_eq_inv_mul]
  · have hz : iteratedDeriv j ω (c⁻¹ * u) = 0 := h.deriv_zero_out j _ (Or.inl (by
      have : c⁻¹ * u < 0 := mul_neg_of_pos_of_neg hci hu
      linarith))
    rw [hz, mul_zero, zero_add, abs_of_neg hu, abs_mul, abs_mul, abs_of_pos hci, abs_pow,
      abs_neg, abs_of_pos hci, ← mul_assoc, ← pow_succ', div_eq_inv_mul, neg_mul_comm]

theorem abs_aW_le {ω : ℝ → ℝ} {Q C : ℝ} (h : DFIOmega ω Q C) (D q : ℕ) (hq : 1 ≤ q) :
    |aW ω D q| ≤ 3 * C / (q * Q) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ : 0 < Q := lt_of_lt_of_le one_pos h.one_le
  have hC := h.C_nonneg
  set a := 2 * Q / q with ha
  have ha0 : 0 < a := by positivity
  set S := (range D).filter (fun r : ℕ => a / 2 ≤ (r : ℝ) + 1 ∧ (r : ℝ) + 1 ≤ a)
  have hterm : ∀ r ∈ range D, |((q : ℝ) * ((r : ℝ) + 1))⁻¹ * ω ((q : ℝ) * ((r : ℝ) + 1))| ≤
      if r ∈ S then C / Q ^ 2 else 0 := by
    intro r hr
    have hc : (0 : ℝ) < q * ((r : ℝ) + 1) := by positivity
    split_ifs with hrS
    · simp only [S, mem_filter] at hrS
      have hcQ : Q ≤ q * ((r : ℝ) + 1) := by
        have := hrS.2.1; rw [ha] at this
        rw [div_div, div_le_iff₀ (by positivity)] at this; nlinarith
      rw [abs_mul, abs_of_pos (inv_pos.mpr hc)]
      have h0 := h.bound 0 (by norm_num) (q * ((r : ℝ) + 1))
      simp only [iteratedDeriv_zero, zero_add, pow_one] at h0
      calc (q * ((r : ℝ) + 1))⁻¹ * |ω (q * ((r : ℝ) + 1))| ≤ Q⁻¹ * (C / Q) := by
            gcongr
      _ = C / Q ^ 2 := by field_simp
    · simp only [S, mem_filter, hr, true_and, not_and_or, not_le] at hrS
      rw [h.zero_out _ ?_, mul_zero, abs_zero]
      rcases hrS with h1 | h1
      · left
        rw [ha] at h1
        have : (r : ℝ) + 1 < Q / q := by linarith [show 2 * Q / q / 2 = Q / q by ring]
        rw [lt_div_iff₀ hq'] at this; linarith
      · right
        rw [ha, div_lt_iff₀ hq'] at h1; linarith
  unfold aW
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [sum_ite_mem, inter_eq_right.mpr (filter_subset _ _), sum_const, nsmul_eq_mul]
  rcases le_or_gt 1 a with h1 | h1
  · have hc := card_filter_le D a ha0.le
    change (S.card : ℝ) * (C / Q ^ 2) ≤ _
    calc (S.card : ℝ) * (C / Q ^ 2) ≤ (a / 2 + 1) * (C / Q ^ 2) := by gcongr
      _ ≤ (3 / 2 * a) * (C / Q ^ 2) := by gcongr; linarith
      _ = 3 * C / (q * Q) := by rw [ha]; field_simp
  · have : S = ∅ := by
      apply eq_empty_of_forall_notMem
      intro r hr
      simp only [S, mem_filter] at hr
      have : (1 : ℝ) ≤ (r : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) r; linarith
      linarith [hr.2.2]
    change (S.card : ℝ) * (C / Q ^ 2) ≤ _
    rw [this, card_empty, Nat.cast_zero, zero_mul]; positivity

theorem abs_bW_le {ω : ℝ → ℝ} {Q C : ℝ} (h : DFIOmega ω Q C) (D q : ℕ) (hq : 1 ≤ q) (u : ℝ) :
    |bW ω D q u| ≤ 3 * C / (q * Q) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ : 0 < Q := lt_of_lt_of_le one_pos h.one_le
  have hC := h.C_nonneg
  have h0 := abs_iteratedDeriv_bW_le h D q hq 0 u
  rw [iteratedDeriv_zero] at h0
  refine h0.trans ?_
  rcases eq_or_ne u 0 with rfl | hu
  · simp only [abs_zero, zero_div, iteratedDeriv_zero]
    rw [h.zero_out 0 (Or.inl (by linarith))]
    simp only [abs_zero, mul_zero, sum_const_zero]; positivity
  · have := sum_omega_deriv_le h D q hq 0 (by norm_num) |u| (abs_pos.mpr hu)
    simpa using this

/-- `|Δ_q(u)| ≤ 6 C / (q Q)`. -/
theorem abs_deltaW_le {ω : ℝ → ℝ} {Q C : ℝ} (h : DFIOmega ω Q C) (D q : ℕ) (hq : 1 ≤ q) (u : ℝ) :
    |deltaW ω D q u| ≤ 6 * C / (q * Q) := by
  rw [deltaW_eq h D q hq]
  calc |aW ω D q - bW ω D q u| ≤ |aW ω D q| + |bW ω D q u| := abs_sub _ _
    _ ≤ 3 * C / (q * Q) + 3 * C / (q * Q) := add_le_add (abs_aW_le h D q hq) (abs_bW_le h D q hq u)
    _ = 6 * C / (q * Q) := by ring

theorem iteratedDeriv_deltaW {ω : ℝ → ℝ} {Q C : ℝ} (h : DFIOmega ω Q C) (D q : ℕ) (hq : 1 ≤ q)
    (j : ℕ) (hj : 1 ≤ j) (u : ℝ) :
    iteratedDeriv j (deltaW ω D q) u = -iteratedDeriv j (bW ω D q) u := by
  have : deltaW ω D q = fun u => aW ω D q - bW ω D q u := funext (deltaW_eq h D q hq)
  rw [this, iteratedDeriv_const_sub hj, iteratedDeriv_neg]

/-- For `1 ≤ j ≤ 4`, `u ≠ 0`: `|Δ_q^{(j)}(u)| ≤ 3 C 2^j / (|u|^j q Q)`. -/
theorem abs_iteratedDeriv_deltaW_le {ω : ℝ → ℝ} {Q C : ℝ} (h : DFIOmega ω Q C) (D q : ℕ)
    (hq : 1 ≤ q) (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ 4) (u : ℝ) (hu : u ≠ 0) :
    |iteratedDeriv j (deltaW ω D q) u| ≤ 3 * C * 2 ^ j / (|u| ^ j * (q * Q)) := by
  rw [iteratedDeriv_deltaW h D q hq j hj1, abs_neg]
  exact (abs_iteratedDeriv_bW_le h D q hq j u).trans
    (sum_omega_deriv_le h D q hq j hj |u| (abs_pos.mpr hu))

/-- For `j ≥ 1` and `|u| < q Q`: `Δ_q^{(j)}(u) = 0`. -/
theorem iteratedDeriv_deltaW_eq_zero {ω : ℝ → ℝ} {Q C : ℝ} (h : DFIOmega ω Q C) (D q : ℕ)
    (hq : 1 ≤ q) (j : ℕ) (hj1 : 1 ≤ j) (u : ℝ) (hu : |u| < q * Q) :
    iteratedDeriv j (deltaW ω D q) u = 0 := by
  rw [iteratedDeriv_deltaW h D q hq j hj1, neg_eq_zero, ← abs_nonpos_iff]
  exact (abs_iteratedDeriv_bW_le h D q hq j u).trans
    (sum_omega_deriv_eq_zero h D q hq j |u| hu).le

end FourSquaresCaps
