/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.DFIWeight
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# The cut-off DFI weight `h(u) = η(u/T) Δ_q(u)`

* `contDiff_hW`, `hW_eq_zero`: `h` is smooth and vanishes for `|u| > T/2`.
* `abs_iteratedDeriv_hW_four_le`: `|h⁗(u)| ≤ 246 C E /(qQ) · min(|u|^{-4}, (qQ)^{-4})` (for `2qQ ≤ T`).
* `abs_deriv_hW_le`: `|h'(u)| ≤ 6CE/(TqQ) + 6CE/(|u| qQ) · 1[qQ ≤ |u|]`.
-/

@[expose] public section

namespace FourSquaresCaps

open Finset

/-- Hypotheses on the cut-off `η`. -/
structure DFIEta (η : ℝ → ℝ) (E : ℝ) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η
  at_zero : η 0 = 1
  zero_out : ∀ y, 1 / 2 < |y| → η y = 0
  bound : ∀ i ≤ 4, ∀ y, |iteratedDeriv i η y| ≤ E

/-- The cut-off DFI weight. -/
noncomputable def hW (ω η : ℝ → ℝ) (D q : ℕ) (T : ℝ) (u : ℝ) : ℝ :=
  η (T⁻¹ * u) * deltaW ω D q u

theorem contDiff_deltaW {ω : ℝ → ℝ} {Q C : ℝ} (h : DFIOmega ω Q C) (D q : ℕ) (hq : 1 ≤ q) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deltaW ω D q) := by
  have : deltaW ω D q = fun u => aW ω D q - bW ω D q u := funext (deltaW_eq h D q hq)
  rw [this]
  exact contDiff_const.sub (contDiff_bW h D q)

theorem contDiff_hW {ω η : ℝ → ℝ} {Q C E : ℝ} (h : DFIOmega ω Q C) (hη : DFIEta η E)
    (D q : ℕ) (hq : 1 ≤ q) (T : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (hW ω η D q T) :=
  (hη.smooth.comp (contDiff_const.mul contDiff_id)).mul (contDiff_deltaW h D q hq)

theorem hW_eq_zero {ω η : ℝ → ℝ} {E : ℝ} (hη : DFIEta η E) (D q : ℕ) {T : ℝ} (hT : 0 < T)
    (u : ℝ) (hu : T / 2 < |u|) : hW ω η D q T u = 0 := by
  unfold hW
  rw [hη.zero_out _ ?_, zero_mul]
  rw [abs_mul, abs_of_pos (inv_pos.mpr hT), ← div_eq_inv_mul, lt_div_iff₀ hT]
  linarith

theorem iteratedDeriv_eta_comp {η : ℝ → ℝ} {E : ℝ} (hη : DFIEta η E) (T : ℝ) (i : ℕ) (u : ℝ) :
    iteratedDeriv i (fun u => η (T⁻¹ * u)) u = T⁻¹ ^ i * iteratedDeriv i η (T⁻¹ * u) := by
  rw [iteratedDeriv_comp_const_mul (hη.smooth.of_le (by exact_mod_cast le_top))]

/-- Leibniz bound. -/
theorem abs_iteratedDeriv_hW_le {ω η : ℝ → ℝ} {Q C E : ℝ} (h : DFIOmega ω Q C)
    (hη : DFIEta η E) (D q : ℕ) (hq : 1 ≤ q) {T : ℝ} (hT : 0 < T) (j : ℕ) (hj : j ≤ 4)
    (u : ℝ) :
    |iteratedDeriv j (hW ω η D q T) u| ≤ ∑ i ∈ range (j + 1),
      (j.choose i : ℝ) * (T⁻¹ ^ i * E) * |iteratedDeriv (j - i) (deltaW ω D q) u| := by
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => η (T⁻¹ * u)) :=
    hη.smooth.comp (contDiff_const.mul contDiff_id)
  have h1 := norm_iteratedFDeriv_mul_le hf (contDiff_deltaW h D q hq) u
    (n := j) (by exact_mod_cast le_top)
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at h1
  refine (le_of_eq_of_le ?_ h1).trans (sum_le_sum fun i hi => ?_)
  · rfl
  · gcongr
    rw [iteratedDeriv_eta_comp hη, abs_mul, abs_pow, abs_inv, abs_of_pos hT]
    gcongr
    exact hη.bound i (by simp only [mem_range] at hi; omega) _

theorem iteratedDeriv_hW_eq_zero {ω η : ℝ → ℝ} {E : ℝ} (hη : DFIEta η E) (D q : ℕ) {T : ℝ}
    (hT : 0 < T) (j : ℕ) (u : ℝ) (hu : T / 2 < |u|) : iteratedDeriv j (hW ω η D q T) u = 0 := by
  have hev : hW ω η D q T =ᶠ[nhds u] fun _ => 0 := by
    have hopen : IsOpen {v : ℝ | T / 2 < |v|} := isOpen_lt continuous_const continuous_abs
    filter_upwards [hopen.mem_nhds hu] with v hv using hW_eq_zero hη D q hT v hv
  rw [(hev.iteratedDeriv j).eq_of_nhds]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · simp

/-- `|h(u)| ≤ 6 C E / (q Q)`. -/
theorem abs_hW_le {ω η : ℝ → ℝ} {Q C E : ℝ} (h : DFIOmega ω Q C) (hη : DFIEta η E)
    (D q : ℕ) (hq : 1 ≤ q) (T : ℝ) (u : ℝ) : |hW ω η D q T u| ≤ 6 * C * E / (q * Q) := by
  unfold hW
  rw [abs_mul]
  have h0 := hη.bound 0 (by norm_num) (T⁻¹ * u)
  rw [iteratedDeriv_zero] at h0
  have hd := abs_deltaW_le h D q hq u
  calc |η (T⁻¹ * u)| * |deltaW ω D q u| ≤ E * (6 * C / (q * Q)) :=
        mul_le_mul h0 hd (abs_nonneg _) ((abs_nonneg _).trans h0)
    _ = 6 * C * E / (q * Q) := by ring

/-- The bound function `min(|u|^{-4}, (qQ)^{-4})`. -/
noncomputable def b4 (a u : ℝ) : ℝ := if |u| < a then (a ^ 4)⁻¹ else (|u| ^ 4)⁻¹

/-- `|h⁗(u)| ≤ 246 C E /(qQ) · b4(qQ, u)` for `2 q Q ≤ T`. -/
theorem abs_iteratedDeriv_hW_four_le {ω η : ℝ → ℝ} {Q C E : ℝ} (h : DFIOmega ω Q C)
    (hη : DFIEta η E) (D q : ℕ) (hq : 1 ≤ q) {T : ℝ} (hT : 2 * (q * Q) ≤ T) (u : ℝ) :
    |iteratedDeriv 4 (hW ω η D q T) u| ≤ 246 * C * E / (q * Q) * b4 (q * Q) u := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ : 0 < Q := lt_of_lt_of_le one_pos h.one_le
  have hqQ : 0 < (q : ℝ) * Q := by positivity
  have hT0 : 0 < T := by linarith
  have hC := h.C_nonneg
  have hE : 0 ≤ E := (abs_nonneg _).trans (hη.bound 0 (by norm_num) 0)
  have hb4 : 0 ≤ b4 (q * Q) u := by unfold b4; split_ifs <;> positivity
  rcases lt_or_ge (T / 2) |u| with hbig | hsmall
  · rw [iteratedDeriv_hW_eq_zero hη D q hT0 4 u hbig, abs_zero]; positivity
  have hL := abs_iteratedDeriv_hW_le h hη D q hq hT0 4 le_rfl u
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.choose, Nat.sub_self,
    iteratedDeriv_zero] at hL
  norm_num at hL
  have hd0 := abs_deltaW_le h D q hq u
  have hTk : ∀ k : ℕ, (T ^ k)⁻¹ ≤ (((q : ℝ) * Q) ^ k)⁻¹ := fun k =>
    inv_anti₀ (by positivity) (pow_le_pow_left₀ hqQ.le (by linarith) k)
  rcases lt_or_ge |u| (q * Q) with hlt | hge
  · -- only the `i = 4` term survives
    have hz : ∀ k, 1 ≤ k → iteratedDeriv k (deltaW ω D q) u = 0 :=
      fun k hk => iteratedDeriv_deltaW_eq_zero h D q hq k hk u hlt
    have hz1 : deriv (deltaW ω D q) u = 0 := by rw [← iteratedDeriv_one]; exact hz 1 le_rfl
    rw [hz 4 (by norm_num), hz 3 (by norm_num), hz 2 (by norm_num), hz1] at hL
    simp only [abs_zero, mul_zero, zero_add] at hL
    refine hL.trans ?_
    unfold b4; rw [if_pos hlt]
    have hK : 0 ≤ C * E / (q * Q) * (((q : ℝ) * Q) ^ 4)⁻¹ := by positivity
    calc (T ^ 4)⁻¹ * E * |deltaW ω D q u| ≤ (((q : ℝ) * Q) ^ 4)⁻¹ * E * (6 * C / (q * Q)) := by
          gcongr; linarith
      _ = 6 * (C * E / (q * Q) * (((q : ℝ) * Q) ^ 4)⁻¹) := by ring
      _ ≤ 246 * C * E / (q * Q) * (((q : ℝ) * Q) ^ 4)⁻¹ := by
          rw [show 246 * C * E / (q * Q) * (((q : ℝ) * Q) ^ 4)⁻¹ =
            246 * (C * E / (q * Q) * (((q : ℝ) * Q) ^ 4)⁻¹) by ring]
          linarith
  · have hu0 : 0 < |u| := lt_of_lt_of_le hqQ hge
    have hu : u ≠ 0 := abs_pos.mp hu0
    have hdk : ∀ k, 1 ≤ k → k ≤ 4 → |iteratedDeriv k (deltaW ω D q) u| ≤
        3 * C * 2 ^ k / (|u| ^ k * (q * Q)) :=
      fun k hk1 hk => abs_iteratedDeriv_deltaW_le h D q hq k hk1 hk u hu
    unfold b4; rw [if_neg (not_lt.mpr hge)]
    have hTu' : T⁻¹ ≤ |u|⁻¹ := inv_anti₀ hu0 (by linarith)
    have hT0' : 0 ≤ T⁻¹ := (inv_pos.mpr hT0).le
    set U := |u|⁻¹ with hU
    have hUpos : 0 < U := inv_pos.mpr hu0
    have hTkU : ∀ k : ℕ, (T ^ k)⁻¹ ≤ U ^ k := fun k => by
      rw [← inv_pow]; exact pow_le_pow_left₀ hT0' hTu' k
    have t0 : |iteratedDeriv 4 (deltaW ω D q) u| ≤ 48 * C * U ^ 4 / (q * Q) := by
      refine (hdk 4 (by norm_num) le_rfl).trans (le_of_eq ?_)
      rw [hU]; field_simp; ring
    have t1 : |iteratedDeriv 3 (deltaW ω D q) u| ≤ 24 * C * U ^ 3 / (q * Q) := by
      refine (hdk 3 (by norm_num) (by norm_num)).trans (le_of_eq ?_)
      rw [hU]; field_simp; ring
    have t2 : |iteratedDeriv 2 (deltaW ω D q) u| ≤ 12 * C * U ^ 2 / (q * Q) := by
      refine (hdk 2 (by norm_num) (by norm_num)).trans (le_of_eq ?_)
      rw [hU]; field_simp; ring
    have t3 : |deriv (deltaW ω D q) u| ≤ 6 * C * U / (q * Q) := by
      rw [← iteratedDeriv_one]
      refine (hdk 1 (by norm_num) (by norm_num)).trans (le_of_eq ?_)
      rw [hU]; field_simp; ring
    have p1 : 4 * (T⁻¹ * E) * |iteratedDeriv 3 (deltaW ω D q) u| ≤
        4 * (U * E) * (24 * C * U ^ 3 / (q * Q)) := by gcongr
    have p2 : 6 * ((T ^ 2)⁻¹ * E) * |iteratedDeriv 2 (deltaW ω D q) u| ≤
        6 * (U ^ 2 * E) * (12 * C * U ^ 2 / (q * Q)) := by gcongr; exact hTkU 2
    have p3 : 4 * ((T ^ 3)⁻¹ * E) * |deriv (deltaW ω D q) u| ≤
        4 * (U ^ 3 * E) * (6 * C * U / (q * Q)) := by gcongr; exact hTkU 3
    have p4 : (T ^ 4)⁻¹ * E * |deltaW ω D q u| ≤ U ^ 4 * E * (6 * C / (q * Q)) := by
      gcongr; exact hTkU 4
    have p0 : E * |iteratedDeriv 4 (deltaW ω D q) u| ≤ E * (48 * C * U ^ 4 / (q * Q)) := by
      gcongr
    have hU4 : (|u| ^ 4)⁻¹ = U ^ 4 := by rw [hU, inv_pow]
    rw [hU4]
    have : 246 * C * E / (q * Q) * U ^ 4 = E * (48 * C * U ^ 4 / (q * Q)) +
        4 * (U * E) * (24 * C * U ^ 3 / (q * Q)) + 6 * (U ^ 2 * E) * (12 * C * U ^ 2 / (q * Q)) +
        4 * (U ^ 3 * E) * (6 * C * U / (q * Q)) + U ^ 4 * E * (6 * C / (q * Q)) := by ring
    rw [this]
    linarith

/-- `b1(a, u) = 1[a ≤ |u|] / |u|`. -/
noncomputable def b1 (a u : ℝ) : ℝ := if |u| < a then 0 else |u|⁻¹

/-- `|h'(u)| ≤ 6 C E /(qQ) · (b1(qQ, u) + T⁻¹)`. -/
theorem abs_deriv_hW_le {ω η : ℝ → ℝ} {Q C E : ℝ} (h : DFIOmega ω Q C)
    (hη : DFIEta η E) (D q : ℕ) (hq : 1 ≤ q) {T : ℝ} (hT0 : 0 < T) (u : ℝ) :
    |iteratedDeriv 1 (hW ω η D q T) u| ≤ 6 * C * E / (q * Q) * (b1 (q * Q) u + T⁻¹) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ : 0 < Q := lt_of_lt_of_le one_pos h.one_le
  have hqQ : 0 < (q : ℝ) * Q := by positivity
  have hC := h.C_nonneg
  have hE : 0 ≤ E := (abs_nonneg _).trans (hη.bound 0 (by norm_num) 0)
  have hL := abs_iteratedDeriv_hW_le h hη D q hq hT0 1 (by norm_num) u
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.choose, Nat.sub_self,
    iteratedDeriv_zero] at hL
  norm_num at hL
  have hd0 := abs_deltaW_le h D q hq u
  have p2 : T⁻¹ * E * |deltaW ω D q u| ≤ T⁻¹ * E * (6 * C / (q * Q)) := by gcongr
  rw [iteratedDeriv_one]
  unfold b1
  split_ifs with hlt
  · have hz : deriv (deltaW ω D q) u = 0 := by
      rw [← iteratedDeriv_one]; exact iteratedDeriv_deltaW_eq_zero h D q hq 1 le_rfl u hlt
    rw [hz, abs_zero, mul_zero, zero_add] at hL
    refine hL.trans (le_of_le_of_eq p2 ?_)
    ring
  · have hu0 : 0 < |u| := lt_of_lt_of_le hqQ (not_lt.mp hlt)
    have hd1 : |deriv (deltaW ω D q) u| ≤ 6 * C * |u|⁻¹ / (q * Q) := by
      rw [← iteratedDeriv_one]
      refine (abs_iteratedDeriv_deltaW_le h D q hq 1 le_rfl (by norm_num) u
        (abs_pos.mp hu0)).trans (le_of_eq ?_)
      field_simp; ring
    have p1 : E * |deriv (deltaW ω D q) u| ≤ E * (6 * C * |u|⁻¹ / (q * Q)) := by gcongr
    refine hL.trans ?_
    have : 6 * C * E / (q * Q) * (|u|⁻¹ + T⁻¹) =
        E * (6 * C * |u|⁻¹ / (q * Q)) + T⁻¹ * E * (6 * C / (q * Q)) := by ring
    rw [this]
    linarith

end FourSquaresCaps
