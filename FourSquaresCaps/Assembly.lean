/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.Theta
public import FourSquaresCaps.Delta
public import FourSquaresCaps.Kloosterman
public import FourSquaresCaps.Lattice
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Assembly of the delta method with Gaussian weights

* `tsum_pi_prod`: `∑_{x ∈ ℤⁿ} ∏ᵢ fᵢ(xᵢ) = ∏ᵢ ∑_x fᵢ(x)` for absolutely summable `fᵢ`.
* `tsum_weight_exp`: `∑_{x ∈ ℤ⁴} W(x) e(α(|x|² − m)) = e(−α m) ∏ᵢ θᵢ(α)`.
-/

@[expose] public section

namespace FourSquaresCaps

open Complex Finset Real

theorem norm_gTerm (A L α : ℝ) (x : ℤ) :
    ‖gTerm A L α x‖ = ‖gTerm A L 0 x‖ := by
  unfold gTerm
  rw [Complex.norm_exp, Complex.norm_exp]
  congr 1
  simp [sq]

theorem summable_norm_gTerm (A L α : ℝ) (hL : L ≠ 0) :
    Summable (fun x : ℤ => ‖gTerm A L α x‖) :=
  summable_norm_iff.mpr (summable_gTerm A L α hL)

theorem gTerm_eq_mul (A L α : ℝ) (x : ℤ) :
    gTerm A L α x = gTerm A L 0 x * cexp (2 * π * I * α * (x : ℂ) ^ 2) := by
  unfold gTerm
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The Gaussian weight of `x ∈ ℤ⁴` centered at `A`. -/
noncomputable def wt (A : Fin 4 → ℝ) (L : ℝ) (x : Fin 4 → ℤ) : ℂ := ∏ i, gTerm (A i) L 0 (x i)

theorem summable_norm_wt (A : Fin 4 → ℝ) (L : ℝ) (hL : L ≠ 0) :
    Summable (fun x : Fin 4 → ℤ => ‖wt A L x‖) :=
  (tsum_pi_prod (fun i => fun x : ℤ => gTerm (A i) L 0 x)
    (fun i => summable_norm_gTerm _ _ _ hL)).1

/-- `∑_{x ∈ ℤ⁴} W(x) e(α (|x|² − m)) = e(−α m) ∏ᵢ θᵢ(α)`. -/
theorem tsum_wt_exp (A : Fin 4 → ℝ) (L : ℝ) (hL : L ≠ 0) (α : ℝ) (m : ℤ) :
    ∑' x : Fin 4 → ℤ, wt A L x * cexp (2 * π * I * α * ((∑ i, x i ^ 2 - m : ℤ) : ℂ)) =
      cexp (-(2 * π * I * α * m)) * ∏ i, thetaW (A i) L α := by
  have h := (tsum_pi_prod (fun i => fun x : ℤ => gTerm (A i) L α x)
    (fun i => summable_norm_gTerm _ _ _ hL)).2
  unfold thetaW
  rw [← h, ← tsum_mul_left]
  refine tsum_congr fun x => ?_
  simp only [wt, gTerm_eq_mul _ L α, prod_mul_distrib, ← Complex.exp_sum]
  have hE : cexp (2 * π * I * α * ((∑ i, x i ^ 2 - m : ℤ) : ℂ)) =
      cexp (-(2 * π * I * α * m)) * cexp (∑ i, 2 * π * I * α * ((x i : ℤ) : ℂ) ^ 2) := by
    rw [← Complex.exp_add, ← mul_sum]
    congr 1
    push_cast
    ring
  rw [hE]
  ring

theorem norm_e (a : ℝ) (n : ℤ) : ‖cexp (2 * π * I * (a : ℂ) * (n : ℂ))‖ = 1 := by
  rw [show (2 * π * I * (a : ℂ) * (n : ℂ)) = ((2 * π * a * n : ℝ) : ℂ) * I by push_cast; ring]
  exact norm_exp_ofReal_mul_I _

/-- The point `u/q + τ` of the circle. -/
noncomputable def alphaU (k : ℕ) (u : (ZMod (k + 1))ˣ) (τ : ℝ) : ℝ :=
  ((u : ZMod (k + 1)).val : ℝ) / (k + 1) + τ

theorem ram_mul (k : ℕ) (n : ℤ) (F : ℝ → ℂ) :
    ram k n * ∫ τ, F τ * cexp (2 * π * I * (τ : ℂ) * n) =
      ∑ u : (ZMod (k + 1))ˣ, ∫ τ, F τ * cexp (2 * π * I * (alphaU k u τ : ℂ) * n) := by
  unfold ram
  rw [sum_mul]
  refine sum_congr rfl fun u _ => ?_
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  ext τ
  have h : (ZMod.stdAddChar ((u : ZMod (k + 1)) * (n : ZMod (k + 1))) : ℂ) =
      cexp (2 * π * I * (((u : ZMod (k + 1)).val * n : ℤ) : ℂ) / ((k + 1 : ℕ) : ℂ)) := by
    rw [show (u : ZMod (k + 1)) * (n : ZMod (k + 1)) =
      ((((u : ZMod (k + 1)).val : ℤ) * n : ℤ) : ZMod (k + 1)) by
        rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]]
    exact ZMod.stdAddChar_coe _
  rw [h, mul_left_comm, ← Complex.exp_add]
  congr 2
  unfold alphaU
  have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  push_cast
  field_simp

/-- **Assembly.** If `1[n = 0] = ∑_k c_{k+1}(n) h_k(n)` and `h_k(n) = ∫ F_k(τ) e(τ n) dτ`, then
the weighted number of representations is
`∑_k ∑_{u unit} ∫ F_k(τ) e(−α m) ∏ᵢ θᵢ(α) dτ`, `α = u/(k+1) + τ`. -/
theorem count_eq (A : Fin 4 → ℝ) (L : ℝ) (hL : L ≠ 0) (m : ℤ) (D : ℕ) (h : ℕ → ℤ → ℂ)
    (F : ℕ → ℝ → ℂ)
    (hdelta : ∀ n : ℤ, (if n = 0 then (1 : ℂ) else 0) = ∑ k ∈ range D, ram k n * h k n)
    (hF : ∀ k (n : ℤ), h k n = ∫ τ, F k τ * cexp (2 * π * I * (τ : ℂ) * n))
    (hFi : ∀ k, MeasureTheory.Integrable (F k)) :
    ∑' x : Fin 4 → ℤ, (if ∑ i, x i ^ 2 = m then wt A L x else 0) =
      ∑ k ∈ range D, ∑ u : (ZMod (k + 1))ˣ, ∫ τ, F k τ *
        (cexp (-(2 * π * I * (alphaU k u τ : ℂ) * m)) *
          ∏ i, thetaW (A i) L (alphaU k u τ)) := by
  classical
  -- the integrand
  let f : ℕ → ∀ k : ℕ, (ZMod (k + 1))ˣ → (Fin 4 → ℤ) → ℝ → ℂ := fun _ k u x τ =>
    wt A L x * (F k τ * cexp (2 * π * I * (alphaU k u τ : ℂ) * ((∑ i, x i ^ 2 - m : ℤ) : ℂ)))
  have hmeas : ∀ k (u : (ZMod (k + 1))ˣ) (n : ℤ), MeasureTheory.AEStronglyMeasurable
      (fun τ : ℝ => cexp (2 * π * I * (alphaU k u τ : ℂ) * (n : ℂ))) := by
    intro k u n
    refine (Continuous.aestronglyMeasurable ?_)
    unfold alphaU
    fun_prop
  have hint : ∀ k (u : (ZMod (k + 1))ˣ) x, MeasureTheory.Integrable (f 0 k u x) := by
    intro k u x
    refine ((hFi k).mul_bdd (hmeas k u _) (c := 1) ?_).const_mul _
    exact Filter.Eventually.of_forall fun τ => (norm_e _ _).le
  have hnorm : ∀ k (u : (ZMod (k + 1))ˣ) x,
      ∫ τ, ‖f 0 k u x τ‖ = ‖wt A L x‖ * ∫ τ, ‖F k τ‖ := by
    intro k u x
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    ext τ
    simp only [f, norm_mul, norm_e, mul_one]
  have hsumx : ∀ k (u : (ZMod (k + 1))ˣ), Summable (fun x => ∫ τ, f 0 k u x τ) := by
    intro k u
    refine Summable.of_norm_bounded ((summable_norm_wt A L hL).mul_right (∫ τ, ‖F k τ‖))
      fun x => ?_
    rw [← hnorm]
    exact MeasureTheory.norm_integral_le_integral_norm _
  have hterm : ∀ x : Fin 4 → ℤ, (if ∑ i, x i ^ 2 = m then wt A L x else 0) =
      ∑ k ∈ range D, ∑ u : (ZMod (k + 1))ˣ, ∫ τ, f 0 k u x τ := by
    intro x
    have h1 : (if ∑ i, x i ^ 2 = m then wt A L x else 0) =
        wt A L x * (if (∑ i, x i ^ 2 - m) = 0 then (1 : ℂ) else 0) := by
      by_cases hx : ∑ i, x i ^ 2 = m <;> simp [hx, sub_eq_zero]
    rw [h1, hdelta, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [hF, ram_mul, mul_sum]
    refine sum_congr rfl fun u _ => ?_
    rw [← MeasureTheory.integral_const_mul]
  rw [tsum_congr hterm, Summable.tsum_finsetSum fun k _ =>
    summable_sum fun u _ => hsumx k u]
  refine sum_congr rfl fun k _ => ?_
  rw [Summable.tsum_finsetSum fun u _ => hsumx k u]
  refine sum_congr rfl fun u _ => ?_
  rw [MeasureTheory.integral_tsum_of_summable_integral_norm (hint k u) (by
    simp_rw [hnorm]; exact (summable_norm_wt A L hL).mul_right _)]
  congr 1
  ext τ
  simp only [f]
  rw [← tsum_wt_exp A L hL, ← tsum_mul_left]
  refine tsum_congr fun x => ?_
  ring

theorem summable_norm_mTerm (A L t : ℝ) (hL : L ≠ 0) (q : ℕ) [NeZero q] :
    Summable (fun n : ℤ => ‖mTerm A L t q n‖) := by
  have haq_re := re_aq_pos L t hL q
  set aq := (q : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * t) with haq
  have haq0 : aq ≠ 0 := fun h => by rw [h, zero_re] at haq_re; exact lt_irrefl 0 haq_re
  have hre : 0 < (1 / aq).re := by
    rw [one_div, inv_re]; exact div_pos haq_re (normSq_pos.mpr haq0)
  refine summable_norm_iff.mpr ((summable_cexp_quad (1 / aq) (- 2 * π * (I * q * A / L ^ 2) / aq)
    (-π * (I * q * A / L ^ 2) ^ 2 / aq - π * A ^ 2 / L ^ 2) hre).congr fun n => ?_)
  unfold mTerm
  congr 1
  rw [← haq]
  ring

/-- **Expansion in `c`.** For `q = k + 1`:
`∑_u e(−α m) ∏ᵢ θᵢ(α) = e(−τ m) a_q^{-2} ∑_{c ∈ ℤ⁴} S_q(m, c) ∏ᵢ Mᵢ(cᵢ)`. -/
theorem sum_units_theta (A : Fin 4 → ℝ) (L : ℝ) (hL : L ≠ 0) (k : ℕ) (m : ℤ) (τ : ℝ) :
    ∑ u : (ZMod (k + 1))ˣ, cexp (-(2 * π * I * (alphaU k u τ : ℂ) * m)) *
        ∏ i, thetaW (A i) L (alphaU k u τ) =
      cexp (-(2 * π * I * (τ : ℂ) * m)) *
        (1 / (((k + 1 : ℕ) : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * τ)) ^ (1 / 2 : ℂ)) ^ 4 *
        ∑' c : Fin 4 → ℤ, expSumS (m : ZMod (k + 1)) (fun i => (c i : ZMod (k + 1))) *
          ∏ i, mTerm (A i) L τ (k + 1) (c i) := by
  classical
  set C := 1 / (((k + 1 : ℕ) : ℂ) ^ 2 * (1 / L ^ 2 - 2 * I * τ)) ^ (1 / 2 : ℂ) with hC
  have hG : ∀ (u : (ZMod (k + 1))ˣ) (i : Fin 4), Summable (fun n : ℤ =>
      ‖gaussQ (u : ZMod (k + 1)) (n : ZMod (k + 1)) * mTerm (A i) L τ (k + 1) n‖) := by
    intro u i
    refine Summable.of_norm_bounded
      ((summable_norm_mTerm (A i) L τ hL (k + 1)).mul_left (Real.sqrt (2 * (k + 1 : ℕ))))
      fun n => ?_
    rw [norm_norm, norm_mul]
    gcongr
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (norm_sq_gaussQ_le _ _ u.isUnit)
  have hθ : ∀ (u : (ZMod (k + 1))ˣ) (i : Fin 4), thetaW (A i) L (alphaU k u τ) =
      C * ∑' n : ℤ, gaussQ (u : ZMod (k + 1)) (n : ZMod (k + 1)) * mTerm (A i) L τ (k + 1) n := by
    intro u i
    have h := thetaW_rat (A i) L τ hL (k + 1) ((u : ZMod (k + 1)).val : ℤ)
    have hα : alphaU k u τ = ((((u : ZMod (k + 1)).val : ℤ) : ℝ)) / ((k + 1 : ℕ) : ℝ) + τ := by
      unfold alphaU; push_cast; ring
    rw [hα, h, hC]
    congr 2
    ext n
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hprod : ∀ u : (ZMod (k + 1))ˣ, ∏ i, thetaW (A i) L (alphaU k u τ) =
      C ^ 4 * ∑' c : Fin 4 → ℤ, ∏ i, (gaussQ (u : ZMod (k + 1)) (c i : ZMod (k + 1)) *
        mTerm (A i) L τ (k + 1) (c i)) := by
    intro u
    simp_rw [hθ u]
    rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin,
      (tsum_pi_prod (fun i => fun n : ℤ => gaussQ (u : ZMod (k + 1)) (n : ZMod (k + 1)) *
        mTerm (A i) L τ (k + 1) n) (hG u)).2]
  have hsumc : ∀ u : (ZMod (k + 1))ˣ, Summable (fun c : Fin 4 → ℤ =>
      ∏ i, (gaussQ (u : ZMod (k + 1)) (c i : ZMod (k + 1)) * mTerm (A i) L τ (k + 1) (c i))) :=
    fun u => summable_norm_iff.mp (tsum_pi_prod (fun i => fun n : ℤ =>
      gaussQ (u : ZMod (k + 1)) (n : ZMod (k + 1)) * mTerm (A i) L τ (k + 1) n) (hG u)).1
  have hphase : ∀ u : (ZMod (k + 1))ˣ, cexp (-(2 * π * I * (alphaU k u τ : ℂ) * m)) =
      cexp (-(2 * π * I * (τ : ℂ) * m)) * ZMod.stdAddChar (-((m : ZMod (k + 1)) * (u : ZMod (k + 1)))) := by
    intro u
    have : -((m : ZMod (k + 1)) * (u : ZMod (k + 1))) =
        ((-(m * ((u : ZMod (k + 1)).val : ℤ)) : ℤ) : ZMod (k + 1)) := by
      push_cast; rw [ZMod.natCast_zmod_val]
    rw [this, ZMod.stdAddChar_coe, ← Complex.exp_add]
    congr 1
    unfold alphaU
    have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    push_cast
    field_simp
    ring
  have step : ∀ u : (ZMod (k + 1))ˣ, cexp (-(2 * π * I * (alphaU k u τ : ℂ) * m)) *
      ∏ i, thetaW (A i) L (alphaU k u τ) =
      (cexp (-(2 * π * I * (τ : ℂ) * m)) * C ^ 4) * ∑' c : Fin 4 → ℤ,
        (ZMod.stdAddChar (-((m : ZMod (k + 1)) * (u : ZMod (k + 1)))) : ℂ) *
          ∏ i, (gaussQ (u : ZMod (k + 1)) (c i : ZMod (k + 1)) * mTerm (A i) L τ (k + 1) (c i)) := by
    intro u
    rw [hphase, hprod, tsum_mul_left]
    ring
  rw [sum_congr rfl fun u _ => step u, ← mul_sum,
    ← Summable.tsum_finsetSum (fun u _ => (hsumc u).mul_left _)]
  congr 1
  refine tsum_congr fun c => ?_
  unfold expSumS
  rw [sum_mul]
  refine sum_congr rfl fun u _ => ?_
  rw [prod_mul_distrib]
  ring

end FourSquaresCaps
