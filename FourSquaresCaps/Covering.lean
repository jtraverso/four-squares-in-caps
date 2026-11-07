/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.MainSplit

/-!
# Representations, the Gaussian weight, and a grid of centers

* `reps m`: the finite set of `x ∈ ℤ⁴` with `|x|² = m`; `countW_eq_sum`.
* `wt_eq`: `W_A(x) = exp(−π |x − A|² / L²)`.
* `exists_grid_point`: every unit vector is within `2/K` of `z/|z|` for some `z ∈ ℤ⁴`,
  `0 < ‖z‖_∞ ≤ K`.
-/

@[expose] public section

namespace FourSquaresCaps

open Finset Real

/-- The representations of `m` as a sum of four squares. -/
noncomputable def reps (m : ℕ) : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun _ => Icc (-(m : ℤ)) m).filter (fun x => ∑ i, x i ^ 2 = m)

theorem mem_reps (m : ℕ) (x : Fin 4 → ℤ) : x ∈ reps m ↔ ∑ i, x i ^ 2 = m := by
  unfold reps
  rw [mem_filter, Fintype.mem_piFinset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i => ?_, h⟩
    have hi : x i ^ 2 ≤ m := by
      rw [← h]
      exact single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (mem_univ i)
    rw [mem_Icc]
    constructor <;> nlinarith [sq_nonneg (x i + 1), sq_nonneg (x i - 1), abs_nonneg (x i)]

theorem wt_eq (A : Fin 4 → ℝ) (L : ℝ) (x : Fin 4 → ℤ) :
    wt A L x = ((Real.exp (-π * ∑ i, ((x i : ℝ) - A i) ^ 2 / L ^ 2) : ℝ) : ℂ) := by
  unfold wt gTerm
  rw [Complex.ofReal_exp, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine sum_congr rfl fun i _ => ?_
  ring

theorem countW_eq_sum (A : Fin 4 → ℝ) (L : ℝ) (m : ℕ) :
    countW A L m = ∑ x ∈ reps m, wt A L x := by
  unfold countW
  rw [tsum_eq_sum (s := reps m) fun x hx => by
    rw [mem_reps] at hx
    rw [if_neg hx]]
  refine sum_congr rfl fun x hx => ?_
  rw [mem_reps] at hx
  simp [hx]

theorem wt_re (A : Fin 4 → ℝ) (L : ℝ) (x : Fin 4 → ℤ) :
    (wt A L x).re = Real.exp (-π * ∑ i, ((x i : ℝ) - A i) ^ 2 / L ^ 2) := by
  rw [wt_eq, Complex.ofReal_re]

/-- **Counting in the box.** If the centers `𝒜` cover all representations within `L`, all lie on
the sphere `|A'|² = |A|²`, and `‖N_A − N_{A'}‖ ≤ ε` for each, then the box of half-width `R`
around `A` contains at least `r₄(m)(e^{−π}/|𝒜| − e^{−π R²/L²}) − ε` representations. -/
theorem box_count_ge (m : ℕ) (A : Fin 4 → ℝ) (L R ε : ℝ) (hL : 0 < L) (hR : 0 ≤ R)
    (𝒜 : Finset (Fin 4 → ℝ)) (h𝒜 : 𝒜.Nonempty)
    (hcov : ∀ x ∈ reps m, ∃ A' ∈ 𝒜, ∑ i, ((x i : ℝ) - A' i) ^ 2 ≤ L ^ 2)
    (hcmp : ∀ A' ∈ 𝒜, ‖countW A L m - countW A' L m‖ ≤ ε) :
    ((reps m).card : ℝ) * (Real.exp (-π) / 𝒜.card - Real.exp (-π * R ^ 2 / L ^ 2)) - ε ≤
      ((reps m).filter (fun x => ∀ i, |(x i : ℝ) - A i| ≤ R)).card := by
  classical
  have hL2 : 0 < L ^ 2 := by positivity
  set Box := (reps m).filter (fun x => ∀ i, |(x i : ℝ) - A i| ≤ R) with hBox
  -- upper bound for `Re N_A`
  have hup : (countW A L m).re ≤ Box.card + (reps m).card * Real.exp (-π * R ^ 2 / L ^ 2) := by
    rw [countW_eq_sum, Complex.re_sum]
    simp_rw [wt_re]
    rw [← sum_filter_add_sum_filter_not (reps m) (fun x => ∀ i, |(x i : ℝ) - A i| ≤ R)]
    gcongr
    · calc ∑ x ∈ Box, Real.exp (-π * ∑ i, ((x i : ℝ) - A i) ^ 2 / L ^ 2)
          ≤ ∑ _x ∈ Box, (1 : ℝ) := sum_le_sum fun x _ => by
            rw [Real.exp_le_one_iff]
            have : 0 ≤ ∑ i, ((x i : ℝ) - A i) ^ 2 / L ^ 2 := sum_nonneg fun i _ => by positivity
            nlinarith [pi_pos]
        _ = Box.card := by simp
    · calc ∑ x ∈ (reps m).filter (fun x => ¬ ∀ i, |(x i : ℝ) - A i| ≤ R),
            Real.exp (-π * ∑ i, ((x i : ℝ) - A i) ^ 2 / L ^ 2)
          ≤ ∑ _x ∈ (reps m).filter (fun x => ¬ ∀ i, |(x i : ℝ) - A i| ≤ R),
              Real.exp (-π * R ^ 2 / L ^ 2) := sum_le_sum fun x hx => by
            simp only [mem_filter, not_forall, not_le] at hx
            obtain ⟨i, hi⟩ := hx.2
            apply Real.exp_le_exp.mpr
            have h1 : R ^ 2 ≤ ((x i : ℝ) - A i) ^ 2 := by
              have := pow_le_pow_left₀ hR hi.le 2
              rwa [sq_abs] at this
            have h2 : ((x i : ℝ) - A i) ^ 2 / L ^ 2 ≤ ∑ j, ((x j : ℝ) - A j) ^ 2 / L ^ 2 :=
              single_le_sum (f := fun j => ((x j : ℝ) - A j) ^ 2 / L ^ 2)
                (fun j _ => by positivity) (mem_univ i)
            have h3 : R ^ 2 / L ^ 2 ≤ ∑ j, ((x j : ℝ) - A j) ^ 2 / L ^ 2 :=
              (div_le_div_of_nonneg_right h1 hL2.le).trans h2
            have h4 := mul_le_mul_of_nonneg_left h3 pi_pos.le
            have e : -π * R ^ 2 / L ^ 2 = -(π * (R ^ 2 / L ^ 2)) := by ring
            rw [e]
            linarith
        _ ≤ (reps m).card * Real.exp (-π * R ^ 2 / L ^ 2) := by
            rw [sum_const, nsmul_eq_mul]
            gcongr
            exact filter_subset _ _
  -- lower bound for the sum over centers
  have hsum : Real.exp (-π) * (reps m).card ≤ ∑ A' ∈ 𝒜, (countW A' L m).re := by
    simp_rw [countW_eq_sum, Complex.re_sum, wt_re]
    rw [sum_comm, mul_comm, ← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun x hx => ?_
    obtain ⟨A', hA', hd⟩ := hcov x hx
    calc Real.exp (-π) ≤ Real.exp (-π * ∑ i, ((x i : ℝ) - A' i) ^ 2 / L ^ 2) := by
          apply Real.exp_le_exp.mpr
          rw [neg_mul, ← sum_div, mul_div_assoc', neg_le_neg_iff, div_le_iff₀ hL2]
          nlinarith [pi_pos]
      _ ≤ ∑ A'' ∈ 𝒜, Real.exp (-π * ∑ i, ((x i : ℝ) - A'' i) ^ 2 / L ^ 2) :=
          single_le_sum (f := fun A'' => Real.exp (-π * ∑ i, ((x i : ℝ) - A'' i) ^ 2 / L ^ 2))
            (fun _ _ => (Real.exp_pos _).le) hA'
  -- pigeonhole
  have hcard : (0 : ℝ) < 𝒜.card := by exact_mod_cast h𝒜.card_pos
  obtain ⟨A', hA', hbig⟩ : ∃ A' ∈ 𝒜, Real.exp (-π) * (reps m).card / 𝒜.card ≤
      (countW A' L m).re := by
    by_contra hcon
    push Not at hcon
    have : ∑ A' ∈ 𝒜, (countW A' L m).re < ∑ _A' ∈ 𝒜, Real.exp (-π) * (reps m).card / 𝒜.card :=
      sum_lt_sum_of_nonempty h𝒜 hcon
    rw [sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hcard.ne'] at this
    linarith
  have hdiff : (countW A' L m).re - (countW A L m).re ≤ ε := by
    have := hcmp A' hA'
    calc (countW A' L m).re - (countW A L m).re = (countW A' L m - countW A L m).re := by simp
      _ ≤ ‖countW A' L m - countW A L m‖ := Complex.re_le_norm _
      _ = ‖countW A L m - countW A' L m‖ := norm_sub_rev _ _
      _ ≤ ε := this
  have : ((reps m).card : ℝ) * (Real.exp (-π) / 𝒜.card) = Real.exp (-π) * (reps m).card / 𝒜.card := by
    ring
  nlinarith [hup, hbig, hdiff, this]

/-- Grid of integer vectors with `0 < ‖z‖_∞ ≤ K`. -/
noncomputable def gridZ (K : ℕ) : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun _ => Icc (-(K : ℤ)) K).filter (· ≠ 0)

/-- Euclidean norm of an integer vector. -/
noncomputable def zn (z : Fin 4 → ℤ) : ℝ := Real.sqrt (∑ i, ((z i : ℝ)) ^ 2)

/-- The centers `X z/|z|`. -/
noncomputable def centers (X : ℝ) (K : ℕ) : Finset (Fin 4 → ℝ) :=
  (gridZ K).image fun z i => X * z i / zn z

theorem zn_pos {z : Fin 4 → ℤ} (hz : z ≠ 0) : 0 < zn z := by
  unfold zn
  apply Real.sqrt_pos.mpr
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h; push Not at h; exact hz (funext h)
  have : 0 < ((z i : ℝ)) ^ 2 := by positivity
  exact lt_of_lt_of_le this (single_le_sum (f := fun j => ((z j : ℝ)) ^ 2)
    (fun j _ => sq_nonneg _) (mem_univ i))

theorem centers_sq (X : ℝ) (K : ℕ) : ∀ A' ∈ centers X K, ∑ i, A' i ^ 2 = X ^ 2 := by
  intro A' hA'
  unfold centers at hA'
  rw [mem_image] at hA'
  obtain ⟨z, hz, rfl⟩ := hA'
  have hz0 : z ≠ 0 := (mem_filter.mp hz).2
  have hn := zn_pos hz0
  have hn2 : zn z ^ 2 = ∑ i, ((z i : ℝ)) ^ 2 := Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)
  simp only [div_pow, mul_pow, ← sum_div, ← mul_sum]
  rw [← hn2]
  field_simp

theorem centers_abs (X : ℝ) (hX : 0 ≤ X) (K : ℕ) : ∀ A' ∈ centers X K, ∀ i, |A' i| ≤ X := by
  intro A' hA' i
  have h := centers_sq X K A' hA'
  have : A' i ^ 2 ≤ X ^ 2 := by
    rw [← h]; exact single_le_sum (f := fun j => A' j ^ 2) (fun j _ => sq_nonneg _) (mem_univ i)
  exact abs_le_of_sq_le_sq' this hX |>.elim (fun h1 h2 => abs_le.mpr ⟨h1, h2⟩) |> fun h => h

theorem card_centers_le (X : ℝ) (K : ℕ) : ((centers X K).card : ℝ) ≤ (2 * K + 1) ^ 4 := by
  unfold centers gridZ
  have h1 := card_image_le (s := (Fintype.piFinset fun _ : Fin 4 => Icc (-(K : ℤ)) K).filter (· ≠ 0))
    (f := fun z i => X * z i / zn z)
  have h2 := Finset.card_filter_le (Fintype.piFinset fun _ : Fin 4 => Icc (-(K : ℤ)) K) (· ≠ 0)
  rw [Fintype.card_piFinset, prod_const, Int.card_Icc, card_univ, Fintype.card_fin] at h2
  have h3 : ((K : ℤ) + 1 - -(K : ℤ)).toNat = 2 * K + 1 := by omega
  rw [h3] at h2
  exact_mod_cast h1.trans h2

/-- **Grid covering.** Every `x` with `|x| = X` is within `2X/K` of a center. -/
theorem grid_cover (X : ℝ) (hX : 0 < X) (K : ℕ) (hK : 2 ≤ K) (x : Fin 4 → ℝ)
    (hx : ∑ i, x i ^ 2 = X ^ 2) :
    ∃ A' ∈ centers X K, ∑ i, (x i - A' i) ^ 2 ≤ (2 * X / K) ^ 2 := by
  have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < K := by linarith
  set z : Fin 4 → ℤ := fun i => round ((K : ℝ) * (x i / X)) with hzdef
  let toE : (Fin 4 → ℝ) → EuclideanSpace ℝ (Fin 4) := fun f => WithLp.toLp 2 f
  have hnorm : ∀ f : Fin 4 → ℝ, ‖toE f‖ ^ 2 = ∑ i, f i ^ 2 := by
    intro f; rw [EuclideanSpace.real_norm_sq_eq]
  set U := toE fun i => x i / X with hU
  set Zv := toE fun i => (z i : ℝ) with hZv
  have hs : ∑ i, (x i / X) ^ 2 = 1 := by
    simp only [div_pow]; rw [← sum_div, hx, div_self (by positivity)]
  have hU1 : ‖U‖ = 1 := by
    have : ‖U‖ ^ 2 = 1 := by rw [hU, hnorm, hs]
    nlinarith [norm_nonneg U, sq_nonneg (‖U‖ - 1)]
  set V := (K : ℝ) • U - Zv with hV
  have hV1 : ‖V‖ ≤ 1 := by
    have hc : ∀ i, |(K : ℝ) * (x i / X) - z i| ≤ 1 / 2 := fun i => by
      rw [hzdef]; exact abs_sub_round _
    have : ‖V‖ ^ 2 ≤ 1 := by
      have e : V = toE fun i => (K : ℝ) * (x i / X) - z i := rfl
      rw [e, hnorm]
      calc ∑ i, ((K : ℝ) * (x i / X) - z i) ^ 2 ≤ ∑ _i : Fin 4, (1 / 2 : ℝ) ^ 2 :=
            sum_le_sum fun i _ => by
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hc i) 2
        _ = 1 := by simp; norm_num
    nlinarith [norm_nonneg V]
  have hZn : zn z = ‖Zv‖ := by
    unfold zn; rw [EuclideanSpace.norm_eq]; simp [hZv, toE]
  have hdiff : |‖Zv‖ - K| ≤ ‖V‖ := by
    have : ‖(K : ℝ) • U‖ = K := by rw [norm_smul, hU1, mul_one, Real.norm_of_nonneg hK0.le]
    rw [← this, abs_sub_comm, hV]
    exact abs_norm_sub_norm_le _ _
  have hn1 : (K : ℝ) - 1 ≤ ‖Zv‖ := by
    have := (abs_le.mp (hdiff.trans hV1)).1; linarith
  have hn0 : 0 < ‖Zv‖ := by linarith
  have hz0 : z ≠ 0 := by
    intro h
    have : Zv = 0 := by ext i; simp [hZv, toE, h]
    rw [this, norm_zero] at hn0; exact lt_irrefl 0 hn0
  have hzK : ∀ i, |z i| ≤ K := by
    intro i
    have hui : |x i / X| ≤ 1 := by
      have h1 : (x i / X) ^ 2 ≤ 1 := by
        rw [← hs]
        exact single_le_sum (f := fun j => (x j / X) ^ 2) (fun j _ => sq_nonneg _) (mem_univ i)
      rw [← abs_one, ← sq_le_sq]; simpa using h1
    have h2 : |(K : ℝ) * (x i / X)| ≤ K := by
      rw [abs_mul, abs_of_pos hK0]; nlinarith [abs_nonneg (x i / X)]
    have h3 : |((z i : ℤ) : ℝ)| < K + 1 := by
      have := abs_sub_round ((K : ℝ) * (x i / X))
      have := abs_sub_abs_le_abs_sub ((z i : ℤ) : ℝ) ((K : ℝ) * (x i / X))
      rw [abs_sub_comm] at this
      simp only [hzdef] at *
      linarith
    have : |z i| < (K : ℤ) + 1 := by exact_mod_cast h3
    omega
  refine ⟨fun i => X * z i / zn z, ?_, ?_⟩
  · unfold centers
    refine mem_image.mpr ⟨z, ?_, rfl⟩
    unfold gridZ
    rw [mem_filter, Fintype.mem_piFinset]
    exact ⟨fun i => mem_Icc.mpr (abs_le.mp (hzK i)), hz0⟩
  · -- `x − A' = X (U − Zv/‖Zv‖)`
    have key : ‖U - ‖Zv‖⁻¹ • Zv‖ ≤ 2 / K := by
      have e : U - ‖Zv‖⁻¹ • Zv = (K : ℝ)⁻¹ • (V + (1 - K / ‖Zv‖) • Zv) := by
        ext j
        simp only [hV, PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
        field_simp
        ring
      rw [e, norm_smul, Real.norm_of_nonneg (by positivity)]
      have h1 : |1 - K / ‖Zv‖| * ‖Zv‖ = |‖Zv‖ - K| := by
        rw [← abs_of_pos hn0, ← abs_mul, abs_of_pos hn0]
        congr 1; field_simp
      calc (K : ℝ)⁻¹ * ‖V + (1 - K / ‖Zv‖) • Zv‖ ≤ (K : ℝ)⁻¹ * (‖V‖ + |1 - K / ‖Zv‖| * ‖Zv‖) := by
            gcongr
            exact (norm_add_le _ _).trans (by rw [norm_smul, Real.norm_eq_abs])
        _ ≤ (K : ℝ)⁻¹ * (1 + 1) := by rw [h1]; gcongr; exact hdiff.trans hV1
        _ = 2 / K := by ring
    have hx' : ∑ i, (x i - X * z i / zn z) ^ 2 = X ^ 2 * ‖U - ‖Zv‖⁻¹ • Zv‖ ^ 2 := by
      have e : U - ‖Zv‖⁻¹ • Zv = toE fun i => x i / X - ‖Zv‖⁻¹ * z i := rfl
      rw [e, hnorm, mul_sum, hZn]
      refine sum_congr rfl fun i _ => ?_
      field_simp
    rw [hx']
    calc X ^ 2 * ‖U - ‖Zv‖⁻¹ • Zv‖ ^ 2 ≤ X ^ 2 * (2 / K) ^ 2 := by
          gcongr
      _ = (2 * X / K) ^ 2 := by ring

end FourSquaresCaps
