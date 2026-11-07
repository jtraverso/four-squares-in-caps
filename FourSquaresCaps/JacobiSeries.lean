/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.JacobiField

/-!
# The AEZ identities in `ℚ⟦X⟧`

We transport the field identities of `JacobiField` to the power series ring `ℚ⟦X⟧` through its
fraction field, obtaining (identity (3) of Andrews–Ekhad–Zeilberger)
`θ_n^4 = U_n^4 · W_n` with `U_n ≡ 1` and `W_n ≡ 1 + 8 ∑_{k=1}^{n} (-1)^k X^k/(1+X^k)^2`
modulo `X^{n+1}`.
-/

@[expose] public section

namespace FourSquaresCaps.Jacobi

open Finset PowerSeries

local notation "R" => PowerSeries ℚ

noncomputable section

/-- The fraction field of `ℚ⟦X⟧`. -/
abbrev KF := FractionRing R

/-- The embedding `ℚ⟦X⟧ → KF`. -/
abbrev φ : R →+* KF := algebraMap R KF

theorem φ_injective : Function.Injective φ := IsFractionRing.injective R KF

theorem φ_inv {f : R} (hf : constantCoeff f ≠ 0) : φ f⁻¹ = (φ f)⁻¹ := by
  refine (eq_inv_of_mul_eq_one_right ?_)
  rw [← map_mul, PowerSeries.mul_inv_cancel f hf, map_one]

theorem cc_one_sub {j : ℕ} (hj : 1 ≤ j) : constantCoeff (1 - X ^ j : R) ≠ 0 := by
  rw [map_sub, map_one, map_pow, constantCoeff_X, zero_pow (by omega), sub_zero]
  exact one_ne_zero

theorem cc_one_add (j : ℕ) : constantCoeff (1 + X ^ j : R) ≠ 0 := by
  rw [map_add, map_one, map_pow, constantCoeff_X]
  rcases j with _ | j
  · norm_num
  · rw [zero_pow (by omega), add_zero]; exact one_ne_zero

theorem cc_one_add_sq (j : ℕ) : constantCoeff ((1 + X ^ j) ^ 2 : R) ≠ 0 := by
  rw [map_pow]; exact pow_ne_zero _ (cc_one_add j)

theorem ne_zero_of_cc {f : R} (hf : constantCoeff f ≠ 0) : f ≠ 0 := by
  rintro rfl; exact hf (map_zero _)

/-- `q = X` in the fraction field. -/
abbrev qK : KF := φ X

theorem good_qK : Good qK where
  sub j hj := by
    rw [← map_pow, ← map_one φ, ← map_sub]
    exact (map_ne_zero_iff φ φ_injective).mpr (ne_zero_of_cc (cc_one_sub hj))
  add j := by
    rw [← map_pow, ← map_one φ, ← map_add]
    exact (map_ne_zero_iff φ φ_injective).mpr (ne_zero_of_cc (cc_one_add j))

/-- `(1+X^j)/(1-X^j)`. -/
def rr (j : ℕ) : R := (1 + X ^ j) * (1 - X ^ j)⁻¹

/-- `(1-X^j)/(1+X^j)`. -/
def rr' (j : ℕ) : R := (1 - X ^ j) * (1 + X ^ j)⁻¹

/-- `H_n` as a power series. -/
def Hp (n : ℕ) : R := ∏ j ∈ range n, rr (j + 1)

/-- `H_n⁻¹` as a power series. -/
def Hinv (n : ℕ) : R := ∏ j ∈ range n, rr' (j + 1)

theorem φ_rr (j : ℕ) (hj : 1 ≤ j) : φ (rr j) = (1 + qK ^ j) / (1 - qK ^ j) := by
  unfold rr
  rw [map_mul, φ_inv (cc_one_sub hj), map_add, map_sub, map_one, map_pow, div_eq_mul_inv]

theorem φ_rr' (j : ℕ) : φ (rr' j) = (1 - qK ^ j) / (1 + qK ^ j) := by
  unfold rr'
  rw [map_mul, φ_inv (cc_one_add j), map_add, map_sub, map_one, map_pow, div_eq_mul_inv]

theorem φ_Hp : ∀ n, φ (Hp n) = Hf qK n
  | 0 => by simp [Hp, Hf]
  | n + 1 => by
    rw [Hp, prod_range_succ, map_mul, ← Hp, φ_Hp n, φ_rr _ (by omega), Hf_succ]

theorem φ_Hinv : ∀ n, φ (Hinv n) = (Hf qK n)⁻¹
  | 0 => by simp [Hinv, Hf]
  | n + 1 => by
    rw [Hinv, prod_range_succ, map_mul, ← Hinv, φ_Hinv n, φ_rr', Hf_succ, mul_inv, inv_div]

theorem rr_mul_rr' (j : ℕ) (hj : 1 ≤ j) : rr j * rr' j = 1 := by
  unfold rr rr'
  calc (1 + X ^ j) * (1 - X ^ j)⁻¹ * ((1 - X ^ j) * (1 + X ^ j)⁻¹)
      = ((1 - X ^ j) * (1 - X ^ j)⁻¹) * ((1 + X ^ j) * (1 + X ^ j)⁻¹ : R) := by ring
    _ = 1 := by
      rw [PowerSeries.mul_inv_cancel _ (cc_one_sub hj), PowerSeries.mul_inv_cancel _ (cc_one_add j),
        one_mul]

theorem Hp_mul_Hinv (n : ℕ) : Hp n * Hinv n = 1 := by
  unfold Hp Hinv
  rw [← prod_mul_distrib]
  exact prod_eq_one fun j _ => rr_mul_rr' (j + 1) (by omega)

/-! ### Congruences modulo `X^m` -/

/-- `f ≡ 1 mod X^m`. -/
def C1 (m : ℕ) (f : R) : Prop := X ^ m ∣ f - 1

theorem C1_one (m : ℕ) : C1 m 1 := by simp [C1]

theorem C1_mul {m : ℕ} {f g : R} (hf : C1 m f) (hg : C1 m g) : C1 m (f * g) := by
  unfold C1 at *
  have : f * g - 1 = (f - 1) * g + (g - 1) := by ring
  rw [this]; exact dvd_add (dvd_mul_of_dvd_left hf _) hg

theorem C1_prod {m : ℕ} {ι : Type*} (s : Finset ι) (f : ι → R) (h : ∀ i ∈ s, C1 m (f i)) :
    C1 m (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact C1_one m
  | insert a s ha ih =>
    rw [prod_insert ha]
    exact C1_mul (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi))

theorem C1_rr {m j : ℕ} (hj : 1 ≤ j) (hmj : m ≤ j) : C1 m (rr j) := by
  unfold C1 rr
  have : (1 + X ^ j) * (1 - X ^ j)⁻¹ - 1 = X ^ j * (2 * (1 - X ^ j)⁻¹ : R) := by
    calc (1 + X ^ j) * (1 - X ^ j)⁻¹ - 1
        = (1 + X ^ j) * (1 - X ^ j)⁻¹ - (1 - X ^ j) * (1 - X ^ j)⁻¹ := by
          rw [PowerSeries.mul_inv_cancel _ (cc_one_sub hj)]
      _ = X ^ j * (2 * (1 - X ^ j)⁻¹ : R) := by ring
  rw [this]
  exact dvd_mul_of_dvd_left (pow_dvd_pow X hmj) _

theorem C1_rr' {m j : ℕ} (hmj : m ≤ j) : C1 m (rr' j) := by
  unfold C1 rr'
  have : (1 - X ^ j) * (1 + X ^ j)⁻¹ - 1 = X ^ j * (-2 * (1 + X ^ j)⁻¹ : R) := by
    calc (1 - X ^ j) * (1 + X ^ j)⁻¹ - 1
        = (1 - X ^ j) * (1 + X ^ j)⁻¹ - (1 + X ^ j) * (1 + X ^ j)⁻¹ := by
          rw [PowerSeries.mul_inv_cancel _ (cc_one_add j)]
      _ = X ^ j * (-2 * (1 + X ^ j)⁻¹ : R) := by ring
  rw [this]
  exact dvd_mul_of_dvd_left (pow_dvd_pow X hmj) _

/-- `H_{n+k}/H_n ≡ 1 mod X^{n+1}`. -/
theorem C1_up (n k : ℕ) : C1 (n + 1) (Hp (n + k) * Hinv n) := by
  have : Hp (n + k) = Hp n * ∏ j ∈ Ico n (n + k), rr (j + 1) := by
    unfold Hp; rw [prod_range_mul_prod_Ico _ (by omega)]
  rw [this, mul_comm (Hp n), mul_assoc, Hp_mul_Hinv, mul_one]
  exact C1_prod _ _ fun j hj => C1_rr (by omega) (by rw [mem_Ico] at hj; omega)

/-- `H_{n-k}/H_n ≡ 1 mod X^{n-k+1}` (for `k ≤ n`). -/
theorem C1_down (n k : ℕ) (hk : k ≤ n) : C1 (n - k + 1) (Hp (n - k) * Hinv n) := by
  have : Hinv n = Hinv (n - k) * ∏ j ∈ Ico (n - k) n, rr' (j + 1) := by
    unfold Hinv; rw [prod_range_mul_prod_Ico _ (by omega)]
  rw [this, ← mul_assoc, Hp_mul_Hinv, one_mul]
  exact C1_prod _ _ fun j hj => C1_rr' (by rw [mem_Ico] at hj; omega)

theorem C1_mono {m m' : ℕ} {f : R} (h : m' ≤ m) (hf : C1 m f) : C1 m' f :=
  (pow_dvd_pow X h).trans hf

/-! ### The three series and identity (3) -/

/-- `θ_n = 1 + 2 ∑_{k=1}^{n} (-1)^k X^{k^2}`. -/
def thetaP (n : ℕ) : R := 1 + 2 * ∑ i ∈ range n, (-1) ^ (i + 1) * X ^ ((i + 1) ^ 2)

/-- `∑_{k=0}^{n} 2(-1)^k X^{(n+1)k} H_k/(1+X^k)`. -/
def Up (n : ℕ) : R :=
  ∑ k ∈ range (n + 1), 2 * (-1) ^ k * X ^ ((n + 1) * k) * (1 + X ^ k)⁻¹ * Hp k

/-- `(-1)^k X^k/(1+X^k)^2`. -/
def Ek (k : ℕ) : R := (-1) ^ k * X ^ k * ((1 + X ^ k) ^ 2)⁻¹

/-- The (normalized) left side of (a). -/
def Wp (n : ℕ) : R :=
  1 + 2 * ∑ i ∈ range n, 4 * Ek (i + 1) * ((Hp (n + (i + 1)) * Hinv n) * (Hp (n - (i + 1)) * Hinv n))

/-- `1 + 8 ∑_{k=1}^{n} (-1)^k X^k/(1+X^k)^2`. -/
def Tp (n : ℕ) : R := 1 + 8 * ∑ i ∈ range n, Ek (i + 1)

theorem φ_thetaP (n : ℕ) : φ (thetaP n) = thetaF qK n := by
  simp [thetaP, thetaF, map_ofNat]

theorem thetaP_eq (n : ℕ) : thetaP n = Up n * Hinv n := by
  apply φ_injective
  rw [φ_thetaP, ← lemma_b good_qK n, map_mul, φ_Hinv, Up, map_sum, sum_mul]
  refine sum_congr rfl fun k _ => ?_
  simp only [map_mul, φ_inv (cc_one_add k), φ_Hp, Fb, map_pow, map_neg, map_one, map_add,
    map_ofNat]
  ring

theorem φ_Wp_mul (n : ℕ) : φ (Wp n) * Hf qK n ^ 4 = 1 := by
  rw [← lemma_a good_qK n, Sa]
  have hH := Hf_ne_zero good_qK n
  have h0 : Fa qK n 0 = Hf qK n ^ 4 := by
    unfold Fa
    simp only [pow_zero, mul_one, Nat.sub_zero, add_zero]
    rw [four_div_sq good_qK]; ring
  rw [h0, Wp, map_add, map_one, add_mul, one_mul, map_mul, map_sum, mul_assoc, sum_mul]
  congr 1
  rw [map_ofNat]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  have hc := cc_one_add_sq (i + 1)
  simp only [Ek, Fa, map_mul, map_pow, map_neg, map_one, map_ofNat, φ_inv hc, φ_Hp, φ_Hinv,
    map_add]
  field_simp

theorem Wp_eq (n : ℕ) : Wp n = Hinv n ^ 4 := by
  apply φ_injective
  have h := φ_Wp_mul n
  have hH := pow_ne_zero 4 (Hf_ne_zero good_qK n)
  rw [map_pow, φ_Hinv, inv_pow]
  exact eq_inv_of_mul_eq_one_left h

/-- Identity (3) of AEZ. -/
theorem identity3 (n : ℕ) : thetaP n ^ 4 = Up n ^ 4 * Wp n := by
  rw [thetaP_eq, Wp_eq]; ring

theorem C1_Up (n : ℕ) : C1 (n + 1) (Up n) := by
  unfold C1 Up
  rw [sum_range_succ']
  have h0 : 2 * (-1) ^ 0 * X ^ ((n + 1) * 0) * (1 + X ^ 0)⁻¹ * Hp 0 = (1 : R) := by
    have h2 : (2 : R) * 2⁻¹ = 1 :=
      PowerSeries.mul_inv_cancel _ (by rw [map_ofNat]; norm_num)
    simp only [pow_zero, mul_zero, mul_one, Hp, range_zero, prod_empty, one_add_one_eq_two]
    exact h2
  rw [h0, add_sub_cancel_right]
  refine dvd_sum fun k _ => ?_
  have : X ^ ((n + 1) * (k + 1)) = (X ^ (n + 1) * X ^ ((n + 1) * k) : R) := by
    rw [← pow_add]; congr 1; ring
  rw [this]
  exact ⟨2 * (-1) ^ (k + 1) * X ^ ((n + 1) * k) * (1 + X ^ (k + 1))⁻¹ * Hp (k + 1), by ring⟩

theorem dvd_Wp_sub (n : ℕ) : X ^ (n + 1) ∣ Wp n - Tp n := by
  have e : Wp n - Tp n = ∑ i ∈ range n, 8 * Ek (i + 1) *
      ((Hp (n + (i + 1)) * Hinv n) * (Hp (n - (i + 1)) * Hinv n) - 1) := by
    unfold Wp Tp
    rw [show ∀ a b : R, (1 + 2 * a) - (1 + 8 * b) = 2 * a - 8 * b from fun a b => by ring,
      mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [e]
  refine dvd_sum fun i hi => ?_
  have hi' : i < n := mem_range.mp hi
  have hP : C1 (n - i) ((Hp (n + (i + 1)) * Hinv n) * (Hp (n - (i + 1)) * Hinv n)) :=
    C1_mul (C1_mono (by omega) (C1_up n (i + 1)))
      (C1_mono (by omega) (C1_down n (i + 1) (by omega)))
  have hX : (X ^ (n + 1) : R) = X ^ (i + 1) * X ^ (n - i) := by rw [← pow_add]; congr 1; omega
  rw [hX]
  have : 8 * Ek (i + 1) * ((Hp (n + (i + 1)) * Hinv n) * (Hp (n - (i + 1)) * Hinv n) - 1) =
      X ^ (i + 1) * ((Hp (n + (i + 1)) * Hinv n) * (Hp (n - (i + 1)) * Hinv n) - 1) *
        (8 * (-1) ^ (i + 1) * ((1 + X ^ (i + 1)) ^ 2)⁻¹) := by unfold Ek; ring
  rw [this]
  exact dvd_mul_of_dvd_left (mul_dvd_mul_left _ hP) _

/-- `θ_n^4 ≡ 1 + 8 ∑_{k=1}^{n} (-1)^k X^k/(1+X^k)^2 (mod X^{n+1})`. -/
theorem dvd_theta4_sub (n : ℕ) : X ^ (n + 1) ∣ thetaP n ^ 4 - Tp n := by
  rw [identity3]
  have hU : C1 (n + 1) (Up n ^ 4) := by
    have := C1_Up n
    rw [show Up n ^ 4 = Up n * Up n * Up n * Up n by ring]
    exact C1_mul (C1_mul (C1_mul this this) this) this
  have : Up n ^ 4 * Wp n - Tp n = (Up n ^ 4 - 1) * Wp n + (Wp n - Tp n) := by ring
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_left hU _) (dvd_Wp_sub n)

end

end FourSquaresCaps.Jacobi
