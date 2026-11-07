/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.GaussSum
public import Mathlib.NumberTheory.Divisors

/-!
# The delta symbol of Duke–Friedlander–Iwaniec (discrete part)

For `ω : ℝ → ℝ` with `ω 0 = 0`, `∑_{d=1}^{D} ω(d) = 1`, and an integer `n` with `|n| ≤ D`:
`1[n = 0] = ∑_{d=1}^{D} d⁻¹ ∑_{a mod d} e_d(a n) (ω(d) − ω(|n|/d))` (`delta_all`).
For `n ≠ 0` the divisor sum `∑_{d ∣ n} (ω(d) − ω(|n|/d))` vanishes by `d ↦ |n|/d`.
-/

@[expose] public section

namespace FourSquaresCaps

open ZMod Finset

/-- The divisor involution: `∑_{d ∣ n} (ω(d) − ω(n/d)) = 0` for `n ≠ 0`. -/
theorem sum_divisors_sub_eq_zero (ω : ℝ → ℝ) (n : ℕ) :
    ∑ d ∈ n.divisors, (ω d - ω ((n : ℝ) / d)) = 0 := by
  rw [sum_sub_distrib, sub_eq_zero]
  have : ∑ d ∈ n.divisors, ω ((n : ℝ) / d) = ∑ d ∈ n.divisors, ω ((n / d : ℕ) : ℝ) := by
    refine sum_congr rfl fun d hd => ?_
    rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd)]
    exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  rw [this, Nat.sum_div_divisors n (fun d => ω (d : ℝ))]

/-- Detection of divisibility: `∑_{a mod d} e_d(a n) = d · 1[d ∣ n]`. -/
theorem sum_stdAddChar_intCast (d : ℕ) [NeZero d] (n : ℤ) :
    ∑ a : ZMod d, (stdAddChar (a * (n : ZMod d)) : ℂ) = if (d : ℤ) ∣ n then (d : ℂ) else 0 := by
  have h := sum_stdAddChar_mul (q := d) (n : ZMod d)
  simp_rw [mul_comm _ (n : ZMod d)]
  simp only [h, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- **The DFI delta identity (all residues).** -/
theorem delta_all (ω : ℝ → ℝ) (hω0 : ω 0 = 0) (D : ℕ)
    (hsum : ∑ k ∈ range D, ω ((k : ℝ) + 1) = 1) (n : ℤ) (hn : n.natAbs ≤ D) :
    ∑ k ∈ range D, ((k : ℂ) + 1)⁻¹ * (∑ a : ZMod (k + 1), (stdAddChar (a * (n : ZMod (k + 1))) : ℂ)) *
      ((ω ((k : ℝ) + 1) - ω (|(n : ℝ)| / ((k : ℝ) + 1)) : ℝ) : ℂ) = if n = 0 then 1 else 0 := by
  have hterm : ∀ k ∈ range D, ((k : ℂ) + 1)⁻¹ *
      (∑ a : ZMod (k + 1), (stdAddChar (a * (n : ZMod (k + 1))) : ℂ)) *
      ((ω ((k : ℝ) + 1) - ω (|(n : ℝ)| / ((k : ℝ) + 1)) : ℝ) : ℂ) =
      if ((k + 1 : ℕ) : ℤ) ∣ n then ((ω ((k : ℝ) + 1) - ω (|(n : ℝ)| / ((k : ℝ) + 1)) : ℝ) : ℂ)
        else 0 := by
    intro k _
    rw [sum_stdAddChar_intCast]
    split_ifs
    · have : ((k + 1 : ℕ) : ℂ) = (k : ℂ) + 1 := by push_cast; ring
      rw [this, inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero k), one_mul]
    · simp
  rw [sum_congr rfl hterm]
  by_cases h0 : n = 0
  · subst h0
    simp only [dvd_zero, if_true, Int.cast_zero, abs_zero, zero_div, hω0, sub_zero]
    exact_mod_cast hsum
  · rw [if_neg h0, ← sum_filter]
    -- the filtered sum is the divisor sum of `|n|`
    have hbij : ∑ k ∈ (range D).filter (fun k => ((k + 1 : ℕ) : ℤ) ∣ n),
        ((ω ((k : ℝ) + 1) - ω (|(n : ℝ)| / ((k : ℝ) + 1)) : ℝ) : ℂ) =
        ∑ d ∈ n.natAbs.divisors, ((ω (d : ℝ) - ω ((n.natAbs : ℝ) / d) : ℝ) : ℂ) := by
      refine sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
      · intro k hk
        simp only [mem_filter, mem_range] at hk
        rw [Nat.mem_divisors]
        exact ⟨Int.natCast_dvd.mp hk.2, Int.natAbs_ne_zero.mpr h0⟩
      · intro a _ b _ h; omega
      · intro d hd
        rw [Nat.mem_divisors] at hd
        have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd.1 (Int.natAbs_pos.mpr h0)
        refine ⟨d - 1, ?_, by omega⟩
        simp only [mem_filter, mem_range]
        have hle : d ≤ n.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr h0) hd.1
        refine ⟨by omega, ?_⟩
        rw [show d - 1 + 1 = d by omega]
        exact Int.natCast_dvd.mpr hd.1
      · intro k _
        push_cast
        rw [Nat.cast_natAbs, Int.cast_abs]
    rw [hbij]
    have := sum_divisors_sub_eq_zero ω n.natAbs
    exact_mod_cast this

/-- The Ramanujan sum `c_{k+1}(n) = ∑_{u unit mod k+1} e_{k+1}(u n)`. -/
noncomputable def ram (k : ℕ) (n : ℤ) : ℂ :=
  ∑ u : (ZMod (k + 1))ˣ, (stdAddChar ((u : ZMod (k + 1)) * (n : ZMod (k + 1))) : ℂ)

/-- `e_q(u n) = e_d(u (d/q) n)` for `q ∣ d`. -/
theorem stdAddChar_dvd {q d : ℕ} [NeZero q] [NeZero d] (hqd : q ∣ d) (x : ℕ) (n : ℤ) :
    (stdAddChar ((x : ZMod q) * (n : ZMod q)) : ℂ) =
      stdAddChar (((x * (d / q) : ℕ) : ZMod d) * (n : ZMod d)) := by
  have h1 : ((x : ZMod q) * (n : ZMod q)) = (((x : ℤ) * n : ℤ) : ZMod q) := by
    rw [Int.cast_mul, Int.cast_natCast]
  have h2 : (((x * (d / q) : ℕ) : ZMod d) * (n : ZMod d)) =
      ((((x * (d / q) : ℕ) : ℤ) * n : ℤ) : ZMod d) := by
    rw [Int.cast_mul, Int.cast_natCast]
  rw [h1, h2, stdAddChar_coe, stdAddChar_coe]
  congr 1
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  obtain ⟨e, rfl⟩ := hqd
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have he : (e : ℂ) ≠ 0 := by
    have := NeZero.ne (q * e)
    exact_mod_cast right_ne_zero_of_mul this
  rw [Nat.mul_div_cancel_left e hq0]
  push_cast
  field_simp

/-- **Reduced fractions.** `∑_{a mod d} e_d(a n) = ∑_{q ∣ d} c_q(n)`, with `d = j + 1`,
`q = k + 1`. -/
theorem sum_ram (j : ℕ) (n : ℤ) :
    ∑ k ∈ (range (j + 1)).filter (fun k => k + 1 ∣ j + 1), ram k n =
      ∑ a : ZMod (j + 1), (stdAddChar (a * (n : ZMod (j + 1))) : ℂ) := by
  classical
  set F := (range (j + 1)).filter (fun k => k + 1 ∣ j + 1) with hF
  have hmemF : ∀ k, k ∈ F ↔ k + 1 ∣ j + 1 := by
    intro k
    simp only [hF, mem_filter, mem_range, and_iff_right_iff_imp]
    intro h; have := Nat.le_of_dvd (Nat.succ_pos j) h; omega
  rw [← sum_coe_sort F]
  simp only [ram]
  refine Eq.trans (Fintype.sum_sigma (fun x : (Σ k : F, (ZMod ((k : ℕ) + 1))ˣ) =>
    (stdAddChar ((x.2 : ZMod ((x.1 : ℕ) + 1)) * (n : ZMod ((x.1 : ℕ) + 1))) : ℂ))).symm ?_
  let φ : (Σ k : F, (ZMod ((k : ℕ) + 1))ˣ) → ZMod (j + 1) := fun x =>
    (((x.2 : ZMod ((x.1 : ℕ) + 1)).val * ((j + 1) / ((x.1 : ℕ) + 1)) : ℕ) : ZMod (j + 1))
  have hlt : ∀ x : (Σ k : F, (ZMod ((k : ℕ) + 1))ˣ),
      (x.2 : ZMod ((x.1 : ℕ) + 1)).val * ((j + 1) / ((x.1 : ℕ) + 1)) < j + 1 := by
    intro x
    obtain ⟨e, he⟩ := (hmemF x.1).mp x.1.2
    have hv := ZMod.val_lt (x.2 : ZMod ((x.1 : ℕ) + 1))
    rw [he, Nat.mul_div_cancel_left e (Nat.succ_pos _)]
    have he0 : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · rw [h] at he; omega
      · exact h
    calc (x.2 : ZMod ((x.1 : ℕ) + 1)).val * e < ((x.1 : ℕ) + 1) * e :=
          Nat.mul_lt_mul_of_pos_right hv he0
      _ = _ := rfl
  have hgcd : ∀ x : (Σ k : F, (ZMod ((k : ℕ) + 1))ˣ),
      Nat.gcd ((x.2 : ZMod ((x.1 : ℕ) + 1)).val * ((j + 1) / ((x.1 : ℕ) + 1))) (j + 1) =
        (j + 1) / ((x.1 : ℕ) + 1) := by
    intro x
    obtain ⟨e, he⟩ := (hmemF x.1).mp x.1.2
    have hcop := ZMod.val_coe_unit_coprime x.2
    rw [he, Nat.mul_div_cancel_left e (Nat.succ_pos _),
      Nat.gcd_mul_right, hcop, one_mul]
  have hinj : Function.Injective φ := by
    rintro ⟨⟨k₁, hk₁⟩, u₁⟩ ⟨⟨k₂, hk₂⟩, u₂⟩ h
    have hnat := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
    rw [Nat.mod_eq_of_lt (hlt _), Nat.mod_eq_of_lt (hlt _)] at hnat
    have hg := congrArg (fun z => Nat.gcd z (j + 1)) hnat
    simp only at hg
    rw [hgcd ⟨⟨k₁, hk₁⟩, u₁⟩, hgcd ⟨⟨k₂, hk₂⟩, u₂⟩] at hg
    simp only at hg
    have hd₁ := (hmemF k₁).mp hk₁
    have hd₂ := (hmemF k₂).mp hk₂
    have hk : k₁ = k₂ := by
      have e1 := Nat.div_mul_cancel hd₁
      have e2 := Nat.div_mul_cancel hd₂
      rw [hg] at e1
      have hpos : 0 < (j + 1) / (k₂ + 1) := Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos j) hd₂)
        (Nat.succ_pos _)
      have : k₁ + 1 = k₂ + 1 := by
        apply Nat.eq_of_mul_eq_mul_left hpos
        rw [e1, e2]
      omega
    subst hk
    simp only at hnat
    have hpos : 0 < (j + 1) / (k₁ + 1) := Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos j) hd₁)
      (Nat.succ_pos _)
    have hv : (u₁ : ZMod (k₁ + 1)).val = (u₂ : ZMod (k₁ + 1)).val :=
      Nat.eq_of_mul_eq_mul_right hpos hnat
    have hu : u₁ = u₂ := Units.ext (ZMod.val_injective _ hv)
    subst hu
    rfl
  have hcard : Fintype.card (Σ k : F, (ZMod ((k : ℕ) + 1))ˣ) = Fintype.card (ZMod (j + 1)) := by
    rw [Fintype.card_sigma, ZMod.card]
    simp only [ZMod.card_units_eq_totient]
    rw [sum_coe_sort F (fun k => Nat.totient (k + 1))]
    conv_rhs => rw [← Nat.sum_totient (j + 1)]
    refine sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
    · intro k hk
      exact Nat.mem_divisors.mpr ⟨(hmemF k).mp hk, Nat.succ_ne_zero j⟩
    · intro a _ b _ h; omega
    · intro d hd
      have hd' := Nat.mem_divisors.mp hd
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd'.1 (Nat.succ_pos j)
      exact ⟨d - 1, (hmemF _).mpr (by rw [show d - 1 + 1 = d by omega]; exact hd'.1),
        by omega⟩
    · intro k _; rfl
  have hbij : Function.Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩
  refine Fintype.sum_bijective φ hbij _ _ fun x => ?_
  obtain ⟨⟨k, hk⟩, u⟩ := x
  have hdvd := (hmemF k).mp hk
  simp only [φ]
  conv_lhs => rw [← ZMod.natCast_zmod_val (u : ZMod (k + 1))]
  exact stdAddChar_dvd hdvd _ n

/-- The DFI weight `Δ_q(u) = ∑_{r=1}^{D} (q r)⁻¹ (ω(q r) − ω(|u|/(q r)))`. -/
noncomputable def deltaW (ω : ℝ → ℝ) (D q : ℕ) (u : ℝ) : ℝ :=
  ∑ r ∈ range D, ((q : ℝ) * ((r : ℝ) + 1))⁻¹ *
    (ω ((q : ℝ) * ((r : ℝ) + 1)) - ω (|u| / ((q : ℝ) * ((r : ℝ) + 1))))

/-- **The DFI delta identity.** If `ω` vanishes on `(-∞, 1)` and on `(D, ∞)`, `∑_{d=1}^{D} ω(d) = 1`
and `|n| ≤ D`, then `1[n = 0] = ∑_{q=1}^{D} c_q(n) Δ_q(n)`. -/
theorem delta_units (ω : ℝ → ℝ) (D : ℕ) (hsmall : ∀ y : ℝ, y < 1 → ω y = 0)
    (hbig : ∀ y : ℝ, (D : ℝ) < y → ω y = 0) (hsum : ∑ k ∈ range D, ω ((k : ℝ) + 1) = 1)
    (n : ℤ) (hn : n.natAbs ≤ D) :
    ∑ k ∈ range D, ram k n * (deltaW ω D (k + 1) n : ℂ) = if n = 0 then 1 else 0 := by
  classical
  rw [← delta_all ω (hsmall 0 one_pos) D hsum n hn]
  set w : ℝ → ℂ := fun d => ((d⁻¹ * (ω d - ω (|(n : ℝ)| / d)) : ℝ) : ℂ) with hw
  have hw0 : ∀ d : ℝ, (D : ℝ) < d → w d = 0 := by
    intro d hd
    have hn' : |(n : ℝ)| ≤ D := by
      rw [← Int.cast_abs, ← Nat.cast_natAbs]; exact_mod_cast hn
    have hdpos : 0 < d := lt_of_le_of_lt (Nat.cast_nonneg D) hd
    simp only [hw, hbig d hd, hsmall (|(n : ℝ)| / d) (by
      rw [div_lt_one hdpos]; linarith), sub_zero, mul_zero, Complex.ofReal_zero]
  -- right side: reduced fractions
  have hR : ∀ j ∈ range D, ((j : ℂ) + 1)⁻¹ *
      (∑ a : ZMod (j + 1), (stdAddChar (a * (n : ZMod (j + 1))) : ℂ)) *
      ((ω ((j : ℝ) + 1) - ω (|(n : ℝ)| / ((j : ℝ) + 1)) : ℝ) : ℂ) =
      ∑ k ∈ (range (j + 1)).filter (fun k => k + 1 ∣ j + 1), ram k n * w ((j : ℝ) + 1) := by
    intro j _
    rw [← sum_ram, ← sum_mul]
    simp only [hw]
    push_cast
    ring
  rw [sum_congr rfl hR]
  rw [sum_comm' (t' := range D)
    (s' := fun k => (range D).filter (fun j => k + 1 ∣ j + 1)) (by
      intro j k
      simp only [mem_range, mem_filter]
      constructor
      · rintro ⟨hj, hk, hdvd⟩; exact ⟨⟨hj, hdvd⟩, by omega⟩
      · rintro ⟨⟨hj, hdvd⟩, hk⟩
        have := Nat.le_of_dvd (Nat.succ_pos j) hdvd
        exact ⟨hj, by omega, hdvd⟩)]
  refine sum_congr rfl fun k hk => ?_
  rw [mem_range] at hk
  simp only [deltaW, Complex.ofReal_sum, mul_sum]
  rw [← sum_filter_add_sum_filter_not (range D) (fun r => (k + 1) * (r + 1) ≤ D)]
  have hzero : ∑ r ∈ (range D).filter (fun r => ¬ (k + 1) * (r + 1) ≤ D),
      ram k n * ((((((k + 1 : ℕ) : ℝ) * ((r : ℝ) + 1))⁻¹ *
        (ω (((k + 1 : ℕ) : ℝ) * ((r : ℝ) + 1)) -
          ω (|((n : ℤ) : ℝ)| / (((k + 1 : ℕ) : ℝ) * ((r : ℝ) + 1)))) : ℝ) : ℂ)) = 0 := by
    refine sum_eq_zero fun r hr => ?_
    simp only [mem_filter, not_le] at hr
    have := hw0 (((k + 1 : ℕ) : ℝ) * ((r : ℝ) + 1)) (by exact_mod_cast hr.2)
    simp only [hw] at this
    rw [this, mul_zero]
  rw [hzero, add_zero]
  refine sum_bij (fun r _ => (k + 1) * (r + 1) - 1) ?_ ?_ ?_ ?_
  · intro r hr
    simp only [mem_filter, mem_range] at hr ⊢
    refine ⟨by have : 0 < (k + 1) * (r + 1) := Nat.mul_pos (by omega) (by omega); omega, ?_⟩
    rw [show (k + 1) * (r + 1) - 1 + 1 = (k + 1) * (r + 1) by
      have := (Nat.mul_pos (by omega) (by omega) : 0 < (k + 1) * (r + 1)); omega]
    exact dvd_mul_right _ _
  · intro a ha b hb h
    have h1 : 0 < (k + 1) * (a + 1) := Nat.mul_pos (by omega) (by omega)
    have h2 : 0 < (k + 1) * (b + 1) := Nat.mul_pos (by omega) (by omega)
    have : (k + 1) * (a + 1) = (k + 1) * (b + 1) := by omega
    have := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) this
    omega
  · intro j hj
    simp only [mem_filter, mem_range] at hj
    obtain ⟨e, he⟩ := hj.2
    have he0 : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · rw [h] at he; omega
      · exact h
    refine ⟨e - 1, ?_, ?_⟩
    · simp only [mem_filter, mem_range]
      rw [show e - 1 + 1 = e by omega, ← he]
      refine ⟨?_, by omega⟩
      have : e ≤ (k + 1) * e := Nat.le_mul_of_pos_left e (Nat.succ_pos k)
      omega
    · rw [show e - 1 + 1 = e by omega, ← he]; omega
  · intro r hr
    have hj : (((k + 1) * (r + 1) - 1 : ℕ) : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) * ((r : ℝ) + 1) := by
      have := (Nat.mul_pos (by omega) (by omega) : 0 < (k + 1) * (r + 1))
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    simp only [hw]
    rw [hj]

end FourSquaresCaps
