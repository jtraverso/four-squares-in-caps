/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.Kloosterman

/-!
# Twisted multiplicativity of `S_q(m, c)`

For coprime `r, s` and a Bézout relation `s' s + r' r = 1`:
`S_{rs}(m, c) = S_r(m, s' c) · S_s(m, r' c)` (`expSumS_mul`).

* `stdAddChar_mul_split`: `e_{rs}(j) = e_r(s' j) e_s(r' j)` for integers `j`.
* `expSumS_eq_sum`: `S_q(m, c) = ∑_{a unit} ∑_{b} e_q(a (|b|² − m) + c · b)`.
-/

@[expose] public section

namespace FourSquaresCaps

open ZMod Finset

/-- `e_{rs}(j) = e_r(s' j) · e_s(r' j)` when `s' s + r' r = 1`. -/
theorem stdAddChar_mul_split {r s : ℕ} [NeZero r] [NeZero s] (r' s' : ℤ)
    (hb : s' * s + r' * r = 1) (j : ℤ) :
    (stdAddChar (N := r * s) (j : ZMod (r * s)) : ℂ) =
      stdAddChar (N := r) (((s' * j : ℤ)) : ZMod r) *
        stdAddChar (N := s) (((r' * j : ℤ)) : ZMod s) := by
  rw [stdAddChar_coe, stdAddChar_coe, stdAddChar_coe, ← Complex.exp_add]
  congr 1
  have hr : (r : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne r
  have hs : (s : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne s
  have hb' : (s' : ℂ) * s + r' * r = 1 := by exact_mod_cast hb
  push_cast
  field_simp
  linear_combination (-(j : ℂ)) * hb'

/-- `S_q(m, c)` as a single sum over `a` and `b ∈ (ZMod q)⁴`. -/
theorem expSumS_eq_sum {q : ℕ} [NeZero q] (m : ZMod q) (c : Fin 4 → ZMod q) :
    expSumS m c = ∑ a : (ZMod q)ˣ, ∑ b : Fin 4 → ZMod q,
      (stdAddChar ((a : ZMod q) * (∑ i, b i ^ 2 - m) + ∑ i, c i * b i) : ℂ) := by
  unfold expSumS
  refine Fintype.sum_congr _ _ fun a => ?_
  simp only [gaussQ]
  rw [Fintype.prod_sum, mul_sum]
  refine Fintype.sum_congr _ _ fun b => ?_
  rw [← addChar_sum, ← AddChar.map_add_eq_mul]
  congr 1
  simp only [Fin.sum_univ_four]
  ring

/-- Reindexing by a unit multiple of `a`. -/
theorem sum_units_mul_eq {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) (f : ZMod q → ℂ) :
    ∑ a : (ZMod q)ˣ, f ((u : ZMod q) * a) = ∑ a : (ZMod q)ˣ, f a :=
  Fintype.sum_equiv (Equiv.mulLeft u) _ _ fun a => by simp

/-- **Twisted multiplicativity.** For coprime `r, s` with `s' s + r' r = 1`,
`S_{rs}(m, c) = S_r(m, s' c) · S_s(m, r' c)`. -/
theorem expSumS_mul {r s : ℕ} [NeZero r] [NeZero s] (h : r.Coprime s) (r' s' : ℤ)
    (hb : s' * s + r' * r = 1) (m : ℤ) (c : Fin 4 → ℤ) :
    expSumS (q := r * s) (m : ZMod (r * s)) (fun i => (c i : ZMod (r * s))) =
      expSumS (q := r) (m : ZMod r) (fun i => ((s' * c i : ℤ) : ZMod r)) *
        expSumS (q := s) (m : ZMod s) (fun i => ((r' * c i : ℤ) : ZMod s)) := by
  classical
  set e := ZMod.chineseRemainder h
  let φ₁ : ZMod (r * s) →+* ZMod r := (RingHom.fst _ _).comp e.toRingHom
  let φ₂ : ZMod (r * s) →+* ZMod s := (RingHom.snd _ _).comp e.toRingHom
  have hφ₁ : ∀ y : ZMod (r * s), φ₁ y = ((y.val : ℕ) : ZMod r) := by
    intro y
    conv_lhs => rw [← ZMod.natCast_zmod_val y]
    rw [map_natCast]
  have hφ₂ : ∀ y : ZMod (r * s), φ₂ y = ((y.val : ℕ) : ZMod s) := by
    intro y
    conv_lhs => rw [← ZMod.natCast_zmod_val y]
    rw [map_natCast]
  have hsplit : ∀ y : ZMod (r * s), (stdAddChar y : ℂ) =
      stdAddChar ((s' : ZMod r) * φ₁ y) * stdAddChar ((r' : ZMod s) * φ₂ y) := by
    intro y
    have hy : y = ((y.val : ℤ) : ZMod (r * s)) := by simp
    rw [hφ₁, hφ₂]
    conv_lhs => rw [hy]
    rw [stdAddChar_mul_split r' s' hb]
    push_cast
    ring_nf
  let EU : (ZMod (r * s))ˣ ≃ (ZMod r)ˣ × (ZMod s)ˣ :=
    ((Units.mapEquiv e.toMulEquiv).trans MulEquiv.prodUnits).toEquiv
  let EB : (Fin 4 → ZMod (r * s)) ≃ (Fin 4 → ZMod r) × (Fin 4 → ZMod s) :=
    (Equiv.piCongrRight fun _ => e.toEquiv).trans (Equiv.arrowProdEquivProdArrow _ _ _)
  let g₁ : (ZMod r)ˣ → (Fin 4 → ZMod r) → ℂ := fun a b =>
    stdAddChar ((s' : ZMod r) * ((a : ZMod r) * (∑ i, b i ^ 2 - (m : ZMod r)) +
      ∑ i, (c i : ZMod r) * b i))
  let g₂ : (ZMod s)ˣ → (Fin 4 → ZMod s) → ℂ := fun a b =>
    stdAddChar ((r' : ZMod s) * ((a : ZMod s) * (∑ i, b i ^ 2 - (m : ZMod s)) +
      ∑ i, (c i : ZMod s) * b i))
  have hterm : ∀ (a : (ZMod (r * s))ˣ) (b : Fin 4 → ZMod (r * s)),
      (stdAddChar ((a : ZMod (r * s)) * (∑ i, b i ^ 2 - (m : ZMod (r * s))) +
        ∑ i, (c i : ZMod (r * s)) * b i) : ℂ) = g₁ (EU a).1 (EB b).1 * g₂ (EU a).2 (EB b).2 := by
    intro a b
    rw [hsplit]
    simp only [g₁, g₂, map_add, map_mul, map_sub, map_sum, map_pow, map_intCast]
    rfl
  -- the factor sums are `S_r` and `S_s`
  have hu₁ : IsUnit (s' : ZMod r) := by
    refine isUnit_iff_exists_inv.mpr ⟨(s : ZMod r), ?_⟩
    have := congrArg (Int.cast : ℤ → ZMod r) hb
    push_cast at this
    simpa using this
  have hu₂ : IsUnit (r' : ZMod s) := by
    refine isUnit_iff_exists_inv.mpr ⟨(r : ZMod s), ?_⟩
    have := congrArg (Int.cast : ℤ → ZMod s) hb
    push_cast at this
    simpa using this
  have h₁ : ∑ a : (ZMod r)ˣ, ∑ b : Fin 4 → ZMod r, g₁ a b =
      expSumS (q := r) (m : ZMod r) (fun i => ((s' * c i : ℤ) : ZMod r)) := by
    rw [expSumS_eq_sum]
    let f : ZMod r → ℂ := fun x => ∑ b : Fin 4 → ZMod r,
      stdAddChar (x * (∑ i, b i ^ 2 - (m : ZMod r)) + ∑ i, ((s' * c i : ℤ) : ZMod r) * b i)
    rw [← sum_units_mul_eq hu₁.unit f]
    refine Fintype.sum_congr _ _ fun a => Fintype.sum_congr _ _ fun b => ?_
    simp only [g₁, IsUnit.unit_spec]
    congr 1
    push_cast
    simp only [Fin.sum_univ_four]
    ring
  have h₂ : ∑ a : (ZMod s)ˣ, ∑ b : Fin 4 → ZMod s, g₂ a b =
      expSumS (q := s) (m : ZMod s) (fun i => ((r' * c i : ℤ) : ZMod s)) := by
    rw [expSumS_eq_sum]
    let f : ZMod s → ℂ := fun x => ∑ b : Fin 4 → ZMod s,
      stdAddChar (x * (∑ i, b i ^ 2 - (m : ZMod s)) + ∑ i, ((r' * c i : ℤ) : ZMod s) * b i)
    rw [← sum_units_mul_eq hu₂.unit f]
    refine Fintype.sum_congr _ _ fun a => Fintype.sum_congr _ _ fun b => ?_
    simp only [g₂, IsUnit.unit_spec]
    congr 1
    push_cast
    simp only [Fin.sum_univ_four]
    ring
  rw [← h₁, ← h₂, expSumS_eq_sum]
  calc ∑ a : (ZMod (r * s))ˣ, ∑ b : Fin 4 → ZMod (r * s),
        (stdAddChar ((a : ZMod (r * s)) * (∑ i, b i ^ 2 - (m : ZMod (r * s))) +
          ∑ i, (c i : ZMod (r * s)) * b i) : ℂ)
      = ∑ a : (ZMod (r * s))ˣ, ∑ b : Fin 4 → ZMod (r * s),
          g₁ (EU a).1 (EB b).1 * g₂ (EU a).2 (EB b).2 :=
        Fintype.sum_congr _ _ fun a => Fintype.sum_congr _ _ fun b => hterm a b
    _ = ∑ p : (ZMod r)ˣ × (ZMod s)ˣ, ∑ x : (Fin 4 → ZMod r) × (Fin 4 → ZMod s),
          g₁ p.1 x.1 * g₂ p.2 x.2 :=
        Fintype.sum_equiv EU _ _ fun a => Fintype.sum_equiv EB _ _ fun b => rfl
    _ = _ := by
        rw [Fintype.sum_prod_type]
        simp_rw [Fintype.sum_prod_type, sum_mul_sum]

end FourSquaresCaps
