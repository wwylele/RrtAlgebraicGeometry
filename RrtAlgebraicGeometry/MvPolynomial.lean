/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
import Mathlib

/-! -/

open MvPolynomial

noncomputable section

instance {σ R : Type*} [CommSemiring R] [NoZeroDivisors R] [Nontrivial R] :
    (MvPolynomial.idealOfVars σ R).IsPrime where
  ne_top' := by
    rw [Ideal.ne_top_iff_one]
    intro h
    have h : 1 ∈ (idealOfVars σ R) ^ 1 := by simpa using h
    rw [MvPolynomial.mem_pow_idealOfVars_iff] at h
    specialize h 0 (by simp)
    simp at h
  mem_or_mem' {x y} h := by
    simp_rw [MvPolynomial.idealOfVars, ← Set.image_univ, MvPolynomial.mem_ideal_span_X_image,
      mem_support_iff] at h ⊢
    contrapose! h
    obtain ⟨⟨m, hm, hm0⟩, ⟨n, hn, hn0⟩⟩ := h
    obtain rfl : m = 0 := by
      ext i
      exact hm0 i (Set.mem_univ _)
    obtain rfl : n = 0 := by
      ext i
      exact hn0 i (Set.mem_univ _)
    refine ⟨0, ?_, by simp⟩
    rw [← MvPolynomial.constantCoeff_eq] at ⊢ hm hn
    simp [hm, hn]

theorem MvPolynomial.sub_C_eval_mem_ideal {σ R : Type*} [CommRing R] (p : MvPolynomial σ R)
    (f : σ → R) : p - C (p.eval f) ∈ Ideal.span (Set.range fun i ↦ X i - C (f i)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp_all
  | add p q hp hq =>
    convert Ideal.add_mem _ hp hq using 1
    simp_rw [map_add]
    ring
  | mul_X p n hp =>
    obtain h1 := Ideal.mul_mem_right (X n) _ hp
    have h2 : C ((eval f) p) * (X n - C (f n)) ∈ Ideal.span (Set.range fun i ↦ X i - C (f i)) := by
      apply Ideal.mul_mem_left
      apply Ideal.mem_span_range_self
    simp_rw [map_mul, eval_X]
    convert Ideal.add_mem _ h1 h2 using 1
    ring

-- Aristotle
theorem MvPolynomial.eq_zero_of_c_mem_ideal {σ R : Type*} [Finite σ] [CommRing R]
    {f : σ → R} {a : R} (h : C a ∈ Ideal.span (Set.range fun i ↦ X i - C (f i))) :
    a = 0 := by
  rw [Ideal.mem_span] at h
  contrapose! h
  set ϕ : MvPolynomial σ R →+* R := MvPolynomial.eval₂Hom (RingHom.id R) f
  refine ⟨Ideal.comap ϕ ⊥, ?_, ?_⟩
  · simp [Set.range_subset_iff, ϕ]
  · aesop

theorem MvPolynomial.eval_eq_zero_iff_mem_ideal {σ R : Type*} [Finite σ] [CommRing R]
    (p : MvPolynomial σ R) (f : σ → R) :
    p.eval f = 0 ↔ p ∈ Ideal.span (Set.range fun i ↦ X i - C (f i)) := by
  constructor <;> intro h
  · simpa [h] using p.sub_C_eval_mem_ideal f
  obtain h := Ideal.sub_mem _ h (p.sub_C_eval_mem_ideal f)
  rw [sub_sub_cancel] at h
  apply MvPolynomial.eq_zero_of_c_mem_ideal h

-- Aristotle
theorem MvPolynomial.ideal_inj {σ R : Type*} [CommRing R] {f g : σ → R}
    (h : Ideal.span (Set.range fun i ↦ X i - C (f i)) =
      Ideal.span (Set.range fun i ↦ X i - C (g i))) :
    f = g := by
  ext i;
  have h_mem : (MvPolynomial.X i - MvPolynomial.C (f i)) ∈ Ideal.span
      (Set.range (fun j ↦ MvPolynomial.X j - MvPolynomial.C (g j))) :=
    h ▸ Ideal.subset_span (Set.mem_range_self i)
  have h_eval : (MvPolynomial.eval g) (MvPolynomial.X i - MvPolynomial.C (f i)) = 0 := by
    rw [Ideal.mem_span] at h_mem;
    specialize h_mem (RingHom.ker (MvPolynomial.eval g))
    simp_all [Set.range_subset_iff]
  symm
  rw [← sub_eq_zero]
  simpa using h_eval

-- Aristotle
instance MvPolynomial.isMaximal_span {σ R : Type*} [Field R] (f : σ → R) :
    (Ideal.span (Set.range fun i ↦ X i - C (f i))).IsMaximal := by
  set M : Ideal (MvPolynomial σ R) :=
    Ideal.span (Set.range (fun i => MvPolynomial.X i - MvPolynomial.C (f i)))
  set ϕ : MvPolynomial σ R →+* R := MvPolynomial.eval f
  have h_ker : M = RingHom.ker ϕ := by
    refine le_antisymm ?_ ?_
    · exact Ideal.span_le.mpr (Set.range_subset_iff.mpr fun i => by simp [ϕ])
    · intro g hg
      have h_eval : g - MvPolynomial.C (ϕ g) ∈ M := by
        have h_eval : ∀ p : MvPolynomial σ R, p - MvPolynomial.C (ϕ p) ∈ M := by
          intro p
          induction p using MvPolynomial.induction_on with
          | C a => simp_all [ϕ];
          | add p q hp hq =>
            convert Ideal.add_mem _ hp hq using 1
            simp [sub_add_sub_comm]
          | mul_X p n hp =>
            convert Ideal.mul_mem_left M (MvPolynomial.X n) hp
              |> Ideal.add_mem _ (Ideal.mul_mem_left M (MvPolynomial.C (ϕ p))
              (Ideal.subset_span (Set.mem_range_self n))) using 1
            simp_rw [ϕ, map_mul, eval_X]
            ring
        exact h_eval g
      aesop
  have h_surj : Function.Surjective ϕ := by
    intro r
    use MvPolynomial.C r
    simp [ϕ]
  exact h_ker.symm ▸ RingHom.ker_isMaximal_of_surjective ϕ h_surj

def MvPolynomial.order {σ R : Type*} [Fintype σ] [CommRing R] (p : MvPolynomial σ R) : ℕ∞ :=
  (p.support.inf (fun d ↦ ∑ i, d i))

@[simp]
theorem MvPolynomial.order_zero {σ R : Type*} [Fintype σ] [CommRing R] :
    (0 : MvPolynomial σ R).order = ⊤ := by
  simp [order]

@[simp]
theorem MvPolynomial.order_eq_zero_iff {σ R : Type*} [Fintype σ] [CommRing R]
    (p : MvPolynomial σ R) : p.order = ⊤ ↔ p = 0 := by
  simp [order, Finset.inf_eq_top_iff, MvPolynomial.eq_zero_iff]

theorem MvPolynomial.order_toMvPowerSeries {σ R : Type*} [Fintype σ] [CommRing R]
    (p : MvPolynomial σ R) :
    p.toMvPowerSeries.order = p.order := by
  apply le_antisymm
  · rw [order]
    apply Finset.le_inf
    intro d hd
    rw [mem_support_iff] at hd
    convert! MvPowerSeries.order_le hd
    rw [Finsupp.degree_eq_sum]
    norm_cast
  · apply MvPowerSeries.le_order
    intro d hd
    rw [order, Finset.lt_inf_iff (by simp)] at hd
    contrapose! hd
    refine ⟨d, ?_, ?_⟩
    · simpa using hd
    · rw [Finsupp.degree_eq_sum]
      norm_cast

theorem MvPolynomial.le_order_X {σ R : Type*} [Fintype σ] [CommRing R] (i : σ) :
    1 ≤ (X i : MvPolynomial σ R).order := by
  apply Finset.le_inf
  intro j hj
  contrapose! hj
  rw [Order.lt_one_iff, Finset.sum_eq_zero_iff] at hj
  have hj : j = 0 := by
    ext k
    simpa using hj k
  rw [hj]
  simp

theorem MvPolynomial.min_order_le_add {σ R : Type*} [Fintype σ] [CommRing R]
    (p q : MvPolynomial σ R) :
    min p.order q.order ≤ (p + q).order := by
  simp_rw [← MvPolynomial.order_toMvPowerSeries, MvPolynomial.coe_add]
  apply MvPowerSeries.min_order_le_add

theorem MvPolynomial.le_order_mul {σ R : Type*} [Fintype σ] [CommRing R]
    (p q : MvPolynomial σ R) :
    p.order + q.order ≤ (p * q).order := by
  simp_rw [← MvPolynomial.order_toMvPowerSeries, MvPolynomial.coe_mul]
  apply MvPowerSeries.le_order_mul

theorem MvPolynomial.order_mul {σ R : Type*} [Fintype σ] [CommRing R] [NoZeroDivisors R]
    (p q : MvPolynomial σ R) :
    (p * q).order = p.order + q.order := by
  simp_rw [← MvPolynomial.order_toMvPowerSeries, MvPolynomial.coe_mul]
  apply MvPowerSeries.order_mul

theorem MvPolynomial.le_order_prod {σ R ι : Type*} [Fintype σ] [CommRing R]
    (f : ι → MvPolynomial σ R) (s : Finset ι) :
    ∑ i ∈ s, (f i).order ≤ (∏ i ∈ s, f i).order := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi h =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    grw [h, MvPolynomial.le_order_mul]

theorem MvPolynomial.biInf_order_le_sum {σ R ι : Type*} [Fintype σ] [CommRing R]
    (p : ι → MvPolynomial σ R) (s : Finset ι) :
    ⨅ i ∈ s, (p i).order ≤ (∑ i ∈ s, p i).order := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi h =>
    rw [Finset.iInf_insert, Finset.sum_insert hi]
    grw [h]
    apply MvPolynomial.min_order_le_add
