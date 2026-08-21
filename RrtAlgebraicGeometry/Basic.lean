/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
import Mathlib

/-! -/

open MvPolynomial

noncomputable section

@[elab_as_elim, induction_eliminator]
theorem Ideal.Quotient.ind {R : Type*} [Ring R] {I : Ideal R} [I.IsTwoSided]
    {motive : (R ⧸ I) → Prop} (mk : ∀ (a : R), motive (Ideal.Quotient.mk I a)) (q : R ⧸ I) :
    motive q :=
  _root_.Quotient.ind mk q

theorem Ideal.Quotient.isLocalRing {R : Type*} [CommRing R] [IsLocalRing R] {I : Ideal R}
    (hI : I ≠ ⊤) : IsLocalRing (R ⧸ I) := by
  have : IsLocalHom (Ideal.Quotient.mk I) := by
    apply isLocalHom_of_le_jacobson_bot
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ (by simp)]
    apply IsLocalRing.le_maximalIdeal hI
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  exact IsLocalRing.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective




/-theorem IsLocalization.AtPrime.to_map_mem_maximal_pow_iff {R : Type u_1} [CommSemiring R]
    (S : Type u_2) [CommSemiring S] [Algebra R S] (I : Ideal R) [hI : I.IsPrime]
    [IsLocalization.AtPrime S I] (x : R) (n : ℕ) (h : IsLocalRing S) :
    (algebraMap R S) x ∈ IsLocalRing.maximalIdeal S ^ n ↔ x ∈ I ^ n := by
  simp
  sorry

theorem IsLocalization.AtPrime.comap_maximalIdeal_pow {R : Type*} [CommSemiring R] (S : Type*)
    [CommSemiring S] [Algebra R S] (I : Ideal R) [hI : I.IsPrime] [IsLocalization.AtPrime S I]
    (n : ℕ) (h : IsLocalRing S) :
    Ideal.comap (algebraMap R S) (IsLocalRing.maximalIdeal S ^ n) = I ^ n := by
  ext x
  simp []
  sorry

def IsLocalization.AtPrime.equivQuotMaximalIdealPow' {R : Type*} [CommRing R] (p : Ideal R)
    [p.IsMaximal] (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
    [IsLocalRing Rₚ] (n : ℕ) :
    R ⧸ p ^ n ≃+* Rₚ ⧸ IsLocalRing.maximalIdeal Rₚ ^ n := by
  refine (Ideal.quotEquivOfEq ?_).trans
    (RingHom.quotientKerEquivOfSurjective
    (f := algebraMap R (Rₚ ⧸ (IsLocalRing.maximalIdeal Rₚ) ^ n)) ?_)
  · rw [IsScalarTower.algebraMap_eq R Rₚ, ← RingHom.comap_ker,
      Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, ← IsLocalization.AtPrime.map_eq_maximalIdeal p,
      ← Ideal.map_pow,]


    sorry
  · sorry

open IsLocalRing in
def IsLocalization.AtPrime.equivQuotMaximalIdeal'
   {R : Type u_7} [CommRing R] (p : Ideal R) [p.IsMaximal] (Rₚ : Type u_8)
   [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ] :
   R ⧸ p ≃+* Rₚ ⧸ maximalIdeal Rₚ := by
  refine (Ideal.quotEquivOfEq ?_).trans
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap R (Rₚ ⧸ maximalIdeal Rₚ)) ?_)
  · rw [IsScalarTower.algebraMap_eq R Rₚ, ← RingHom.comap_ker,
      Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, IsLocalization.AtPrime.comap_maximalIdeal Rₚ p]
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
    let : Field (R ⧸ p) := Ideal.Quotient.field p
    obtain ⟨s', hs⟩ := Ideal.Quotient.mk_surjective (I := p) (Ideal.Quotient.mk p s)⁻¹
    simp only [IsScalarTower.algebraMap_eq R Rₚ (Rₚ ⧸ _),
      Ideal.Quotient.algebraMap_eq, RingHom.comp_apply]
    use x * s'
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    have : algebraMap R Rₚ s ∉ maximalIdeal Rₚ := by
      rw [← Ideal.mem_comap, IsLocalization.AtPrime.comap_maximalIdeal Rₚ p]
      exact s.prop
    refine ((inferInstanceAs <| (maximalIdeal Rₚ).IsPrime).mem_or_mem ?_).resolve_left this
    rw [mul_sub, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mul_cancel_left,
      ← map_mul, ← map_sub, ← Ideal.mem_comap, IsLocalization.AtPrime.comap_maximalIdeal Rₚ p,
      mul_left_comm, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul, hs,
      mul_inv_cancel₀, mul_one, sub_self]
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact s.prop-/

@[simp]
theorem RingEquiv.coe_subringCongr {R : Type u} [Ring R] {s t : Subring R} (h : s = t) (x : s) :
    (RingEquiv.subringCongr h x).val = x.val := rfl

def IsLocalization.AtPrime.equivQuotMaximalIdealPowₐ (k : Type*) [CommSemiring k]
    {R : Type*} [CommRing R] (p : Ideal R) [Algebra k R]
    [p.IsMaximal] (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
    [IsLocalRing Rₚ] [Algebra k Rₚ] [IsScalarTower k R Rₚ] (n : ℕ) :
    (R ⧸ p ^ n) ≃ₐ[k] Rₚ ⧸ IsLocalRing.maximalIdeal Rₚ ^ n :=
  AlgEquiv.ofRingEquiv (f := IsLocalization.AtPrime.equivQuotMaximalIdealPow p Rₚ n) (fun x ↦ by
    change (equivQuotMaximalIdealPow p Rₚ n) ((algebraMap k R) x) =
        (algebraMap k (Rₚ ⧸ IsLocalRing.maximalIdeal Rₚ ^ n)) x
    rw [IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk]
    simp [IsScalarTower.algebraMap_apply k R (Rₚ ⧸ IsLocalRing.maximalIdeal Rₚ ^ n)]
    )

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
theorem MvPolynomial.isMaximal_span {σ R : Type*} [Field R] (f : σ → R) :
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

open Pointwise in
theorem Ideal.span_pow {R : Type u} [CommSemiring R] (S : Set R) (n : ℕ) :
    span S ^ n = span (S ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, ih, span_mul_span]

theorem MvPolynomial.le_order_iff {σ R : Type*} [Fintype σ] [CommRing R] (p : MvPolynomial σ R)
    (n : ℕ) : n ≤ p.order ↔ p ∈ Ideal.span (Set.range X) ^ n where
  mp h := by
    rw [p.as_sum]
    apply Ideal.sum_mem
    intro i hi
    rw [order] at h
    obtain h := h.trans (Finset.inf_le hi)
    norm_cast at h
    rw [MvPolynomial.monomial_eq, Finsupp.prod_pow]
    apply Ideal.mul_mem_left
    suffices ∏ a, X a ^ i a ∈ ∏ a, Ideal.span (Set.range (X : σ → MvPolynomial σ R)) ^ i a by
      apply Set.mem_of_mem_of_subset this
      rw [Finset.prod_pow_eq_pow_sum]
      exact Ideal.pow_le_pow_right h
    apply Ideal.prod_mem_prod
    intro i _
    apply Ideal.pow_mem_pow
    apply Ideal.mem_span_range_self
  mpr h := by
    rw [Ideal.span_pow] at h
    obtain ⟨f, t, ht, hf, h⟩ := Submodule.mem_span_iff_exists_finset_subset.mp h
    rw [← h]
    grw [← MvPolynomial.biInf_order_le_sum]
    suffices ∀ i ∈ t, ↑n ≤ (f i * i).order by
      simpa
    intro i hi
    grw [← MvPolynomial.le_order_mul]
    apply le_add_of_le_right
    obtain hi := Set.mem_of_mem_of_subset hi ht
    simp_rw [Set.mem_pow, List.prod_ofFn] at hi
    obtain ⟨g, rfl⟩ := hi
    grw [← MvPolynomial.le_order_prod]
    rw [show (n : ℕ∞) = ∑ i : Fin n, 1 by simp [Finset.sum_const]]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    obtain h := (g i).prop
    rw [Set.mem_range] at h
    obtain ⟨y, hy⟩ := h
    rw [← hy]
    apply MvPolynomial.le_order_X

def MvPolynomial.restrictTotalDegreeEquiv (σ R : Type*) [Fintype σ] [CommRing R] (n : ℕ) :
    restrictTotalDegree σ R n ≃ₗ[R]
    MvPolynomial σ R ⧸ Ideal.span (Set.range (X : σ → MvPolynomial σ R)) ^ (n + 1) := by
  refine LinearEquiv.ofBijective
    ((Ideal.Quotient.mkₐ R (Ideal.span (Set.range (X : σ → MvPolynomial σ R)) ^ (n + 1))) ∘ₗ
    (restrictTotalDegree σ R n).subtype)
    ⟨?_ , ?_⟩
  · intro p q h
    have h : n + 1 ≤ (p.val - q.val).order := by
      simpa [Ideal.Quotient.eq, ← MvPolynomial.le_order_iff] using h
    suffices (p.val - q.val).order = ⊤ by
      simpa [sub_eq_zero] using this
    norm_cast at ⊢ h
    by_contra! htop
    have h0 : (p - q).val ≠ 0 := by
      contrapose! htop
      simpa using htop
    rw [ENat.ne_top_iff_exists] at htop
    obtain ⟨m, hm⟩ := htop
    rw [← hm] at h
    rw [order] at hm
    have hsupport : ∀ s ∈ ((p - q).val).support, m ≤ ∑ i, (s i : ℕ∞) := Finset.le_inf_iff.mp hm.le
    have hdegree : ((p - q).val).totalDegree ≤ n :=
      (MvPolynomial.mem_restrictTotalDegree _ _ _).mp (p - q).prop
    rw [MvPolynomial.totalDegree, Finset.sup_le_iff] at hdegree
    obtain ⟨s, hs⟩ := MvPolynomial.support_nonempty.mpr h0
    specialize hsupport s hs
    specialize hdegree s hs
    norm_cast at h hsupport
    rw [Finsupp.sum_fintype _ _ (by simp)] at hdegree
    obtain h := (h.trans hsupport).trans hdegree
    simp at h
  · classical
    intro p
    induction p with | mk p
    refine ⟨⟨∑ d ∈ p.support, if (∑ i, d i) ≤ n then monomial d (p.coeff d) else 0, ?_⟩, ?_⟩
    · rw [MvPolynomial.mem_restrictTotalDegree, MvPolynomial.totalDegree]
      apply Finset.sup_le
      intro d hd
      simp only [mem_support_iff, coeff_sum, apply_ite, coeff_zero] at hd
      obtain ⟨e, hesupport, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
      obtain ⟨hn, heq, h0⟩ : ∑ i, e i ≤ n ∧ e = d ∧ coeff e p ≠ 0 := by simpa using he
      rw [heq] at hn
      rw [Finsupp.sum_fintype _ _ (by simp)]
      exact hn
    · suffices ∀ (s : σ →₀ ℕ),
          (∑ x ∈ p.support, if ∑ i, x i ≤ n then if x = s then coeff x p else 0 else 0)
            - coeff s p ≠ 0 →
          (n : ℕ∞) + 1 ≤ ∑ i, s i by
        simpa [-map_sum, Ideal.Quotient.eq, ← MvPolynomial.le_order_iff, order, coeff_sum,
          apply_ite]
      intro s hs
      conv at hs in (fun (_ : σ →₀ ℕ) ↦ _)  =>
        ext d
        rw [← ite_and]
        rw [ite_congr (show (∑ i, d i ≤ n ∧ d = s) = (d = s ∧ ∑ i, d i ≤ n) by rw [and_comm])
          (fun _ ↦ rfl) (fun _ ↦ rfl)]
        rw [ite_and]
      have hs : (if coeff s p = 0 then -coeff s p else if ∑ i, s i ≤ n then 0 else -coeff s p)
        ≠ 0 := by simpa [ite_sub] using hs
      by_cases h : coeff s p = 0
      · simp [h] at hs
      rw [ENat.add_one_le_iff (by simp)]
      norm_cast
      simpa [h] using hs

-- Aristotle
theorem Set.encard_preimage_sum_singleton (σ : Type*) [Fintype σ] (k : ℕ) :
    Set.encard ((fun (d : σ → ℕ) ↦ ∑ i, d i) ⁻¹' {k}) = (Fintype.card σ + k - 1).choose k := by
  let : Fintype ↑((fun (d : σ → ℕ) ↦ ∑ i, d i) ⁻¹' {k}) := by
    refine Fintype.ofFinset ?_ ?_;
    · exact Finset.image ( fun x : Fin (Fintype.card σ) → ℕ => fun i => x (Fintype.equivFin σ i))
        (Finset.filter (fun x : Fin (Fintype.card σ) → ℕ => ∑ i, x i = k) (Finset.Iic (fun _ => k)))
    norm_num [ Finset.ext_iff ];
    intro x; constructor;
    · intro h
      obtain ⟨a, ha₁, ha₂⟩ := h
      have h_sum : ∑ i : σ, x i = ∑ i : Fin (Fintype.card σ), a i := by
        conv_rhs => rw [ ← Equiv.sum_comp ( Fintype.equivFin σ ) ] ;
        rw [ ← ha₂ ];
      rw [ h_sum, ha₁.2 ];
    · intro hx
      use fun i => x (Fintype.equivFin σ |>.symm i);
      have h_sum_eq : ∑ i : Fin (Fintype.card σ), x (Fintype.equivFin σ |>.symm i)
          = ∑ i : σ, x i := Equiv.sum_comp (Fintype.equivFin σ).symm x
      exact ⟨ ⟨ fun i => le_trans ( Finset.single_le_sum (
          fun a _ => Nat.zero_le ( x ( Fintype.equivFin σ |>.symm a ) ) )
          ( Finset.mem_univ i ) ) ( h_sum_eq.le.trans hx.le ), h_sum_eq.trans hx ⟩,
          funext fun i => by simp ⟩;
  convert Set.encard_eq_coe_toFinset_card ↑((fun (d : σ → ℕ) ↦ ∑ i, d i) ⁻¹' {k})
  norm_num
  rw [ Finset.card_image_of_injective ];
  · induction Fintype.card σ generalizing k with
    | zero =>
      cases k <;> simp +decide
    | succ n ih =>
      simp only [Nat.succ_add_sub_one, Fin.sum_univ_succ]
      rw [ show ( Finset.filter ( fun x : Fin ( n + 1 ) → ℕ => x 0 + ∑ i : Fin n, x i.succ = k )
        ( Finset.Iic fun _ => k ) ) = Finset.biUnion
        ( Finset.range ( k + 1 ) ) fun i => Finset.image
        ( fun x : Fin n → ℕ => Fin.cons i x )
        ( Finset.filter ( fun x : Fin n → ℕ => ∑ i : Fin n, x i = k - i )
        ( Finset.Iic fun _ => k - i ) ) from ?_, Finset.card_biUnion ]
      · rw [ Finset.sum_congr rfl fun i hi => Finset.card_image_of_injective _ <| fun x y hxy => by
          simpa [ Fin.ext_iff ] using hxy ];
        rw [ ← Finset.sum_congr rfl fun i hi => ih ( k - i ) ];
        exact Nat.recOn k ( by simp) fun k ih => by
          simp [ Nat.choose, add_comm, add_left_comm, Finset.sum_range_succ' ] at * ;
          linarith;
      · intro i hi j hj hij; simp[ Finset.disjoint_left ] ; aesop;
      · ext x;
        simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_biUnion, Finset.mem_range,
          Order.lt_add_one_iff, Finset.mem_image];
        constructor;
        · intro hx
          use x 0, by
            linarith [ hx.2, Nat.zero_le ( ∑ i : Fin n, x i.succ ) ], fun i => x i.succ, by
            exact ⟨ fun i => Nat.le_sub_of_add_le ( by
              linarith [ hx.1 i.succ,
              Finset.single_le_sum ( fun a _ => Nat.zero_le ( x ( Fin.succ a ) ) )
                ( Finset.mem_univ i ) ] ), eq_tsub_of_add_eq ( by linarith ) ⟩, by
            exact funext fun i => by cases i using Fin.inductionOn <;> rfl;
        · rintro ⟨ a, ha, b, ⟨ hb₁, hb₂ ⟩, rfl ⟩
          exact ⟨ fun i => by
            cases i using Fin.inductionOn
            <;> [ exact Nat.le_trans ( Nat.le_of_lt_succ (by simpa using ha) ) ( Nat.le_refl _ ) ;
            exact le_trans ( hb₁ _ ) ( Nat.sub_le _ _ ) ],
              by simp [ hb₂ ] ; omega ⟩ ;
  · exact fun x y h => funext fun i => by simpa using congr_fun h ( Fintype.equivFin σ |>.symm i ) ;

theorem MvPolynomial.finrank_quot (σ R : Type*) [Fintype σ] [Field R] {n : ℕ} (hn : n ≠ 0) :
    Module.finrank R (MvPolynomial σ R ⧸ Ideal.span (Set.range (X : σ → MvPolynomial σ R)) ^ n) =
    ((n - 1) + Fintype.card σ).choose (n - 1) := by
  rcases isEmpty_or_nonempty σ with hσ | hσ
  · rw [Set.range_eq_empty, Ideal.span_empty, Ideal.bot_pow hn]
    rw [show Module.finrank R (MvPolynomial σ R ⧸ (⊥ : Ideal (MvPolynomial σ R))) =
      Module.finrank R (MvPolynomial σ R ⧸ (⊥ : Submodule R (MvPolynomial σ R))) from rfl]
    rw [LinearEquiv.finrank_eq (Submodule.quotEquivOfEqBot _ rfl)]
    rw [Module.finrank_eq_card_basis (MvPolynomial.basisMonomials σ R)]
    simp
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  rw [← (MvPolynomial.restrictTotalDegreeEquiv σ R m).finrank_eq]
  have hcard (k : ℕ) : Set.encard ((fun (d : σ → ℕ) ↦ ∑ i, d i) ⁻¹' {k}) =
      (k + (Fintype.card σ - 1)).choose k := by
    rw [Set.encard_preimage_sum_singleton]
    rw [add_comm]
    rw [add_tsub_assoc_of_le]
    rw [Nat.one_le_iff_ne_zero]
    simp
  let hequiv (k : ℕ) : (fun (d : σ →₀ ℕ) ↦ d.sum fun x e ↦ e) ⁻¹' {k} ≃
      (fun (d : σ → ℕ) ↦ ∑ i, d i) ⁻¹' {k} :=
      Set.BijOn.equiv (Finsupp.equivFunOnFinite) (by
    refine ⟨?_, by simp, ?_⟩
    · intro d hd
      rw [Set.mem_preimage, Set.mem_singleton_iff, Finsupp.sum_fintype _ _ (by simp)] at hd
      simpa using hd
    · classical
      intro d hd
      rw [Set.mem_image_equiv, Set.mem_preimage, Set.mem_singleton_iff,
        Finsupp.sum_fintype _ _ (by simp)]
      simpa using hd
    )
  have hunion : {d : σ →₀ ℕ | (d.sum fun x e ↦ e) ≤ m} =
      ⋃ k ∈ Set.Icc 0 m, ((fun (d : σ →₀ ℕ) ↦ d.sum fun x e ↦ e) ⁻¹' {k}) := by
    aesop
  have hall : Set.encard {d : σ →₀ ℕ | (d.sum fun x e ↦ e) ≤ m} =
      (m + Fintype.card σ).choose m := by
    rw [hunion]
    rw [Set.Finite.encard_biUnion (by simp) (fun a _ b _ c ↦ by
      apply Disjoint.preimage
      simpa using c)]
    rw [finsum_mem_eq_finite_toFinset_sum _ (by simp)]
    rw [Finset.sum_congr (show _ = Finset.range (m + 1) by ext x; simp) (fun _ _ ↦ rfl)]
    simp_rw [fun k ↦ Set.encard_congr (hequiv k), hcard]
    norm_cast
    conv in fun _ ↦ _ =>
      ext x
      rw [Nat.choose_symm_add]
    rw [Nat.sum_range_add_choose]
    rw [add_assoc, Nat.sub_add_cancel (by simp [Nat.one_le_iff_ne_zero])]
    rw [← Nat.choose_symm_add]
  have : Finite {d : σ →₀ ℕ | (d.sum fun x e ↦ e) ≤ m} := Set.finite_of_encard_eq_coe hall
  let : Fintype {d : σ →₀ ℕ | (d.sum fun x e ↦ e) ≤ m} := Fintype.ofFinite _
  rw [← Set.coe_fintypeCard] at hall
  norm_cast at hall
  rw [restrictTotalDegree, Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport R _)]
  simpa using hall

def MvPolynomial.mult {σ R : Type*} [Fintype σ] [CommRing R] (p : MvPolynomial σ R) (f : σ → R) :
    ℕ∞ := (p.eval₂ C (fun i ↦ X i + C (f i))).order

theorem MvPolynomial.le_mult_mul {σ R : Type*} [Fintype σ] [CommRing R]
    (p q : MvPolynomial σ R) (f : σ → R) :
    p.mult f + q.mult f ≤ (p * q).mult f := by
  unfold mult
  grw [MvPolynomial.le_order_mul]
  simp

theorem MvPolynomial.mult_mul {σ R : Type*} [Fintype σ] [CommRing R] [NoZeroDivisors R]
    (p q : MvPolynomial σ R) (f : σ → R) :
    (p * q).mult f = p.mult f + q.mult f := by
  unfold mult
  rw [← MvPolynomial.order_mul]
  simp

def MvPolynomial.natMult {σ R : Type*} [Fintype σ] [CommRing R] (p : MvPolynomial σ R) (f : σ → R) :
    ℕ := (p.mult f).toNat

def MvPolynomial.translate {σ R : Type*} [Fintype σ] [CommRing R] (f : σ → R) :
  MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R := AlgEquiv.ofAlgHom
    (MvPolynomial.aevalTower (Algebra.ofId R (MvPolynomial σ R)) (fun i ↦ X i + C (f i)))
    (MvPolynomial.aevalTower (Algebra.ofId R (MvPolynomial σ R)) (fun i ↦ X i - C (f i)))
    (by
      ext x i
      simp [-eval₂Hom_C_eq_bind₁]
    )
    (by
      ext x i
      simp [-eval₂Hom_C_eq_bind₁]
    )

def MvPolynomial.quotientTranslate {σ R : Type*} [Fintype σ] [CommRing R] (f : σ → R) (n : ℕ) :
    (MvPolynomial σ R ⧸ Ideal.span (Set.range fun i ↦ X i - C (f i)) ^ n) ≃ₐ[R]
    MvPolynomial σ R ⧸ Ideal.span (Set.range (X : σ → MvPolynomial σ R)) ^ n :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.translate f) (by
    simp only [translate, aevalTower_ofId, Ideal.map_pow, Ideal.map_span, RingHom.coe_coe,
      AlgEquiv.ofAlgHom_apply]
    congr
    ext i
    simp
  )

theorem MvPolynomial.le_mult_iff {σ R : Type*} [Fintype σ] [CommRing R] (p : MvPolynomial σ R)
    (f : σ → R) (n : ℕ) : n ≤ (p.mult f) ↔
    p ∈ Ideal.span (Set.range fun i ↦ X i - C (f i)) ^ n := by
  rw [← Ideal.apply_mem_of_equiv_iff (f := (MvPolynomial.translate f).toRingEquiv), Ideal.map_pow,
    Ideal.map_span, mult]
  convert! MvPolynomial.le_order_iff (MvPolynomial.translate f p) n
  ext x
  simp [MvPolynomial.translate]

theorem MvPolynomial.one_le_mult_iff {σ R : Type*} [Fintype σ] [CommRing R] (p : MvPolynomial σ R)
    (f : σ → R) : 1 ≤ p.mult f ↔ p.eval f = 0 := by
  change (1 : ℕ) ≤ (p.mult f) ↔ p.eval f = 0
  rw [MvPolynomial.le_mult_iff p f 1, MvPolynomial.eval_eq_zero_iff_mem_ideal, pow_one]

theorem MvPolynomial.eval_eq_zero_of_one_le_natMult
    {σ R : Type*} [Fintype σ] [CommRing R] {p : MvPolynomial σ R}
    {f : σ → R} (h : p.natMult f ≠ 0) : p.eval f = 0 := by
  rw [← MvPolynomial.one_le_mult_iff, Order.one_le_iff_ne_zero]
  rw [natMult] at h
  exact (ne_of_apply_ne ENat.toNat fun a ↦ h a.symm).symm

theorem MvPolynomial.finrank_quot' (σ R : Type*) [Fintype σ] [Field R] (f : σ → R)
    {n : ℕ} (hn : n ≠ 0) :
    Module.finrank R (MvPolynomial σ R ⧸ Ideal.span (Set.range fun i ↦ X i - C (f i)) ^ n) =
    ((n - 1) + Fintype.card σ).choose (n - 1) := by
  rw [(MvPolynomial.quotientTranslate f n).toLinearEquiv.finrank_eq]
  exact MvPolynomial.finrank_quot _ _ hn

instance MvPolynomial.finite_quot' (σ R : Type*) [Finite σ] [Field R] (f : σ → R) (n : ℕ) :
    Module.Finite R (MvPolynomial σ R ⧸ Ideal.span (Set.range fun i ↦ X i - C (f i)) ^ n) := by
  let : Fintype σ := Fintype.ofFinite σ
  by_cases hn : n = 0
  · rw [Ideal.pow_eq_top_iff.mpr (by simp [hn])]
    infer_instance
  apply Module.finite_of_finrank_pos
  rw [MvPolynomial.finrank_quot' _ _ _ hn]
  apply Nat.choose_pos
  simp

theorem MvPolynomial.rank_quot' (σ R : Type*) [Fintype σ] [Field R] (f : σ → R)
    {n : ℕ} (hn : n ≠ 0) :
    Module.rank R (MvPolynomial σ R ⧸ Ideal.span (Set.range fun i ↦ X i - C (f i)) ^ n) =
    ((n - 1) + Fintype.card σ).choose (n - 1) := by
  rw [← Module.finrank_eq_rank, MvPolynomial.finrank_quot' σ R f hn]

theorem MvPolynomial.rank_quot'_zero (σ R : Type*) [Field R] (f : σ → R) :
    Module.rank R (MvPolynomial σ R ⧸ Ideal.span (Set.range fun i ↦ X i - C (f i)) ^ 0) = 0 := by
  rw [Ideal.pow_eq_top_iff.mpr (by simp)]
  exact rank_subsingleton' R (MvPolynomial σ R ⧸ ⊤)

variable {𝕜 : Type*} [Field 𝕜]

-- The polynomial ring 𝕜[X,Y], or the ring of polynomial functions over the plane
notation:9000 R "[X,Y]" => MvPolynomial (Fin 2) R

notation R "[X,Y,Z]" => MvPolynomial (Fin 3) R

-- Affine coordinate ring Γ[𝕜, K] for curve K, represents the function ring on the curve
notation "Γ[" 𝕜 "," K "]" => 𝕜[X,Y] ⧸ Ideal.span {K}

instance (K : 𝕜[X,Y]) : CommRing Γ[𝕜, K] :=
  inferInstance

instance (K : 𝕜[X,Y]) : DistribMulAction Γ[𝕜, K] Γ[𝕜, K] :=
  inferInstance

-- The ideal consisting of functions that vanish at a specific point on the curve
def coordRingMaxIdeal (K : 𝕜[X,Y]) (P : Fin 2 → 𝕜) : Ideal Γ[𝕜, K] :=
  Ideal.span { Ideal.Quotient.mk (Ideal.span {K}) (X 0 - C (P 0)),
    Ideal.Quotient.mk (Ideal.span {K}) (X 1 - C (P 1)) }

theorem coordRingMaxIdeal_eq_map (K : 𝕜[X,Y]) (P : Fin 2 → 𝕜) :
    coordRingMaxIdeal K P =
    (Ideal.span {(X 0 - C (P 0)), (X 1 - C (P 1))}).map (Ideal.Quotient.mk (Ideal.span {K})) := by
  rw [coordRingMaxIdeal]
  rw [Ideal.map_span]
  congr
  grind

namespace Th4_1

def phi1 (K : 𝕜[X,Y]) (P : Fin 2 → 𝕜) (hP : K.eval P = 0) : Γ[𝕜, K] →ₐ[𝕜] 𝕜 :=
    Ideal.Quotient.liftₐ (Ideal.span {K})
    (MvPolynomial.aeval P) (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨l, rfl⟩ := ha
    simp [hP]
  )

theorem ker_phi1 (K : 𝕜[X,Y]) (P : Fin 2 → 𝕜) (hP : K.eval P = 0) :
    RingHom.ker (phi1 K P hP) = coordRingMaxIdeal K P := by
  ext x
  induction x with | mk x
  suffices (eval P) x = 0 ↔
    ∃ a b,
    a * ((Ideal.Quotient.mk (Ideal.span {K})) (X 0) -
      (Ideal.Quotient.mk (Ideal.span {K})) (C (P 0))) +
    b * ((Ideal.Quotient.mk (Ideal.span {K})) (X 1) -
      (Ideal.Quotient.mk (Ideal.span {K})) (C (P 1))) =
      (Ideal.Quotient.mk (Ideal.span {K})) x by
    simpa [phi1, coordRingMaxIdeal, Ideal.mem_span_pair]
  suffices (eval P) x = 0 ↔
    ∃ a b,
    (Ideal.Quotient.mk (Ideal.span {K})) a *
      ((Ideal.Quotient.mk (Ideal.span {K})) (X 0) -
        (Ideal.Quotient.mk (Ideal.span {K})) (C (P 0))) +
    (Ideal.Quotient.mk (Ideal.span {K})) b *
      ((Ideal.Quotient.mk (Ideal.span {K})) (X 1) -
        (Ideal.Quotient.mk (Ideal.span {K})) (C (P 1))) =
      (Ideal.Quotient.mk (Ideal.span {K})) x by
    convert this
    constructor <;> rintro ⟨a, b, h⟩
    · induction a with | mk a
      induction b with | mk b
      use a, b
    · use (Ideal.Quotient.mk (Ideal.span {K})) a, (Ideal.Quotient.mk (Ideal.span {K})) b
  simp_rw [← map_sub, ← map_mul, ← map_add, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  constructor
  · intro h
    suffices ∃ a b, a * (X 0 - C (P 0)) + b * (X 1 - C (P 1)) = x by
      obtain ⟨a, b, h⟩ := this
      use a, b
      simp [h]
    suffices x - C (x.eval P) ∈ Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} by
      rw [Ideal.mem_span_pair] at this
      simpa [h] using this
    convert MvPolynomial.sub_C_eval_mem_ideal x P
    aesop
  · rintro ⟨a, b, ⟨l, hl⟩⟩
    rw [sub_eq_iff_comm] at hl
    rw [← hl]
    simp [hP]

theorem phi1_surjective (K : 𝕜[X,Y]) (P : Fin 2 → 𝕜) (hP : K.eval P = 0) :
    Function.Surjective (phi1 K P hP) := by
  apply Ideal.Quotient.lift_surjective_of_surjective
  intro x
  use C x
  simp

-- The quotient on the left represents the ring of functions on a specific point, which
-- intuitively is isomorphic to the field 𝕜 itself.
set_option backward.isDefEq.respectTransparency false in
abbrev phi2 (K : 𝕜[X,Y]) (P : Fin 2 → 𝕜) (hP : K.eval P = 0) :
    (Γ[𝕜, K] ⧸ coordRingMaxIdeal K P) ≃ₐ[𝕜] 𝕜 :=
  AlgEquiv.ofBijective (Ideal.Quotient.liftₐ _ (phi1 K P hP) (by
    simp_rw [← RingHom.mem_ker, ker_phi1]
    simp
  )) ⟨
  by
    intro a b h
    induction a with | mk a
    induction b with | mk b
    simp_rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk, RingHom.coe_coe] at h
    rw [← RingHom.sub_mem_ker_iff, ker_phi1] at h
    rw [Ideal.Quotient.eq]
    exact h,
  by
    apply Ideal.Quotient.lift_surjective_of_surjective
    exact phi1_surjective K P hP⟩

theorem _root_.coordRingMaxIdeal_isMaximal (K : 𝕜[X,Y]) {P : Fin 2 → 𝕜} (hP : K.eval P = 0) :
    (coordRingMaxIdeal K P).IsMaximal := by
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact MulEquiv.isField (Field.toIsField 𝕜) (phi2 K P hP).toMulEquiv

theorem _root_.coordRingMaxIdeal_injOn (K : 𝕜[X,Y]) :
    Set.InjOn (coordRingMaxIdeal K) {P | K.eval P = 0} := by
  intro a ha b hb h
  rw [Set.mem_ofPred_eq] at ha hb
  simp_rw [coordRingMaxIdeal_eq_map] at h
  rw [Ideal.ext_iff] at h
  have h (x : 𝕜[X,Y]) : x ∈ Ideal.span {X 0 - C (a 0), X 1 - C (a 1)} ⊔ Ideal.span {K} ↔
      x ∈ Ideal.span {X 0 - C (b 0), X 1 - C (b 1)} ⊔ Ideal.span {K} := by
    simpa using h (Ideal.Quotient.mk _ x)
  rw [sup_eq_left.mpr (by
    rw [Ideal.span_singleton_le_iff_mem]
    convert MvPolynomial.sub_C_eval_mem_ideal K a
    · aesop
    · simp [ha]
    )] at h
  rw [sup_eq_left.mpr (by
    rw [Ideal.span_singleton_le_iff_mem]
    convert MvPolynomial.sub_C_eval_mem_ideal K b
    · aesop
    · simp [hb]
    )] at h
  rw [← Ideal.ext_iff] at h
  apply MvPolynomial.ideal_inj
  convert h
  · aesop
  · aesop

theorem _root_.coordRingMaxIdeal_bijOn [IsAlgClosed 𝕜] (K : 𝕜[X,Y]) :
    Set.BijOn (coordRingMaxIdeal K) {P | K.eval P = 0} {m | m.IsMaximal} := by
  refine ⟨?_, coordRingMaxIdeal_injOn K, ?_⟩
  · intro P hP
    rw [Set.mem_ofPred] at hP ⊢
    exact coordRingMaxIdeal_isMaximal K hP
  intro m hm
  rw [Set.mem_ofPred] at hm
  simp_rw [Set.mem_image, Set.mem_ofPred]
  let L := Γ[𝕜, K] ⧸ m
  let hL : Field L := ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hm).toField
  let : Algebra 𝕜 L := inferInstance
  have halgMap (a : 𝕜) : algebraMap 𝕜 L a = Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (C a)) := rfl
  have : Algebra.FiniteType 𝕜 L := inferInstance
  have : Module.Finite 𝕜 L := finite_of_finite_type_of_isJacobsonRing 𝕜 L -- Th4_2
  have : Algebra.IsAlgebraic 𝕜 L := Algebra.IsAlgebraic.of_finite 𝕜 L
  have : Algebra.IsIntegral 𝕜 L := Algebra.IsIntegral.of_finite 𝕜 L
  have hkL : Function.Bijective (algebraMap 𝕜 L) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨a, ha⟩ := hkL.surjective (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (X 0)))
  obtain ⟨b, hb⟩ := hkL.surjective (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (X 1)))
  symm at ha hb
  let f := (Ideal.Quotient.mk (Ideal.span {K}))
  rw [halgMap, Ideal.Quotient.eq, ← map_sub] at ha hb
  have heval : K.eval ![a, b] = 0 := by
    rw [MvPolynomial.eval_eq_zero_iff_mem_ideal]
    rw [← Ideal.span_singleton_le_iff_mem]
    have hm : (Ideal.comap (Ideal.Quotient.mk (Ideal.span {K})) m).IsMaximal := by
      apply Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    have : Ideal.span (Set.range fun i ↦ X i - C (![a, b] i)) =
        Ideal.comap (Ideal.Quotient.mk (Ideal.span {K})) m := by
      apply Ideal.IsMaximal.eq_of_le (MvPolynomial.isMaximal_span _) hm.ne_top
      rw [Ideal.span_le, Set.range_subset_iff]
      intro i
      fin_cases i
      · simpa using ha
      · simpa using hb
    rw [this, ← Ideal.map_le_iff_le_comap, Ideal.map_quotient_self]
    apply bot_le
  refine ⟨![a, b], heval, ?_⟩
  obtain hmax := coordRingMaxIdeal_isMaximal K heval
  apply Ideal.IsMaximal.eq_of_le hmax hm.ne_top
  rw [coordRingMaxIdeal, Ideal.span_le]
  apply Set.pair_subset ha hb

end Th4_1

-- "k'-point" on page 66
def 𝕝Point {𝕝 : Type*} [Field 𝕝] [Algebra 𝕜 𝕝] (K : 𝕜[X,Y]) : Set (Fin 2 → 𝕝) := {P | K.aeval P = 0}

-- local ring, the curve function ring localized at specific point. In other words, this is the
-- ring of rational functions where poles are permitted anywhere except at the specific point.
abbrev 𝒪 (K : 𝕜[X,Y]) (P : Fin 2 → 𝕜) (hP : K.eval P = 0) :=
  haveI := coordRingMaxIdeal_isMaximal K hP
  Localization.AtPrime (coordRingMaxIdeal K P)

notation "𝔪[" K "," P "," hP "]" => IsLocalRing.maximalIdeal (𝒪 K P hP)

example (K : 𝕜[X,Y]) (P : Fin 2 → 𝕜) (hP : K.eval P = 0) (n : ℕ) := 𝒪 K P hP ⧸ 𝔪[K, P, hP] ^ n

instance (K : 𝕜[X,Y]) (P : Fin 2 → 𝕜) (hP : K.eval P = 0) (n : ℕ) :
    Module 𝕜 (𝒪 K P hP ⧸ 𝔪[K, P, hP] ^ n) := inferInstance

def quot𝔪Equiv (K : 𝕜[X,Y]) (P : Fin 2 → 𝕜) (hP : K.eval P = 0) (n : ℕ) :
    Γ[𝕜, K] ⧸ coordRingMaxIdeal K P ^ n ≃+* 𝒪 K P hP ⧸ 𝔪[K, P, hP] ^ n :=
  haveI := coordRingMaxIdeal_isMaximal K hP
  IsLocalization.AtPrime.equivQuotMaximalIdealPow (coordRingMaxIdeal K P) (𝒪 K P hP) n

def quot𝔪Equivₐ (K : 𝕜[X,Y]) (P : Fin 2 → 𝕜) (hP : K.eval P = 0) (n : ℕ) :
    (Γ[𝕜, K] ⧸ coordRingMaxIdeal K P ^ n) ≃ₐ[𝕜] 𝒪 K P hP ⧸ 𝔪[K, P, hP] ^ n :=
  haveI := coordRingMaxIdeal_isMaximal K hP
  IsLocalization.AtPrime.equivQuotMaximalIdealPowₐ 𝕜 (coordRingMaxIdeal K P) (𝒪 K P hP) n

namespace Th4_6

def alpha (K : 𝕜[X,Y]) (P : Fin 2 → 𝕜) (n : ℕ) (h : K.mult P ≤ n) :
    (𝕜[X,Y] ⧸ (Ideal.span {X 0 - C (P 0), X 1 - C (P 1)}) ^ (n - K.natMult P)) →ₗ[𝕜[X,Y]]
    𝕜[X,Y] ⧸ (Ideal.span {X 0 - C (P 0), X 1 - C (P 1)}) ^ n :=
  Submodule.mapQ ((Ideal.span {(X 0 - C (P 0) : 𝕜[X,Y]), X 1 - C (P 1)}) ^ (n - K.natMult P))
    ((Ideal.span {(X 0 - C (P 0) : 𝕜[X,Y]), X 1 - C (P 1)}) ^ n) (K • LinearMap.id) (by
    intro a ha
    have htop : K.mult P ≠ ⊤ := by
      intro htop
      simp [htop] at h
    have hset : {X 0 - C (P 0), X 1 - C (P 1)} = Set.range fun i ↦ (X i : 𝕜[X,Y]) - C (P i) := by
      aesop
    suffices K * a ∈ Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n by
      simpa
    rw [hset] at ⊢ ha
    rw [← MvPolynomial.le_mult_iff] at ⊢ ha
    grw [← MvPolynomial.le_mult_mul, ← ha]
    push_cast
    rw [natMult, ENat.natCast_toNat htop]
    rw [add_tsub_cancel_of_le h]
  )

theorem exact_alpha (K : 𝕜[X,Y]) (P : Fin 2 → 𝕜) (n : ℕ) (h : K.mult P ≤ n) :
    Function.Exact (alpha K P n h)
    (Ideal.Quotient.mkₐ 𝕜[X,Y] ((Ideal.span {K}).map
    (Ideal.Quotient.mk ((Ideal.span {X 0 - C (P 0), X 1 - C (P 1)}) ^ n)))).toLinearMap := by
  apply Function.Exact.of_comp_of_mem_range
  · ext x
    induction x with | mk x
    suffices (alpha K P n h) ((Ideal.Quotient.mk (Ideal.span {X 0 - C (P 0), X 1 - C (P 1)}
        ^ (n - K.natMult P))) x) ∈
      Ideal.map (Ideal.Quotient.mk (Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n))
        (Ideal.span {K}) by
      simpa [Ideal.Quotient.eq_zero_iff_mem]
    change Ideal.Quotient.mk (Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n) (K * x) ∈
      Ideal.map (Ideal.Quotient.mk (Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n))
        (Ideal.span {K})
    apply Ideal.mem_map_of_mem
    apply Ideal.mul_mem_right
    apply Ideal.mem_span_singleton_self
  · intro x hx
    induction x with | mk x
    rw [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_map_iff_of_surjective _ (Ideal.Quotient.mk_surjective)] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    rw [Ideal.mem_span_singleton] at hy
    obtain ⟨z, hz⟩ := hy
    rw [Set.mem_range]
    use Ideal.Quotient.mk (Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ (n - K.natMult P)) z
    change Ideal.Quotient.mk (Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n) (K * z) =
      Ideal.Quotient.mk (Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n) x
    rw [← hz]
    exact hxy

def r (K : 𝕜[X,Y]) (P : Fin 2 → 𝕜) (n : ℕ) :=
  ((𝕜[X,Y] ⧸ Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n) ⧸
  Ideal.map (Ideal.Quotient.mk (Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n)) (Ideal.span {K}))


instance (K : 𝕜[X,Y]) (P : Fin 2 → 𝕜) (n : ℕ) :
  AddCommMonoid ((𝕜[X,Y] ⧸ Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n) ⧸
  Ideal.map (Ideal.Quotient.mk (Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n)) (Ideal.span {K})) :=
  inferInstance

instance (K : 𝕜[X,Y]) (P : Fin 2 → 𝕜) (n : ℕ) :
  Module 𝕜 ((𝕜[X,Y] ⧸ Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n) ⧸
  Ideal.map (Ideal.Quotient.mk (Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n)) (Ideal.span {K})) :=
  inferInstance

theorem exact_alpha' (K : 𝕜[X,Y]) (P : Fin 2 → 𝕜) (n : ℕ) (h : K.mult P ≤ n) :
    Function.Exact ((alpha K P n h).restrictScalars 𝕜)
    (Ideal.Quotient.mkₐ 𝕜 ((Ideal.span {K}).map
    (Ideal.Quotient.mk ((Ideal.span {X 0 - C (P 0), X 1 - C (P 1)}) ^ n)))).toLinearMap :=
  exact_alpha K P n h

instance (K : 𝕜[X,Y]) (P : Fin 2 → 𝕜) (n : ℕ) :
    Module.Free 𝕜 ((𝕜[X,Y] ⧸ (Ideal.span {X 0 - C (P 0), X 1 - C (P 1)}) ^ (n - K.natMult P))) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- why is this slow?
instance (K : 𝕜[X,Y]) (P : Fin 2 → 𝕜) (n : ℕ) :
    Module.Free 𝕜 ((𝕜[X,Y] ⧸ Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n) ⧸
    Ideal.map (Ideal.Quotient.mk (Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n)) (Ideal.span {K}))
    :=
  inferInstance

def equiv (K : 𝕜[X,Y]) (P : Fin 2 → 𝕜) (n : ℕ) (h : K.mult P ≤ n) :
    ((𝕜[X,Y] ⧸ (Ideal.span {X 0 - C (P 0), X 1 - C (P 1)}) ^ (n - K.natMult P)) ×
    ((𝕜[X,Y] ⧸ Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n) ⧸
    Ideal.map (Ideal.Quotient.mk (Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n)) (Ideal.span {K})))
    ≃ₗ[𝕜]
    (𝕜[X,Y] ⧸ (Ideal.span {X 0 - C (P 0), X 1 - C (P 1)}) ^ n) := by
  refine lequivProdOfLeftSplitExact ?_ (LinearMap.exact_iff.mp (exact_alpha' K P n h)).symm
    (LinearMap.leftInverse_comp_of_inj ?_)
  · exact Ideal.Quotient.mkₐ_surjective 𝕜 _
  · have htop : K.mult P ≠ ⊤ := by
      intro htop
      simp [htop] at h
    rw [LinearMap.ker_eq_bot]
    intro x y h
    induction x with | mk x
    induction y with | mk y
    change Ideal.Quotient.mk (Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n) (K * x) =
      Ideal.Quotient.mk (Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n) (K * y) at h
    rw [Ideal.Quotient.eq] at ⊢ h
    rw [← mul_sub] at h
    have hset : {X 0 - C (P 0), X 1 - C (P 1)} = Set.range fun i ↦ (X i : 𝕜[X,Y]) - C (P i) := by
      aesop
    rw [hset, ← MvPolynomial.le_mult_iff] at ⊢ h
    rw [MvPolynomial.mult_mul] at h
    push_cast
    rw [natMult, ENat.natCast_toNat htop]
    rw [tsub_le_iff_left]
    exact h

def quotQuotEquiv (K : 𝕜[X,Y]) (P : Fin 2 → 𝕜) (n : ℕ) :
    (𝕜[X,Y] ⧸ Ideal.span {K}) ⧸ coordRingMaxIdeal K P ^ n ≃+*
    (𝕜[X,Y] ⧸ Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n) ⧸
    Ideal.map (Ideal.Quotient.mk (Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n))
    (Ideal.span {K}) :=
  (Ideal.quotEquivOfEq (by
    rw [coordRingMaxIdeal_eq_map K P]
    rw [Ideal.map_pow]
  )).trans (DoubleQuot.quotQuotEquivComm _ _)

def quotQuotEquivₐ (K : 𝕜[X,Y]) (P : Fin 2 → 𝕜) (n : ℕ) :
    ((𝕜[X,Y] ⧸ Ideal.span {K}) ⧸ coordRingMaxIdeal K P ^ n) ≃ₐ[𝕜]
    (𝕜[X,Y] ⧸ Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n) ⧸
    Ideal.map (Ideal.Quotient.mk (Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n))
    (Ideal.span {K}) :=
  AlgEquiv.ofRingEquiv (f := quotQuotEquiv K P n) (fun _ ↦ rfl)

theorem rank_quot𝔪 {K : 𝕜[X,Y]} {P : Fin 2 → 𝕜} (hP : K.eval P = 0) {n : ℕ} (h : K.mult P ≤ n) :
    Module.rank 𝕜 (𝒪 K P hP ⧸ 𝔪[K, P, hP] ^ n) =
    K.natMult P * n - K.natMult P * (K.natMult P - 1) / 2 := by
  have hn0 : n ≠ 0 := by
    rw [← MvPolynomial.one_le_mult_iff] at hP
    obtain h := hP.trans h
    rw [Order.one_le_iff_ne_zero] at h
    simpa using h
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hmn : K.natMult P ≤ n := by
    obtain h := (ENat.natCast_toNat_le_self _).trans h
    unfold natMult
    simpa using h
  have hm1 : 1 ≤ K.natMult P := by
    rw [← MvPolynomial.one_le_mult_iff] at hP
    unfold natMult
    rw [← ENat.natCast_le_natCast]
    rw [ENat.natCast_toNat (fun h' ↦ by simp [h'] at h)]
    exact hP
  rw [← (quot𝔪Equivₐ K P hP n).toLinearEquiv.rank_eq]
  rw [(quotQuotEquivₐ K P n).toLinearEquiv.rank_eq]
  obtain heq := (equiv K P n h).rank_eq
  rw [rank_prod'] at heq
  have hset : {X 0 - C (P 0), X 1 - C (P 1)} = Set.range fun i ↦ (X i : 𝕜[X,Y]) - C (P i) := by
    aesop
  have (m : ℕ) : Module.rank 𝕜 (𝕜[X,Y] ⧸ Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ m) =
      Module.rank 𝕜 (𝕜[X,Y] ⧸ Ideal.span (Set.range fun i ↦ (X i : 𝕜[X,Y]) - C (P i)) ^ m) := by
    congr
  simp_rw [this] at heq
  rw [MvPolynomial.rank_quot' _ _ _ hn0] at heq
  by_cases! h0 : n - K.natMult P = 0
  · rw [h0, MvPolynomial.rank_quot'_zero, zero_add] at heq
    rw [Nat.sub_eq_zero_iff_le] at h0
    obtain hmn := le_antisymm hmn h0
    suffices (n - 1 + 2).choose (n - 1) = n * n - n * (n - 1) / 2 by
      simpa [hmn, heq]
    rw [Nat.choose_symm_add, Nat.choose_two_right]
    apply Nat.eq_sub_of_add_eq
    rw [← Nat.mul_left_inj (show 2 ≠ 0 by simp), Nat.add_mul]
    rw [Nat.div_mul_cancel (by apply Nat.two_dvd_mul_sub_one)]
    rw [Nat.div_mul_cancel (by apply Nat.two_dvd_mul_sub_one)]
    rw [show n - 1 + 2 - 1 = n - 1 + 1 by simp]
    zify [hn1]
    ring
  · have hnm1 : 1 ≤ n - K.natMult P := Nat.one_le_iff_ne_zero.mpr h0
    have hnm2 : K.natMult P - 1 ≤ n * 2 := by
      trans K.natMult P
      · simp
      rw [Nat.sub_ne_zero_iff_lt] at h0
      trans n
      · exact h0.le
      exact Nat.le_mul_of_pos_right _ (by simp)
    rw [MvPolynomial.rank_quot' _ _ _ h0] at heq
    obtain haleph0 | haleph0 := le_or_gt Cardinal.aleph0 (Module.rank 𝕜
      ((𝕜[X,Y] ⧸ Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n) ⧸
        Ideal.map (Ideal.Quotient.mk (Ideal.span {X 0 - C (P 0), X 1 - C (P 1)} ^ n))
        (Ideal.span {K})))
    · rw [Cardinal.add_eq_max' haleph0] at heq
      obtain h' := haleph0.trans (heq ▸ le_max_right _ _)
      contrapose! h'
      simp
    obtain ⟨u, hu⟩ := Cardinal.lt_aleph0.mp haleph0
    rw [hu] at ⊢ heq
    norm_cast at heq
    rw [Nat.eq_sub_of_add_eq' heq]
    rw [Nat.choose_symm_add, Nat.choose_symm_add]
    norm_cast
    simp only [Fintype.card_fin, Nat.choose_two_right, Nat.add_one_sub_one]
    rw [← Nat.mul_left_inj (show 2 ≠ 0 by simp), Nat.sub_mul, Nat.sub_mul]
    rw [Nat.div_mul_cancel (by
      rw [mul_comm]
      exact Nat.two_dvd_mul_add_one (n - 1 + 1))]
    rw [Nat.div_mul_cancel (by
      rw [mul_comm]
      exact Nat.two_dvd_mul_add_one (n - K.natMult P - 1 + 1))]
    rw [Nat.div_mul_cancel (by apply Nat.two_dvd_mul_sub_one)]
    rw [mul_assoc, ← Nat.mul_sub]
    apply Nat.sub_eq_of_eq_add
    zify [hn1, hnm1, hmn, hnm2, hm1]
    ring

instance {K : 𝕜[X,Y]} : Module (𝕜[X,Y] ⧸ Ideal.span {K}) (𝕜[X,Y] ⧸ Ideal.span {K}) := inferInstance

theorem Submodule.rank_quotient_add_rank'.{u} {R : Type*} {M : Type u} [Ring R] [AddCommGroup M]
    [Module R M] [HasRankNullity.{u} R]
    {S : Type*} [Ring S] [SMul R S] [Module S M] [IsScalarTower R S M]
    (N : Submodule S M) :
    Module.rank R (M ⧸ N) + Module.rank R N = Module.rank R M := by
  exact (N.restrictScalars R).rank_quotient_add_rank

set_option synthInstance.maxHeartbeats 400000 in
-- Somehow slow
abbrev _root_.𝔪Quot𝔪 (K : 𝕜[X,Y]) (P : Fin 2 → 𝕜) (hP : K.eval P = 0) (n : ℕ) :=
    Submodule.map (𝔪[K, P, hP] ^ (n + 1)).mkQ (𝔪[K, P, hP] ^ n)

-- dim[𝕜] (𝔪[K, P] ^ n ⧸ 𝔪[K, P] ^ (n + 1)) = K.natMult P
set_option maxHeartbeats 400000 in
-- Somehow slow
theorem _root_.rank_𝔪Quot𝔪 {K : 𝕜[X,Y]} {P : Fin 2 → 𝕜} (hP : K.eval P = 0) {n : ℕ}
    (h : K.mult P ≤ n) :
    Module.rank 𝕜 (𝔪Quot𝔪 K P hP n) = K.natMult P := by
  have hm1 : 1 ≤ K.natMult P := by
    rw [← MvPolynomial.one_le_mult_iff] at hP
    unfold natMult
    rw [← ENat.natCast_le_natCast]
    rw [ENat.natCast_toNat (fun h' ↦ by simp [h'] at h)]
    exact hP
  have hm0 : 0 < K.natMult P :=
    (Nat.pos_iff_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hm1))
  have hmn : K.natMult P ≤ n := by
    obtain h := (ENat.natCast_toNat_le_self _).trans h
    unfold natMult
    simpa using h
  obtain heq := congr($(((Submodule.quotientQuotientEquivQuotient
    (𝔪[K, P, hP] ^ (n + 1)) (𝔪[K, P, hP] ^ n)
    (Ideal.pow_le_pow_right (by simp))).restrictScalars 𝕜).rank_eq) +
    Module.rank 𝕜 (𝔪Quot𝔪 K P hP n))
  rw [Submodule.rank_quotient_add_rank'] at heq
  rw [rank_quot𝔪 hP (h.trans (by simp))] at heq
  rw [rank_quot𝔪 hP h] at heq
  obtain haleph0 | haleph0 := le_or_gt Cardinal.aleph0 (Module.rank 𝕜 (𝔪Quot𝔪 K P hP n))
  · rw [Cardinal.add_eq_max' haleph0] at heq
    obtain h' := haleph0.trans (heq ▸ le_max_right _ _)
    contrapose! h'
    simp
  · obtain ⟨u, hu⟩ := Cardinal.lt_aleph0.mp haleph0
    rw [hu] at ⊢ heq
    norm_cast at heq ⊢
    rw [← Nat.sub_eq_iff_eq_add' (by
      apply Nat.sub_le_sub_right
      rw [Nat.mul_le_mul_left_iff hm0]
      simp)] at heq
    rw [← heq]
    rw [Nat.sub_sub_sub_cancel_right (by
      rw [← Nat.mul_le_mul_right_iff (show 0 < 2 by simp)]
      rw [Nat.div_mul_cancel (by apply Nat.two_dvd_mul_sub_one)]
      rw [mul_assoc]
      rw [Nat.mul_le_mul_left_iff hm0]
      apply (Nat.sub_le _ _).trans (hmn.trans (Nat.le_mul_of_pos_right _ (by simp))))]
    rw [← Nat.mul_sub]
    simp


end Th4_6

namespace Th4_7


-- This doesn't type check. IsDiscreteValuationRing requires `𝒪 K P hP` to be a domain to even state
-- For `𝒪 K P hP`, a localization of `Γ[𝕜, K]`, to be a domain, we can try letting `Γ[𝕜, K]` to be a
-- domain, but this requires `K` to be prime, i.e. a irreducible curve
/-theorem _root_.nonsingular_iff_IsDiscreteValuationRing [IsAlgClosed 𝕜]
    {K : 𝕜[X,Y]} {P : Fin 2 → 𝕜} (hP : K.eval P = 0) :
    K.natMult P = 1 ↔ IsDiscreteValuationRing (𝒪 K P hP) := by
  sorry-/

end Th4_7

instance (P : Fin 2 → 𝕜) : (Ideal.span {(X 0 - C (P 0) : 𝕜[X,Y]), X 1 - C (P 1)}).IsMaximal := by
  convert MvPolynomial.isMaximal_span P
  aesop

abbrev 𝒪2 (P : Fin 2 → 𝕜) :=
  Localization.AtPrime (Ideal.span { (X 0 - C (P 0) : 𝕜[X,Y]), (X 1 - C (P 1)) })
