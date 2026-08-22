/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
import Mathlib
import RrtAlgebraicGeometry.MvPolynomial

/-! -/

noncomputable section

open MvPolynomial

variable {ι η : Type*}

variable {𝕜 : Type*} [Field 𝕜]

notation:9000 R "[X_" ι "]" => MvPolynomial ι R

abbrev pointIdeal (P : η → 𝕜) : Ideal 𝕜[X_η] := Ideal.span (Set.range (fun n ↦ X n - C (P n)))

instance (P : η → 𝕜) : (pointIdeal P).IsMaximal := inferInstance

abbrev 𝒪 (P : η → 𝕜) := Localization.AtPrime (pointIdeal P)

abbrev 𝒪I (P : η → 𝕜) (F : ι → 𝕜[X_η]) : Ideal (𝒪 P) :=
   (Ideal.span (Set.range F)).map (algebraMap 𝕜[X_η] (𝒪 P))

abbrev 𝒪I_eq_span (P : η → 𝕜) (F : ι → 𝕜[X_η]) :
  𝒪I P F = Ideal.span (Set.range fun i ↦ algebraMap 𝕜[X_η] (𝒪 P) (F i)) := by
  rw [𝒪I, Ideal.map_span, ← Set.range_comp']

theorem 𝒪I_eq_map_span (P : η → 𝕜) (F : ι → 𝕜[X_η]) :
    𝒪I P F = (Ideal.span (Set.range F)).map (algebraMap 𝕜[X_η] (𝒪 P)) := by
  rfl

-- Def 4.2, the ring of intersection at point P of curves F
abbrev ℛ (P : η → 𝕜) (F : ι → 𝕜[X_η]) := 𝒪 P ⧸ 𝒪I P F

instance (P : η → 𝕜) (F : ι → 𝕜[X_η]) : Algebra 𝕜 (ℛ P F) := inferInstance
instance (P : η → 𝕜) (F : ι → 𝕜[X_η]) : Module.Free 𝕜 (ℛ P F) := Module.Free.of_divisionRing _ _

theorem forall_eval_eq_zero_iff [Finite η] (P : η → 𝕜) (F : ι → 𝕜[X_η]) :
    (∀ (n : ι), (eval P) (F n) = 0) ↔ Ideal.span (Set.range F) ≤ pointIdeal P := by
  rw [Ideal.span_le, Set.range_subset_iff]
  congrm ∀ i, ?_
  rw [MvPolynomial.eval_eq_zero_iff_mem_ideal]
  rfl

-- Def 4.2, the order of intersection at point P of curves F
def ℐ (P : η → 𝕜) (F : ι → 𝕜[X_η]) := Module.rank 𝕜 (ℛ P F)

def finℐ (P : η → 𝕜) (F : ι → 𝕜[X_η]) := (ℐ P F).toNat

theorem isPrime_map_pointIdeal [Finite η] {P : η → 𝕜} {F : ι → 𝕜[X_η]} (h : ∀ n, (F n).eval P = 0) :
    ((pointIdeal P).map (Ideal.Quotient.mk (Ideal.span (Set.range F)))).IsPrime := by
  apply Ideal.isPrime_map_quotientMk_of_isPrime
  exact (forall_eval_eq_zero_iff P F).mp h

@[simp]
theorem Ideal.toRingHom_quotientMapₐ {R₁ : Type u_1} {A : Type u_3} {B : Type u_4}
    [CommSemiring R₁] [Ring A] [Algebra R₁ A] [Ring B] [Algebra R₁ B] {I : Ideal A} (J : Ideal B)
    [I.IsTwoSided] [J.IsTwoSided] (f : A →ₐ[R₁] B) (hIJ : I ≤ comap f J) :
    (Ideal.quotientMapₐ J f hIJ).toRingHom = Ideal.quotientMap J f hIJ :=
  rfl

def IsLocalization.quotientEquiv (R Rₚ RIₚ : Type*) [CommRing R] [CommRing Rₚ] [CommRing RIₚ]
    (p : Ideal R) [p.IsPrime]
    [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
    (I : Ideal R) (hIp : I ≤ p)
    (_ : (p.map (Ideal.Quotient.mk I)).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIp)
    [Algebra (R ⧸ I) RIₚ] [IsLocalization.AtPrime RIₚ (p.map (Ideal.Quotient.mk I))] :
    Rₚ ⧸ I.map (algebraMap R Rₚ) ≃+* RIₚ := by
  have hIle : I ≤ Ideal.comap (algebraMap R Rₚ) (Ideal.map (algebraMap R Rₚ) I) :=
    Ideal.le_comap_map
  have h1 (x : p.primeCompl) :
      IsUnit (((algebraMap (R ⧸ I) RIₚ).comp (Ideal.Quotient.mk I)) x.val) := by
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [IsLocalization.AtPrime.isUnit_to_map_iff _ (p.map (Ideal.Quotient.mk I))]
    suffices x.val ∉ p by simpa [sup_eq_left.mpr hIp]
    exact x.prop
  have h2 (x : (Ideal.map (Ideal.Quotient.mk I) p).primeCompl) :
      IsUnit ((Ideal.quotientMap (I.map (algebraMap R Rₚ)) (algebraMap R Rₚ) hIle) x.val) := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    suffices IsUnit (Ideal.Quotient.mk (I.map (algebraMap R Rₚ)) (algebraMap R Rₚ y)) by simpa
    apply RingHom.isUnit_map
    rw [IsLocalization.AtPrime.isUnit_to_map_iff _ p]
    simpa [sup_eq_left.mpr hIp] using hx
  refine RingEquiv.ofRingHom (Ideal.Quotient.lift _ (IsLocalization.lift h1) ?_)
    (IsLocalization.lift h2) ?_ ?_
  · intro x hx
    obtain ⟨y, z, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
    rw [IsLocalization.mk'_mem_map_algebraMap_iff] at hx
    obtain ⟨s, hs, hsy⟩ := hx
    simp only [lift_mk'_spec, RingHom.coe_comp, Function.comp_apply, mul_zero]
    rw [← IsLocalization.mk'_one (M := (p.map (Ideal.Quotient.mk I)).primeCompl)]
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨Ideal.Quotient.mk _ s, ?_⟩, ?_⟩
    · suffices s ∉ p by simpa [sup_eq_left.mpr hIp]
      exact hs
    · simpa [← map_mul, Ideal.Quotient.eq_zero_iff_mem] using hsy
  · apply IsLocalization.ringHom_ext (Ideal.map (Ideal.Quotient.mk I) p).primeCompl
    ext y
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
      IsLocalization.lift_eq, Ideal.quotientMap_mk, Ideal.Quotient.lift_mk]
  · ext x
    simp only [RingHom.coe_comp, Function.comp_apply, Ideal.Quotient.lift_mk,
      RingHomCompTriple.comp_eq]
    obtain ⟨y, z, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
    have (h' : ∀ (x : p.primeCompl),
        IsUnit (((algebraMap (R ⧸ I) RIₚ).comp (Ideal.Quotient.mk I)) x.val)) :
      IsLocalization.lift h' (IsLocalization.mk' Rₚ y z) =
      IsLocalization.mk'
        (M := (p.map (Ideal.Quotient.mk I)).primeCompl)
        _ y ⟨z.val, (by
          suffices z.val ∉ p by simpa [sup_eq_left.mpr hIp]
          exact z.prop)⟩ := by
      simp [IsLocalization.lift_mk'_spec]
    rw [this]
    rw [IsLocalization.lift_mk'_spec]
    simp only [Ideal.quotientMap_mk, Ideal.Quotient.mk_algebraMap]
    have (u : R) : algebraMap R (Rₚ ⧸ I.map (algebraMap R Rₚ)) u =
        Ideal.Quotient.mk (I.map (algebraMap R Rₚ)) (algebraMap R Rₚ u) := rfl
    simp_rw [this]
    rw [← map_mul]
    simp

-- `𝕜[X_η]_P ⧸ F_P ≃ (𝕜[X_η] ⧸ F)_P`
def ℛRingEquiv [Finite η] {P : η → 𝕜} {F : ι → 𝕜[X_η]} (h : ∀ n, (F n).eval P = 0) :
    have := isPrime_map_pointIdeal h
    ℛ P F ≃+*
      (Localization.AtPrime ((pointIdeal P).map (Ideal.Quotient.mk (Ideal.span (Set.range F))))) :=
  have := isPrime_map_pointIdeal h
  have h : Ideal.span (Set.range F) ≤ pointIdeal P := (forall_eval_eq_zero_iff P F).mp h
  IsLocalization.quotientEquiv 𝕜[X_η] (𝒪 P) _ (pointIdeal P) (Ideal.span (Set.range F)) h

def ℛRingEquivₐ [Finite η] {P : η → 𝕜} {F : ι → 𝕜[X_η]} (h : ∀ n, (F n).eval P = 0) :
    have := isPrime_map_pointIdeal h
    ℛ P F ≃ₐ[𝕜]
      (Localization.AtPrime ((pointIdeal P).map (Ideal.Quotient.mk (Ideal.span (Set.range F))))) :=
  AlgEquiv.ofRingEquiv (f := ℛRingEquiv h) (by
    intro x
    simp only [ℛRingEquiv, IsLocalization.quotientEquiv, RingEquiv.ofRingHom_apply]
    have : algebraMap 𝕜 (ℛ P F) x =
      Ideal.Quotient.mk (𝒪I P F) (algebraMap 𝕜[X_η] (𝒪 P) (algebraMap 𝕜 𝕜[X_η] x)) := rfl
    rw [this, ← IsLocalization.mk'_one (𝒪 P) (M := (pointIdeal P).primeCompl),
      Ideal.Quotient.lift_mk]
    rw [IsLocalization.lift_mk'_spec]
    simp
    rfl
  )

theorem ℐ_eq_rank_localization [Finite η] {P : η → 𝕜} {F : ι → 𝕜[X_η]} (h : ∀ n, (F n).eval P = 0) :
    have := isPrime_map_pointIdeal h
    ℐ P F = Module.rank 𝕜 (Localization.AtPrime
      ((pointIdeal P).map (Ideal.Quotient.mk (Ideal.span (Set.range F))))) := by
  unfold ℐ ℛ

  sorry

theorem IsLocalization.AtPrime.map_eq_top_iff_not_le
    {R : Type*} [CommSemiring R] (S : Type*) [CommSemiring S] [Algebra R S]
    {I p : Ideal R} [p.IsPrime] [IsLocalization.AtPrime S p] :
    Ideal.map (algebraMap R S) I = ⊤ ↔ ¬I ≤ p where
  mp h := by
    have : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S p
    contrapose! h
    refine ne_top_of_le_ne_top ?_ (Ideal.map_mono h)
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal p S]
    exact Ideal.IsPrime.ne_top'
  mpr := IsLocalization.AtPrime.map_eq_top_of_not_le S

-- Proposition 4.12 (1)
-- the order of intersection at point P is zero iff some curve in F doesn't pass P
theorem ℐ_eq_zero_iff [Finite η] (P : η → 𝕜) (F : ι → 𝕜[X_η]) :
    ℐ P F = 0 ↔ ∃ n, (F n).eval P ≠ 0 := by
  let : Fintype η := Fintype.ofFinite η
  calc
    _ ↔ Subsingleton (ℛ P F) := Module.rank_zero_iff_of_free
    _ ↔ 𝒪I P F = ⊤ := Ideal.Quotient.subsingleton_iff
    _ ↔ ¬Ideal.span (Set.range F) ≤ pointIdeal P := by
      rw [𝒪I_eq_map_span]
      apply IsLocalization.AtPrime.map_eq_top_iff_not_le
    _ ↔ _ := by
      contrapose!
      rw [forall_eval_eq_zero_iff]

def IntersectProperly (F : ι → 𝕜[X_η]) := Ring.KrullDimLE 0 (𝕜[X_η] ⧸ Ideal.span (Set.range F))

theorem IntersectProperly.isArtinianRing [Finite η] {F : ι → 𝕜[X_η]} (h : IntersectProperly F) :
    IsArtinianRing (𝕜[X_η] ⧸ Ideal.span (Set.range F)) := by
  have : Ring.KrullDimLE 0 (𝕜[X_η] ⧸ Ideal.span (Set.range F)) := h
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

theorem IntersectProperly.finiteDimensional [Finite η] {F : ι → 𝕜[X_η]} (h : IntersectProperly F) :
    FiniteDimensional 𝕜 (𝕜[X_η] ⧸ Ideal.span (Set.range F)) :=
  (Module.finite_iff_krullDimLE_zero _ _).mpr h

-- Aristotle
theorem isMaximal_of_finite_zeroLocus [Finite η] [IsAlgClosed 𝕜] {P : Ideal 𝕜[X_η]}
    [P.IsPrime] (hP : (MvPolynomial.zeroLocus 𝕜 P).Finite) : P.IsMaximal := by
  have hPeq : MvPolynomial.vanishingIdeal 𝕜 (MvPolynomial.zeroLocus 𝕜 P) = P :=
    MvPolynomial.IsPrime.vanishingIdeal_zeroLocus P
  -- the vanishing ideal of a finite set is the (finite) infimum of the maximal ideals of points
  set s : Finset (η → 𝕜) := hP.toFinset with hs
  have hinf : s.inf (fun x => MvPolynomial.vanishingIdeal 𝕜 ({x} : Set (η → 𝕜))) ≤ P := by
    rw [← hPeq]
    intro p hp x hx
    have hxs : x ∈ s := by simpa [hs] using hx
    have := Finset.inf_le hxs (f := fun x => MvPolynomial.vanishingIdeal 𝕜 ({x} : Set (η → 𝕜)))
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x p).1 (this hp)
  obtain ⟨x, hxs, hxle⟩ := (Ideal.IsPrime.inf_le' ‹P.IsPrime›).1 hinf
  have hPx : P = MvPolynomial.vanishingIdeal 𝕜 ({x} : Set (η → 𝕜)) := by
    refine le_antisymm ?_ hxle
    rw [← hPeq]
    exact MvPolynomial.vanishingIdeal_anti_mono
      (Set.singleton_subset_iff.2 (by simpa [hs] using hxs))
  rw [hPx]
  infer_instance

-- Aristotle
theorem IntersectProperly.of_finite [Finite η] [IsAlgClosed 𝕜] {F : ι → 𝕜[X_η]}
    (h : {P : η → 𝕜 | ∀ i, (F i).eval P = 0}.Finite) :
    IntersectProperly F := by
  refine Ring.KrullDimLE.mk₀ ?_
  intro p hp
  have : (Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range F))) p).IsPrime :=
    Ideal.comap_isPrime _ _
  have hIq : Ideal.span (Set.range F) ≤
      Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range F))) p := by
    intro z hz
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hz]
  have hfin : (MvPolynomial.zeroLocus 𝕜
      (Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range F))) p)).Finite := by
    refine h.subset ?_
    intro x hx i
    have hxi : MvPolynomial.aeval x (F i) = 0 :=
      hx (F i) (hIq (Ideal.subset_span ⟨i, rfl⟩))
    rwa [MvPolynomial.aeval_eq_eval] at hxi
  have hqmax : (Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range F))) p).IsMaximal :=
    isMaximal_of_finite_zeroLocus hfin
  have hker : RingHom.ker (Ideal.Quotient.mk (Ideal.span (Set.range F))) ≤
      Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range F))) p := by
    rw [Ideal.mk_ker]; exact hIq
  have hmap := Ideal.IsMaximal.map_of_surjective_of_ker_le
    (f := Ideal.Quotient.mk (Ideal.span (Set.range F)))
    Ideal.Quotient.mk_surjective hker
  rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at hmap

-- Proposition 4.19
theorem finsum_finℐ_eq_rank [Finite η] {F : ι → 𝕜[X_η]} (h : IntersectProperly F) :
    ∑ᶠ P, finℐ P F = Module.finrank 𝕜 (𝕜[X_η] ⧸ Ideal.span (Set.range F)) := by
  have : IsArtinianRing (𝕜[X_η] ⧸ Ideal.span (Set.range F)) := h.isArtinianRing
  let : Fintype (PrimeSpectrum (𝕜[X_η] ⧸ Ideal.span (Set.range F))) := Fintype.ofFinite _
  have : Module.Finite 𝕜 (𝕜[X_η] ⧸ Ideal.span (Set.range F)) := h.finiteDimensional
  rw [IsArtinianRing.finrank_eq_sum_primeSpectrum]
  --unfold finℐ ℐ ℛ 𝒪
  sorry
