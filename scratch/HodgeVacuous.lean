import Problems.Hodge.Millennium
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

/-!
# The repository's Hodge statement is vacuous

`SmoothProjectiveRealization ℂ X s` asks for a type `points` in bijection with all scheme
morphisms `Spec ℂ ⟶ X`, together with an injection `points → ℙ^N(ℂ)`.  Since `ℂ` has more than
continuum many ring endomorphisms, `Spec ℂ ⟶ X` has cardinality `> 𝔠` as soon as it is nonempty,
while `ℙ^N(ℂ)` has cardinality `𝔠`.  Hence every `SmoothProjectiveVariety ℂ` has no complex
points at all, its Betti cohomology vanishes, and `ClayHodge` holds trivially.
-/

namespace MillenniumHodge.Vacuous

open AlgebraicGeometry VarietyDefinition Cardinal CategoryTheory

universe u₁ u₂ u₃

/-! ### Many ring endomorphisms of `ℂ` -/

/-- A copy of `ℂ` on which we may install a twisted algebra structure. -/
def CTwist : Type := ℂ

noncomputable instance : Field CTwist := inferInstanceAs (Field ℂ)
instance : IsAlgClosed CTwist := inferInstanceAs (IsAlgClosed ℂ)

/-- Any injective self-map of a transcendence basis of `ℂ/ℚ` extends to a ring endomorphism. -/
theorem exists_ringHom_extending (T : Set ℂ) (hT : IsTranscendenceBasis ℚ ((↑) : T → ℂ))
    (τ : T → T) (hτ : Function.Injective τ) :
    ∃ ρ : ℂ →+* ℂ, ∀ t : T, ρ t = τ t := by
  have hg : AlgebraicIndependent ℚ (((↑) : T → ℂ) ∘ τ) := hT.1.comp τ hτ
  let φ : Algebra.adjoin ℚ (Set.range ((↑) : T → ℂ)) →ₐ[ℚ] ℂ :=
    (MvPolynomial.aeval (((↑) : T → ℂ) ∘ τ)).comp hT.1.aevalEquiv.symm.toAlgHom
  have hφ : Function.Injective φ := by
    intro a b hab
    exact hT.1.aevalEquiv.symm.injective (hg (by simpa [φ] using hab))
  letI : Algebra (Algebra.adjoin ℚ (Set.range ((↑) : T → ℂ))) CTwist := φ.toRingHom.toAlgebra
  haveI : Module.IsTorsionFree (Algebra.adjoin ℚ (Set.range ((↑) : T → ℂ))) CTwist :=
    (Module.isTorsionFree_iff_algebraMap_injective).2 hφ
  haveI : Algebra.IsAlgebraic (Algebra.adjoin ℚ (Set.range ((↑) : T → ℂ))) ℂ := hT.isAlgebraic
  let ρ' : ℂ →ₐ[Algebra.adjoin ℚ (Set.range ((↑) : T → ℂ))] CTwist := IsAlgClosed.lift
  refine ⟨ρ'.toRingHom, fun t => ?_⟩
  have ht : (t : ℂ) = algebraMap (Algebra.adjoin ℚ (Set.range ((↑) : T → ℂ))) ℂ
      (hT.1.aevalEquiv (MvPolynomial.X t)) := by
    rw [hT.1.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
  calc ρ'.toRingHom t
      = ρ' (algebraMap (Algebra.adjoin ℚ (Set.range ((↑) : T → ℂ))) ℂ
          (hT.1.aevalEquiv (MvPolynomial.X t))) := by rw [← ht]; rfl
    _ = φ (hT.1.aevalEquiv (MvPolynomial.X t)) := ρ'.commutes _
    _ = τ t := by simp [φ]

/-- For any ring endomorphism `ψ` of `ℂ`, there is a family of endomorphisms `ρ σ`, indexed by
the permutations of a set of size continuum, whose compositions `ρ σ ∘ ψ` are pairwise
distinct. -/
theorem exists_perm_family (ψ : ℂ →+* ℂ) :
    ∃ (S : Set ℂ) (_ : #S = 𝔠) (ρ : Equiv.Perm S → (ℂ →+* ℂ)),
      ∀ σ σ', (ρ σ).comp ψ = (ρ σ').comp ψ → σ = σ' := by
  classical
  obtain ⟨B, hB⟩ := exists_isTranscendenceBasis ℚ ℂ
  have hBcard : #B = 𝔠 := by
    have := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hB
      (Cardinal.mk_le_aleph0) (by rw [Cardinal.mk_complex]; exact aleph0_lt_continuum)
    rw [Cardinal.mk_complex] at this
    exact this.symm
  let ψA : ℂ →ₐ[ℚ] ℂ :=
    { ψ with commutes' := fun q => by simp [map_ratCast] }
  have hψinj : Function.Injective ψ := ψ.injective
  have hS : AlgebraicIndependent ℚ ((↑) : (ψ '' B) → ℂ) := by
    have := hB.1.map (f := ψA) hψinj.injOn
    refine this.to_subtype_range' ?_
    rw [Set.range_comp, Subtype.range_coe]
    rfl
  obtain ⟨T, hST, hT⟩ := exists_isTranscendenceBasis_superset (R := ℚ) hS
  refine ⟨ψ '' B, by rw [Cardinal.mk_image_eq hψinj, hBcard], ?_⟩
  let τ : Equiv.Perm (ψ '' B) → T → T := fun σ t =>
    if h : (t : ℂ) ∈ ψ '' B then ⟨σ ⟨t, h⟩, hST (σ ⟨t, h⟩).2⟩ else t
  have hτ : ∀ σ, Function.Injective (τ σ) := by
    intro σ t t' htt'
    simp only [τ] at htt'
    split_ifs at htt' with h h' h'
    · have := congrArg Subtype.val htt'
      simp only at this
      have h2 : (⟨t, h⟩ : ψ '' B) = ⟨t', h'⟩ := σ.injective (Subtype.ext this)
      have h3 : (t : ℂ) = t' := Subtype.mk.inj h2
      exact Subtype.ext h3
    · exfalso
      have := congrArg Subtype.val htt'
      simp only at this
      exact h' (this ▸ (σ ⟨t, h⟩).2)
    · exfalso
      have := congrArg Subtype.val htt'
      simp only at this
      exact h (this ▸ (σ ⟨t', h'⟩).2)
    · exact htt'
  choose ρ hρ using fun σ => exists_ringHom_extending T hT (τ σ) (hτ σ)
  refine ⟨ρ, fun σ σ' h => ?_⟩
  ext ⟨s, hs⟩
  obtain ⟨b, hb, rfl⟩ := hs
  have h1 : ρ σ (ψ b) = ρ σ' (ψ b) := by
    have := congrArg (fun f : ℂ →+* ℂ => f b) h
    simpa using this
  have hmem : ψ b ∈ ψ '' B := ⟨b, hb, rfl⟩
  have e1 := hρ σ ⟨ψ b, hST hmem⟩
  have e2 := hρ σ' ⟨ψ b, hST hmem⟩
  rw [e1, e2] at h1
  simp only [τ, dif_pos hmem] at h1
  exact h1

/-! ### Projective space is small -/

theorem card_projectivization_le (N : ℕ) :
    #(Projectivization ℂ (Fin (N + 1) → ℂ)) ≤ 𝔠 := by
  calc #(Projectivization ℂ (Fin (N + 1) → ℂ))
      ≤ #{v : Fin (N + 1) → ℂ // v ≠ 0} :=
        Cardinal.mk_le_of_surjective
          (f := fun v : {v : Fin (N + 1) → ℂ // v ≠ 0} => Projectivization.mk ℂ v.1 v.2)
          (Projectivization.ind fun v hv => ⟨⟨v, hv⟩, rfl⟩)
    _ ≤ #(Fin (N + 1) → ℂ) := Cardinal.mk_subtype_le _
    _ = 𝔠 ^ ((N + 1 : ℕ) : Cardinal) := by
        rw [← Cardinal.power_def, Cardinal.mk_complex, Cardinal.mk_fin]
    _ ≤ 𝔠 := Cardinal.power_nat_le aleph0_le_continuum

/-! ### No variety in the repository has a complex point -/

theorem isEmpty_hom (V : SmoothProjectiveVariety ℂ) :
    IsEmpty (Spec (CommRingCat.of ℂ) ⟶ V.X) := by
  refine ⟨fun f => ?_⟩
  have hup : #(Spec (CommRingCat.of ℂ) ⟶ V.X) ≤ 𝔠 := by
    calc #(Spec (CommRingCat.of ℂ) ⟶ V.X)
        = #V.realization.points :=
          (Cardinal.mk_congr V.realization.points_equiv_scheme_points).symm
      _ ≤ #(Projectivization ℂ
            (Fin (V.realization.projective_embedding.ambient_dimension + 1) → ℂ)) :=
          Cardinal.mk_le_of_injective V.realization.projective_embedding.injective
      _ ≤ 𝔠 := card_projectivization_le _
  let φ : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ := Spec.preimage (f ≫ V.structure_map)
  have hf : f ≫ V.structure_map = Spec.map φ := (Spec.map_preimage _).symm
  obtain ⟨S, hS, ρ, hρ⟩ := exists_perm_family φ.hom
  have hinj : Function.Injective
      (fun σ : Equiv.Perm S => Spec.map (CommRingCat.ofHom (ρ σ)) ≫ f) := by
    intro σ σ' h
    apply hρ
    have h2 := congrArg (fun g => g ≫ V.structure_map) h
    simp only [Category.assoc, hf, ← Spec.map_comp] at h2
    have h3 := Spec.map_injective h2
    have h4 := congrArg CommRingCat.Hom.hom h3
    simpa [CommRingCat.hom_comp] using h4
  haveI : Infinite S := Cardinal.infinite_iff.2 (by rw [hS]; exact aleph0_le_continuum)
  have hlow : 𝔠 < #(Spec (CommRingCat.of ℂ) ⟶ V.X) := by
    calc 𝔠 < 2 ^ 𝔠 := Cardinal.cantor _
      _ = #(Equiv.Perm S) := by rw [Cardinal.mk_perm_eq_two_power, hS]
      _ ≤ _ := Cardinal.mk_le_of_injective hinj
  exact absurd hup (not_le.2 hlow)

theorem isEmpty_points (V : SmoothProjectiveVariety ℂ) : IsEmpty V.realization.points :=
  haveI := isEmpty_hom V
  V.realization.points_equiv_scheme_points.isEmpty

/-! ### Betti cohomology vanishes -/

theorem isZero_bettiHomology (V : SmoothProjectiveVariety ℂ) (R : Type) [Field R] (n : ℕ) :
    Limits.IsZero (bettiHomology R V n) := by
  haveI : IsEmpty V.realization.points := isEmpty_points V
  haveI : IsEmpty ↑V.realization.top_cat := ‹IsEmpty V.realization.points›
  haveI : TotallyDisconnectedSpace ↑V.realization.top_cat :=
    ⟨fun _ _ _ => Set.subsingleton_of_subsingleton⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine Limits.IsZero.of_iso ?_
      (AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace
        (ModuleCat R) (ModuleCat.of R R) V.realization.top_cat)
    haveI : IsEmpty (Discrete ↑V.realization.top_cat) := ⟨fun x => isEmptyElim x.as⟩
    exact (Limits.isColimitEquivIsInitialOfIsEmpty (C := ModuleCat R) _
      (Limits.coproductIsCoproduct (fun _ : ↑V.realization.top_cat => ModuleCat.of R R))).isZero
  · exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat R) n (ModuleCat.of R R) V.realization.top_cat hn.ne'

theorem subsingleton_bettiCohomology (V : SmoothProjectiveVariety ℂ) (R : Type) [Field R]
    (n : ℕ) : Subsingleton (bettiCohomology R V n) := by
  haveI := ModuleCat.subsingleton_of_isZero (isZero_bettiHomology V R n)
  exact ⟨fun f g => LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩

/-! ### The Millennium target -/

/-- The repository's Hodge target is provable: it has no content. -/
theorem clayHodge : ClayHodge.{u₁, u₂, u₃} := by
  intro realization hcan X p x _hx
  obtain ⟨e⟩ := hcan.rational_cohomology_is_betti X (2 * p)
  haveI := subsingleton_bettiCohomology X ℚ (2 * p)
  haveI : Subsingleton ((realization.assignment.data X).cohomology_q (2 * p)) :=
    e.toEquiv.subsingleton
  exact ⟨0, by rw [map_zero]; exact Subsingleton.elim _ _⟩

end MillenniumHodge.Vacuous
