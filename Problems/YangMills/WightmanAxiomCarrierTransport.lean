import Problems.YangMills.WightmanCarrierTransport
import Mathlib.Analysis.Calculus.Deriv.Comp

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 2400000
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
namespace YangMills.CarrierTransport
open MeasureTheory
universe u v
variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Real-parameter generator derivatives commute with the actual unitary
carrier change. -/
theorem hasDerivAt_carrier (e : K ≃ₗᵢ[ℂ] H) (f : ℝ → K) (w : K) (t : ℝ) :
    HasDerivAt (fun r => e (f r)) (e w) t ↔ HasDerivAt f w t := by
  constructor
  · intro h
    have hh := (e.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h
    change HasDerivAt (fun r => e.symm (e (f r))) (e.symm (e w)) t at hh
    simpa only [LinearIsometryEquiv.symm_apply_apply] using! hh
  · intro h
    exact (e.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h

/-- All operator axioms survive literal unitary carrier transport. -/
theorem wightman_axioms (e : K ≃ₗᵢ[ℂ] H) (Q : WightmanData H)
    (h : WightmanAxioms H Q) : WightmanAxioms K (wightman e Q) := by
  letI : CompleteSpace H := h.complete
  letI : CompleteSpace K := e.toIsometryEquiv.completeSpace_iff.mpr h.complete
  letI : TopologicalSpace.SeparableSpace H := h.separable
  refine {
    complete := inferInstance
    separable := e.symm.surjective.denseRange.separableSpace e.symm.continuous
    dense_domain := h.dense_domain.preimage e.toHomeomorph.isOpenMap
    vacuum_norm := by simpa only [wightman_vacuum,LinearIsometryEquiv.norm_map] using! h.vacuum_norm
    unitary_identity := ?_
    unitary_comp := ?_
    strongly_continuous := ?_
    domain_action := ?_
    vacuum_invariant := ?_
    vacuum_unique := ?_
    spectral_integrable := ?_
    spectral_support := ?_
    field_continuous := ?_
    conjugateTest_eq := h.conjugateTest_eq
    adjoint_involution := h.adjoint_involution
    adjoint_relation := ?_
    component_identity := h.component_identity
    component_comp := h.component_comp
    component_continuous := h.component_continuous
    component_translation := h.component_translation
    pullback_eq := h.pullback_eq
    covariance := ?_
    locality := ?_
    cyclic := ?_
    selfAdjoint := operator_selfAdjoint e Q.hamiltonian h.selfAdjoint
    generator_domain := ?_
    generator_action := ?_
    spectrum_real := ?_
    positive_energy := ?_
    vacuum_mem := ?_
    vacuum_zero := ?_ }
  · intro x
    simp only [wightman_unitary,h.unitary_identity,LinearIsometryEquiv.symm_apply_apply]
  · intro g j x
    simp only [wightman_unitary,LinearIsometryEquiv.apply_symm_apply,h.unitary_comp]
  · intro x
    exact e.symm.continuous.comp (h.strongly_continuous (e x))
  · intro g x
    change e.symm (Q.domainAction g (domainEquiv e Q.domain x) : H) = _
    rw [h.domain_action]
    rfl
  · intro g
    simp only [wightman_unitary,wightman_vacuum,LinearIsometryEquiv.apply_symm_apply,h.vacuum_invariant]
  · intro x hx
    obtain ⟨c,hc⟩ := h.vacuum_unique (e x) (by
      intro a
      have hh := congrArg e (hx a)
      simpa only [wightman_unitary,LinearIsometryEquiv.apply_symm_apply] using! hh)
    refine ⟨c,?_⟩
    apply e.injective
    simpa only [map_smul,wightman_vacuum,LinearIsometryEquiv.apply_symm_apply] using! hc
  · intro f x
    have hi := e.symm.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp (h.spectral_integrable f (e x))
    simpa only [map_smul,wightman_unitary] using! hi
  · intro f hf x
    change (∫ a : Spacetime, WightmanData.spectralKernel f a • e.symm
      (Q.unitary (PoincareTransform.translate a) (e x))) = 0
    calc
      _ = ∫ a : Spacetime, e.symm (WightmanData.spectralKernel f a •
          Q.unitary (PoincareTransform.translate a) (e x)) := by
        apply integral_congr_ae
        filter_upwards [] with a
        exact (map_smul e.symm _ _).symm
      _ = e.symm (∫ a : Spacetime, WightmanData.spectralKernel f a •
          Q.unitary (PoincareTransform.translate a) (e x)) :=
        e.symm.toContinuousLinearEquiv.integral_comp_comm _
      _ = 0 := by rw [h.spectral_support f hf (e x),map_zero]
  · intro i x
    change Continuous (fun f => e.symm (Q.field i f (domainEquiv e Q.domain x) : H))
    exact e.symm.continuous.comp (h.field_continuous i _)
  · intro i f x y
    have hh := h.adjoint_relation i f (domainEquiv e Q.domain x) (domainEquiv e Q.domain y)
    change inner ℂ (e.symm (Q.field i f (domainEquiv e Q.domain x) : H)) (y : K) =
      inner ℂ (x : K) (e.symm (Q.field (Q.adjointIndex i) (Q.conjugateTest f) (domainEquiv e Q.domain y) : H))
    rw [← e.inner_map_map,← e.inner_map_map (x : K),LinearIsometryEquiv.apply_symm_apply,
      LinearIsometryEquiv.apply_symm_apply]
    exact hh
  · intro g n i f x
    apply (domainEquiv e Q.domain).injective
    have action (g : PoincareTransform) (y : (wightman e Q).domain) :
        domainEquiv e Q.domain ((wightman e Q).domainAction g y) =
          Q.domainAction g (domainEquiv e Q.domain y) :=
      (domainEquiv e Q.domain).apply_symm_apply _
    simpa only [action,map_sum,map_smul,wightman_field] using!
      h.covariance g n i f (domainEquiv e Q.domain x)
  · intro i j f g hf x
    apply (domainEquiv e Q.domain).injective
    simpa only [wightman_field] using! h.locality i j f g hf (domainEquiv e Q.domain x)
  · have hd := e.symm.surjective.denseRange.dense_image e.symm.continuous h.cyclic
    apply hd.mono
    rintro x ⟨y,hy,rfl⟩
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨word,rfl⟩ := hy
      apply Submodule.subset_span
      refine ⟨word,?_⟩
      apply e.injective
      simpa only [LinearIsometryEquiv.apply_symm_apply,domainEquiv_coe] using!
        congrArg (fun z : Q.domain => (z : H)) (wightman_word e Q word)
    | zero => simpa only [map_zero] using! (Submodule.zero_mem _)
    | add x y _ _ hx hy => simpa only [map_add] using! Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa only [map_smul] using! Submodule.smul_mem _ c hx
  · intro x
    constructor
    · rintro ⟨w,hw⟩
      apply (h.generator_domain (e x)).mp
      refine ⟨e w,?_⟩
      have hh := (hasDerivAt_carrier e _ w 0).mpr hw
      simpa only [WightmanData.timeTranslation,wightman_unitary,LinearIsometryEquiv.apply_symm_apply] using! hh
    · intro hx
      obtain ⟨w,hw⟩ := (h.generator_domain (e x)).mpr hx
      refine ⟨e.symm w,?_⟩
      apply (hasDerivAt_carrier e _ _ 0).mp
      simpa only [WightmanData.timeTranslation,wightman_unitary,LinearIsometryEquiv.apply_symm_apply] using! hw
  · intro x
    apply (hasDerivAt_carrier e _ _ 0).mp
    change HasDerivAt (fun t => e (e.symm (Q.timeTranslation t (e x))))
      (e (Complex.I • e.symm (Q.hamiltonian.toLinearMap
        (domainEquiv e Q.hamiltonian.domain x)))) 0
    simpa only [map_smul,LinearIsometryEquiv.apply_symm_apply,domainEquiv_coe] using!
      h.generator_action (domainEquiv e Q.hamiltonian.domain x)
  · simpa only [wightman,operator_spectrum] using! h.spectrum_real
  · simpa only [wightman,operator_realSpectrum] using! h.positive_energy
  · change e (e.symm (Q.vacuum : H)) ∈ Q.hamiltonian.domain
    simpa only [LinearIsometryEquiv.apply_symm_apply] using! h.vacuum_mem
  · apply e.injective
    change e (e.symm (Q.hamiltonian.toLinearMap
      ⟨e (e.symm (Q.vacuum : H)),_⟩)) = e 0
    simpa only [LinearIsometryEquiv.apply_symm_apply,map_zero] using! h.vacuum_zero

end YangMills.CarrierTransport
