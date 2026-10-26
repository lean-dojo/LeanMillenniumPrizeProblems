import Problems.YangMills.QFT.Wightman

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unnecessarySimpa false
namespace YangMills.CarrierTransport
universe u v
variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The domain is pulled back, including its entire graph, by a unitary
carrier change e:K→H. It is never replaced by a more convenient core. -/
def domainEquiv (e : K ≃ₗᵢ[ℂ] H) (D : Submodule ℂ H) :
    D.comap e.toLinearEquiv.toLinearMap ≃ₗᵢ[ℂ] D where
  toFun x := ⟨e x,x.property⟩
  invFun y := ⟨e.symm y,by simpa using y.property⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y
  map_add' _ _ := by apply Subtype.ext; exact map_add e _ _
  map_smul' _ _ := by apply Subtype.ext; exact map_smul e _ _
  norm_map' x := e.norm_map x

@[simp] theorem domainEquiv_apply (e : K ≃ₗᵢ[ℂ] H) (D : Submodule ℂ H)
    (x : D.comap e.toLinearEquiv.toLinearMap) :
    domainEquiv e D x = ⟨e x, x.property⟩ := rfl

@[simp] theorem domainEquiv_coe (e : K ≃ₗᵢ[ℂ] H) (D : Submodule ℂ H)
    (x : D.comap e.toLinearEquiv.toLinearMap) : (domainEquiv e D x : H) = e x := rfl

@[simp] theorem domainEquiv_symm_coe (e : K ≃ₗᵢ[ℂ] H) (D : Submodule ℂ H)
    (x : D) : ((domainEquiv e D).symm x : K) = e.symm x := rfl

/-- Exact conjugation of an unbounded operator and its dense full domain. -/
def operator (e : K ≃ₗᵢ[ℂ] H) (A : DenselyDefinedOperator H) : DenselyDefinedOperator K where
  domain := A.domain.comap e.toLinearEquiv.toLinearMap
  toLinearMap := e.symm.toLinearEquiv.toLinearMap.comp
    (A.toLinearMap.comp (domainEquiv e A.domain).toLinearEquiv.toLinearMap)
  dense_domain := A.dense_domain.preimage e.toHomeomorph.isOpenMap

@[simp] theorem operator_apply (e : K ≃ₗᵢ[ℂ] H) (A : DenselyDefinedOperator H)
    (x : (operator e A).domain) :
    (operator e A).toLinearMap x = e.symm (A.toLinearMap (domainEquiv e A.domain x)) := rfl

/-- The complete adjoint-graph condition is preserved, with no new hypotheses. -/
theorem operator_selfAdjoint (e : K ≃ₗᵢ[ℂ] H) (A : DenselyDefinedOperator H)
    (h : A.IsSelfAdjoint) : (operator e A).IsSelfAdjoint := by
  intro x y
  constructor
  · intro hx
    have hz : ∀ u : A.domain, inner ℂ (A.toLinearMap u) (e x) = inner ℂ (u : H) (e y) := by
      intro u
      have hu := hx ((domainEquiv e A.domain).symm u)
      simpa only [operator_apply,domainEquiv_symm_coe,LinearIsometryEquiv.apply_symm_apply,
        LinearIsometryEquiv.symm_apply_apply] using
        (e.inner_map_map _ _).trans (hu.trans (e.inner_map_map _ _).symm)
    obtain ⟨hm,he⟩ := (h (e x) (e y)).mp hz
    refine ⟨hm,?_⟩
    apply e.injective
    simpa only [operator_apply,domainEquiv_apply,LinearIsometryEquiv.apply_symm_apply] using he
  · rintro ⟨hm,he⟩ u
    have hz := (h (e x) (e y)).mpr ⟨hm,by
      have hh := congrArg e he
      simpa only [operator_apply,domainEquiv_apply,LinearIsometryEquiv.apply_symm_apply] using hh⟩ (domainEquiv e A.domain u)
    have hi := e.inner_map_map (e.symm (A.toLinearMap (domainEquiv e A.domain u))) x
    rw [LinearIsometryEquiv.apply_symm_apply] at hi
    exact hi.symm.trans (hz.trans (e.inner_map_map u y))

/-- Both bounded inverse laws and the range-in-domain condition transport. -/
theorem operator_resolvent (e : K ≃ₗᵢ[ℂ] H) (A : DenselyDefinedOperator H) (z : ℂ)
    (h : A.InResolvent z) : (operator e A).InResolvent z := by
  obtain ⟨R,hR,hr,hl⟩ := h
  let R' := e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (R.comp e.toContinuousLinearEquiv.toContinuousLinearMap)
  have hR' (x : K) : R' x ∈ (operator e A).domain := by
    change e (e.symm (R (e x))) ∈ A.domain
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hR (e x)
  refine ⟨R',hR',?_,?_⟩
  · intro x
    apply e.injective
    simp only [operator_apply,map_sub,map_smul,LinearIsometryEquiv.apply_symm_apply]
    change A.toLinearMap ⟨e (e.symm (R (e x))),_⟩ -
      z • e (e.symm (R (e x))) = e x
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hr (e x)
  · intro x
    apply e.injective
    simpa only [R',ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe,operator_apply,map_sub,map_smul,
      LinearIsometryEquiv.apply_symm_apply,domainEquiv_coe] using hl (domainEquiv e A.domain x)

/-- Conjugation preserves the full resolvent, including continuous spectrum. -/
theorem operator_resolvent_iff (e : K ≃ₗᵢ[ℂ] H) (A : DenselyDefinedOperator H) (z : ℂ) :
    (operator e A).InResolvent z ↔ A.InResolvent z := by
  constructor
  · rintro ⟨R,hR,hr,hl⟩
    let R' := e.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (R.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap)
    have hR' (x : H) : R' x ∈ A.domain := hR (e.symm x)
    refine ⟨R',hR',?_,?_⟩
    · intro x
      have hh := congrArg e (hr (e.symm x))
      simpa only [R',ContinuousLinearMap.comp_apply,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe,
        operator_apply,map_sub,map_smul,domainEquiv_apply,LinearIsometryEquiv.apply_symm_apply] using hh
    · intro x
      have hh := congrArg e (hl ((domainEquiv e A.domain).symm x))
      simpa only [R',ContinuousLinearMap.comp_apply,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe,
        operator_apply,map_sub,map_smul,LinearIsometryEquiv.apply_symm_apply,
        LinearIsometryEquiv.symm_apply_apply,domainEquiv_symm_coe] using hh
  · exact operator_resolvent e A z

@[simp] theorem operator_spectrum (e : K ≃ₗᵢ[ℂ] H) (A : DenselyDefinedOperator H) :
    (operator e A).spectrum = A.spectrum := by
  ext z
  exact not_congr (operator_resolvent_iff e A z)

@[simp] theorem operator_realSpectrum (e : K ≃ₗᵢ[ℂ] H) (A : DenselyDefinedOperator H) :
    (operator e A).realSpectrum = A.realSpectrum := by
  ext r
  exact not_congr (operator_resolvent_iff e A r)

end YangMills.CarrierTransport
