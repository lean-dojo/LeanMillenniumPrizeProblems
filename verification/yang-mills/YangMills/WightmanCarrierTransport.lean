import YangMills.OperatorCarrierTransport
import YangMills.WightmanVacuumKernels
noncomputable section
set_option maxHeartbeats 1600000
namespace YangMills.CarrierTransport
universe u v
variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Every part of the actual Wightman data is conjugated by the SAME unitary
carrier change. Test functions, component labels and their actions are unchanged. -/
def wightman (e : K ≃ₗᵢ[ℂ] H) (Q : WightmanData H) : WightmanData K where
  domain := Q.domain.comap e.toLinearEquiv.toLinearMap
  vacuum := (domainEquiv e Q.domain).symm Q.vacuum
  componentCount := Q.componentCount
  field i :=
    { toFun := fun f => (domainEquiv e Q.domain).symm.toLinearEquiv.toLinearMap.comp
        ((Q.field i f).comp (domainEquiv e Q.domain).toLinearEquiv.toLinearMap)
      map_add' := by intro f g; ext x; simp
      map_smul' := by intro c f; ext x; simp }
  adjointIndex := Q.adjointIndex
  unitary g := (e.trans (Q.unitary g)).trans e.symm
  domainAction g := ((domainEquiv e Q.domain).toLinearEquiv.trans (Q.domainAction g)).trans
    (domainEquiv e Q.domain).symm.toLinearEquiv
  componentAction := Q.componentAction
  pullback := Q.pullback
  conjugateTest := Q.conjugateTest
  hamiltonian := operator e Q.hamiltonian

@[simp] theorem wightman_vacuum (e : K ≃ₗᵢ[ℂ] H) (Q : WightmanData H) :
    ((wightman e Q).vacuum : K) = e.symm Q.vacuum := rfl

@[simp] theorem wightman_field (e : K ≃ₗᵢ[ℂ] H) (Q : WightmanData H)
    (i : Q.FieldIndex) (f : TestFunction) (x : (wightman e Q).domain) :
    (domainEquiv e Q.domain) ((wightman e Q).field i f x) =
      Q.field i f (domainEquiv e Q.domain x) :=
  (domainEquiv e Q.domain).apply_symm_apply _

@[simp] theorem wightman_unitary (e : K ≃ₗᵢ[ℂ] H) (Q : WightmanData H)
    (g : PoincareTransform) (x : K) :
    (wightman e Q).unitary g x = e.symm (Q.unitary g (e x)) := rfl

@[simp] theorem wightman_word (e : K ≃ₗᵢ[ℂ] H) (Q : WightmanData H)
    (word : List (Q.FieldIndex × TestFunction)) :
    domainEquiv e Q.domain ((wightman e Q).word word) = Q.word word := by
  induction word with
  | nil => exact (domainEquiv e Q.domain).apply_symm_apply _
  | cons head tail ih =>
    cases head with
    | mk i f => simp only [WightmanData.word,wightman_field,ih]

/-- The entire actual ordered vacuum distribution hierarchy is preserved. -/
@[simp] theorem wightman_vacuumNPoint (e : K ≃ₗᵢ[ℂ] H) (Q : WightmanData H)
    (word : List (Q.FieldIndex × TestFunction)) :
    (wightman e Q).vacuumNPoint word = Q.vacuumNPoint word := by
  have hw := congrArg (fun x : Q.domain => (x : H)) (wightman_word e Q word)
  change e ((wightman e Q).word word) = (Q.word word : H) at hw
  change inner ℂ ((wightman e Q).vacuum : K) ((wightman e Q).word word : K) = _
  rw [← e.inner_map_map, wightman_vacuum,LinearIsometryEquiv.apply_symm_apply,hw]
  rfl

/-- Full Schwartz kernels are transported unchanged because all actual
vacuum words are equal, not selected independently for the new theory. -/
def vacuumKernels (e : K ≃ₗᵢ[ℂ] H) (Q : WightmanData H)
    (W : WightmanVacuumKernels Q) : WightmanVacuumKernels (wightman e Q) where
  tensor := W.tensor
  tensor_eq := W.tensor_eq
  tensor_dense := W.tensor_dense
  kernel := W.kernel
  actual_words n indices tests := by
    rw [wightman_vacuumNPoint]
    exact W.actual_words n indices tests

end YangMills.CarrierTransport
