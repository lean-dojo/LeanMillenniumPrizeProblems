import YangMills.SmallHilbertCarrier
import YangMills.WightmanAxiomCarrierTransport
noncomputable section
namespace YangMills.CarrierTransport
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A small presentation is an actual unitary change of carrier of the
original Wightman data, rather than a second unrelated theory. -/
structure SmallWightmanPresentation (Q : WightmanData H) where
  State : Type
  [normed : NormedAddCommGroup State]
  [innerProduct : InnerProductSpace ℂ State]
  carrier : State ≃ₗᵢ[ℂ] H
  axioms : WightmanAxioms State (wightman carrier Q)

attribute [instance] SmallWightmanPresentation.normed SmallWightmanPresentation.innerProduct

/-- Every universe-polymorphic separable Wightman theory has a Type0
unitarily equivalent presentation with the full SAME operator axioms. -/
def smallWightmanPresentation (Q : WightmanData H) (h : WightmanAxioms H Q) :
    SmallWightmanPresentation Q := by
  letI : TopologicalSpace.SeparableSpace H := h.separable
  letI : Small.{0} H := separableMetric_small H
  exact {
    State := Shrink.{0} H
    normed := SmallHilbert.normed H
    innerProduct := SmallHilbert.innerProduct H
    carrier := SmallHilbert.carrier H
    axioms := wightman_axioms (SmallHilbert.carrier H) Q h }

/-- The gap is the same numerical property of the exact same resolvent
spectrum after transport; no eigenvector or isolation assumption is added. -/
theorem SmallWightmanPresentation.gapped (Q : WightmanData H)
    (P : SmallWightmanPresentation Q) (h : GappedWightmanTheory H Q) :
    GappedWightmanTheory P.State (wightman P.carrier Q) where
  axioms := P.axioms
  massGap := by simpa only [wightman,operator_realSpectrum] using h.massGap

/-- Full actual tempered vacuum kernels are available on the small carrier
whenever they are available on the original one. -/
def SmallWightmanPresentation.kernels (Q : WightmanData H)
    (P : SmallWightmanPresentation Q) (W : WightmanVacuumKernels Q) :
    WightmanVacuumKernels (wightman P.carrier Q) := vacuumKernels P.carrier Q W

/-- The numerical mass defined by the source's supremum of gaps is unchanged. -/
theorem SmallWightmanPresentation.realSpectrum (Q : WightmanData H)
    (P : SmallWightmanPresentation Q) :
    (wightman P.carrier Q).hamiltonian.realSpectrum = Q.hamiltonian.realSpectrum :=
  operator_realSpectrum P.carrier Q.hamiltonian

end YangMills.CarrierTransport
