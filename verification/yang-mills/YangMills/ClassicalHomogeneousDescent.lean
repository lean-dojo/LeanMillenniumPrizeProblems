import YangMills.ClassicalHomogeneousProjection
import YangMills.ClassicalRecenter

noncomputable section
namespace YangMills.CurvatureJetPolynomial
variable {G : CompactSimpleGaugeGroup}

/-- Centering an actual smooth connection makes dilation test its jets at any
chosen point, without assuming that arbitrary jet assignments are realizable. -/
theorem scalePolynomial_eval_onConnection (p : CurvatureJetPolynomial G)
    (A : Connection G) (x : Spacetime) (scale : ℝ) :
    (scalePolynomial p (fun j => j.evaluate A x)).eval scale =
      p.onConnection ((A.recenter x).dilate scale) 0 := by
  rw [scalePolynomial_eval, onConnection_dilate]
  unfold evaluate scaleJets
  apply congrArg (fun assignment : CurvatureJetCoordinate G → ℝ => MvPolynomial.eval assignment p)
  funext c
  simp only [smul_zero, CurvatureJet.evaluate_recenter, zero_add]
  rfl

/-- Relations holding on all actual smooth connections split by engineering
degree. In particular, no extra formal-jet injectivity assumption is used. -/
theorem engineeringPart_respects (degree : ℕ) {p q : CurvatureJetPolynomial G}
    (same : sameOnConnections p q) :
    sameOnConnections (engineeringPart degree p) (engineeringPart degree q) := by
  intro A x
  have identity : scalePolynomial p (fun j => j.evaluate A x) =
      scalePolynomial q (fun j => j.evaluate A x) := by
    apply Polynomial.funext
    intro scale
    rw [scalePolynomial_eval_onConnection, scalePolynomial_eval_onConnection]
    exact same ((A.recenter x).dilate scale) 0
  have coefficient := congrArg (fun P : Polynomial ℝ => P.coeff degree) identity
  simpa only [scalePolynomial_coeff, onConnection] using coefficient

namespace ConnectionObservable
/-- The actual classical connection-observable quotient admits canonical
engineering-degree projections. -/
def engineeringPart (degree : ℕ) : ConnectionObservable G → ConnectionObservable G :=
  Quotient.map (invariantEngineeringPart degree) (by
    intro p q same
    funext A x
    exact engineeringPart_respects degree (fun A x => congrFun (congrFun same A) x) A x)

@[simp] theorem engineeringPart_mk (degree : ℕ) (p : invariantAlgebra G) :
    engineeringPart degree (Quotient.mk (connectionSetoid G) p) =
      Quotient.mk (connectionSetoid G) (invariantEngineeringPart degree p) := rfl

/-- Quotient-level engineering projections are idempotent. -/
theorem engineeringPart_idempotent (degree : ℕ) (o : ConnectionObservable G) :
    engineeringPart degree (engineeringPart degree o) = engineeringPart degree o := by
  induction o using Quotient.inductionOn with
  | _ p =>
    apply congrArg (Quotient.mk (connectionSetoid G))
    apply Subtype.ext
    exact (CurvatureJetPolynomial.engineeringPart_part degree degree p.val).trans (if_pos rfl)

/-- Different degrees are orthogonal even after all actual differential
identities on connections have been quotiented out. -/
theorem engineeringPart_orthogonal (degree other : ℕ) (different : degree ≠ other)
    (o : ConnectionObservable G) :
    engineeringPart degree (engineeringPart other o) =
      Quotient.mk (connectionSetoid G) (0 : invariantAlgebra G) := by
  induction o using Quotient.inductionOn with
  | _ p =>
    apply congrArg (Quotient.mk (connectionSetoid G))
    apply Subtype.ext
    exact (CurvatureJetPolynomial.engineeringPart_part degree other p.val).trans (if_neg different)

/-- A representative's redundant high-degree terms cannot create a nonzero
component above the intrinsic quotient filtration. -/
theorem engineeringPart_eq_zero_of_filtered (degree bound : ℕ) (higher : bound < degree)
    {o : ConnectionObservable G} (bounded : HasDimensionAtMost bound o) :
    engineeringPart degree o = Quotient.mk (connectionSetoid G) (0 : invariantAlgebra G) := by
  obtain ⟨p, equal, hp⟩ := bounded
  rw [← equal, engineeringPart_mk]
  apply congrArg (Quotient.mk (connectionSetoid G))
  apply Subtype.ext
  exact CurvatureJetPolynomial.engineeringPart_eq_zero_of_bound degree bound higher hp

end ConnectionObservable
end YangMills.CurvatureJetPolynomial
