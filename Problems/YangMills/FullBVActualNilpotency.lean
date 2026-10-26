import Problems.YangMills.FullBVActualGhostAntifieldNilpotency
import Problems.YangMills.FullBVNilpotencyPromotion
import Problems.YangMills.FullBVLocalIntegration

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 2600000
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- All eight actual basic/antifield species have square zero for the SAME
full interacting master action. No CME or nilpotency premise is used. -/
theorem classicalLocalST_square_coordinate {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (field : ExternalLeg G) :
    classicalLocalSTDensity e g (classicalLocalSTDensity e g (jet ⟨field,0⟩)) = 0 := by
  cases field with
  | inl K => exact classicalLocalST_square_basic e g K
  | inr K =>
    cases K with
    | gauge mu a => exact classicalLocalST_square_gaugeAntifield e g mu a
    | ghost a => exact classicalLocalST_square_ghostAntifield e g a
    | antighost a => exact classicalLocalST_square_antiantighost e g a
    | auxiliary a => exact classicalLocalST_square_antiauxiliary e g a

/-- All spacetime descendants of all eight actual BV species. -/
theorem classicalLocalST_square_jet {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (j : Jet G) :
    classicalLocalSTDensity e g (classicalLocalSTDensity e g (jet j)) = 0 :=
  localST_square_jet_of_coordinate _ j.field
    (classicalLocalST_square_coordinate e g j.field) j.derivative

/-- Full pointwise nilpotency on the concrete polynomial/exterior jet algebra,
including all antifields and every local descendant. -/
theorem classicalLocalST_square {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (P : JetAlgebra G) :
    classicalLocalSTDensity e g (classicalLocalSTDensity e g P) = 0 :=
  localST_square_of_jets _ (parity_masterActionDensity e g)
    (classicalLocalST_square_jet e g) P

end YangMills.FullBV
