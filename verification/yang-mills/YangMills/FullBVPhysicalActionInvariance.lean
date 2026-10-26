import YangMills.FullBVCurvatureActionInvariance
import YangMills.FullBVGaugeFermionNilpotency
import YangMills.FullBVLocalIntegration
noncomputable section
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- The actual free-plus-interacting physical density, retaining the
Feynman-gauge ghosts and shifted auxiliary field and excluding only sources. -/
def physicalGaugeFixedDensity {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) : JetAlgebra G :=
  freeGluonDensity G + freeGhostDensity G + auxiliarySquareDensity G +
    densityOfVertices g (physicalCubicVertices e) +
    densityOfVertices g (physicalQuarticVertices e) +
    densityOfVertices g (physicalGhostVertices e)

theorem physicalGaugeFixedDensity_decomposition {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) :
    physicalGaugeFixedDensity e g + kineticCurrentDivergence G + ghostCurrentDivergence e g =
      gluonCurvatureDensity e g + classicalLocalSTDensity e g (gaugeFermionDensity G) := by
  have hs : masterActionDensity e g = physicalGaugeFixedDensity e g + fullAntifieldDensity e g :=
    masterDensity_physical_antifield e g
  apply add_right_cancel (b := fullAntifieldDensity e g)
  calc
    _ = masterActionDensity e g + kineticCurrentDivergence G + ghostCurrentDivergence e g := by
      rw [hs]; abel
    _ = _ := masterDensity_gaugeFermion_curvature e g

/-- A completely explicit current for the physical action's Ward variation. -/
def physicalWardCurrent {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (a : Fin G.dimension) (mu : Fin 4) : JetAlgebra G :=
  classicalLocalSTDensity e g (gluonKineticCurrent G a mu) +
    classicalLocalSTDensity e g (gaugeFermionCurrent e g a mu)

/-- The physical action's actual ST variation is a fixed total divergence.
This is derived using only proved basic nilpotency, curvature covariance,
the same action's fixed gauge fermion and evolutionary prolongation. -/
theorem classicalLocalST_physicalGaugeFixed_current {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) :
    classicalLocalSTDensity e g (physicalGaugeFixedDensity e g) +
      (∑ a : Fin G.dimension, ∑ mu : Fin 4,
        totalDerivative mu (physicalWardCurrent e g a mu)) = 0 := by
  have hs := congrArg (classicalLocalSTDensity e g)
    (physicalGaugeFixedDensity_decomposition e g)
  change localST (masterActionDensity e g) _ = localST (masterActionDensity e g) _ at hs
  simp only [localST_add] at hs
  change (classicalLocalSTDensity e g (physicalGaugeFixedDensity e g) +
    classicalLocalSTDensity e g (kineticCurrentDivergence G)) +
    classicalLocalSTDensity e g (ghostCurrentDivergence e g) =
    classicalLocalSTDensity e g (gluonCurvatureDensity e g) +
      classicalLocalSTDensity e g (classicalLocalSTDensity e g (gaugeFermionDensity G)) at hs
  rw [classicalLocalST_curvatureDensity, classicalLocalST_square_gaugeFermion,
    add_zero] at hs
  unfold kineticCurrentDivergence ghostCurrentDivergence classicalLocalSTDensity at hs
  simp only [localST_sum, ← totalDerivative_localST] at hs
  unfold physicalWardCurrent classicalLocalSTDensity
  simp only [totalDerivative_add, Finset.sum_add_distrib]
  convert hs using 1; abel

/-- Actual local-functional BRST invariance of the SAME physical action.
It does not assert or assume the remaining full antifield master equation. -/
theorem classicalLocalST_physicalGaugeFixed_class {B : InvariantForm G}
    (e : ColorFrame B) (g : ℝ) :
    localClass (classicalLocalSTDensity e g (physicalGaugeFixedDensity e g)) = 0 := by
  have hs := congrArg (divergences G).mkQ (classicalLocalST_physicalGaugeFixed_current e g)
  change localClass (_ + _) = localClass (0 : JetAlgebra G) at hs
  change (divergences G).mkQ (_ + _) = (divergences G).mkQ (0 : JetAlgebra G) at hs
  simp only [map_add, map_sum, map_zero] at hs
  change localClass (classicalLocalSTDensity e g (physicalGaugeFixedDensity e g)) +
    (∑ a : Fin G.dimension, ∑ mu : Fin 4,
      localClass (totalDerivative mu (physicalWardCurrent e g a mu))) = 0 at hs
  simpa only [totalDerivative_class_zero, Finset.sum_const_zero, add_zero] using hs

end YangMills.FullBV
