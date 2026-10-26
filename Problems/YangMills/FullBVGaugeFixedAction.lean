import Problems.YangMills.FullBVPhysicalCurvatureSquared

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

def freeGluonDensity (G : CompactSimpleGaugeGroup) : JetAlgebra G :=
  ∑ a : Fin G.dimension, ∑ mu : Fin 4, ∑ nu : Fin 4,
    (1 / 2 : ℂ) • (gaugeFirstJet G mu nu a * gaugeFirstJet G mu nu a)
def freeGhostDensity (G : CompactSimpleGaugeGroup) : JetAlgebra G :=
  ∑ mu : Fin 4, ∑ a : Fin G.dimension,
    jet ⟨.inl (.antighost a), Pi.single mu 1⟩ * jet ⟨.inl (.ghost a), Pi.single mu 1⟩
def auxiliarySquareDensity (G : CompactSimpleGaugeGroup) : JetAlgebra G :=
  ∑ a : Fin G.dimension, (1 / 2 : ℂ) • (auxiliaryJet G a * auxiliaryJet G a)
def gaugeFixingSquareDensity (G : CompactSimpleGaugeGroup) : JetAlgebra G :=
  ∑ a : Fin G.dimension, (1 / 2 : ℂ) • (gaugeDivergence G a * gaugeDivergence G a)

def freeAntifieldDensity (G : CompactSimpleGaugeGroup) : JetAlgebra G :=
  ∑ a : Fin G.dimension,
    ((-Complex.I) • (auxiliaryJet G a * jet ⟨.inr (.antighost a), 0⟩) +
    ∑ mu : Fin 4,
      ((-1 : ℂ) • (jet ⟨.inl (.ghost a), Pi.single mu 1⟩ * jet ⟨.inr (.gauge mu a), 0⟩) +
      (-1 : ℂ) • (gaugeFirstJet G mu mu a * jet ⟨.inr (.antighost a), 0⟩) +
      (-Complex.I) • (jet ⟨.inl (.ghost a), Pi.single mu 2⟩ * jet ⟨.inr (.auxiliary a), 0⟩)))

def fullAntifieldDensity {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) : JetAlgebra G :=
  freeAntifieldDensity G + nonlinearSourceDensity e g

def gluonCurvatureDensity {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) : JetAlgebra G :=
  ∑ mu : Fin 4, ∑ nu : Fin 4, ∑ a : Fin G.dimension,
    (1 / 4 : ℂ) •
      (nonabelianCurvatureJet e g mu nu a * nonabelianCurvatureJet e g mu nu a)

def abelianCurvatureDensity (G : CompactSimpleGaugeGroup) : JetAlgebra G :=
  ∑ mu : Fin 4, ∑ nu : Fin 4, ∑ a : Fin G.dimension,
    (1 / 4 : ℂ) • (abelianCurvatureJet G mu nu a * abelianCurvatureJet G mu nu a)

def kineticCurrentDivergence (G : CompactSimpleGaugeGroup) : JetAlgebra G :=
  ∑ a : Fin G.dimension, ∑ mu : Fin 4, totalDerivative mu (gluonKineticCurrent G a mu)
def ghostCurrentDivergence {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) : JetAlgebra G :=
  ∑ a : Fin G.dimension, ∑ mu : Fin 4, totalDerivative mu (gaugeFermionCurrent e g a mu)

private theorem sum_rotate_three {I J K M : Type*}
    [Fintype I] [Fintype J] [Fintype K] [AddCommMonoid M] (f : I → J → K → M) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ j, ∑ k, ∑ i, f i j k := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j hj
  exact Finset.sum_comm

/-- Exact free physical/source decomposition of the SAME master action. -/
theorem freeDensity_physical_antifield :
    freeActionDensity G = freeGluonDensity G + freeGhostDensity G +
      auxiliarySquareDensity G + freeAntifieldDensity G := by
  rw [freeActionDensity_eq_quadratic]
  unfold freeDensityQuadratic freeGluonDensity freeGhostDensity auxiliarySquareDensity
    freeAntifieldDensity auxiliaryJet gaugeFirstJet
  rw [Finset.sum_comm (f := fun mu a =>
    jet (G := G) ⟨.inl (.antighost a), Pi.single mu 1⟩ *
      jet ⟨.inl (.ghost a), Pi.single mu 1⟩)]
  simp only [Finset.sum_add_distrib]
  abel

theorem physicalDensity_split {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    densityOfVertices g (physicalActionVertices e) =
      densityOfVertices g (physicalCubicVertices e) +
      densityOfVertices g (physicalQuarticVertices e) +
      densityOfVertices g (physicalGhostVertices e) := by
  have hs : physicalActionVertices e = physicalCubicVertices e ++
      physicalQuarticVertices e ++ physicalGhostVertices e := by
    simp only [physicalActionVertices, actionMonomials, List.map_append,
      physicalCubicVertices, physicalQuarticVertices, physicalGhostVertices]
    rfl
  rw [hs, densityOfVertices_append, densityOfVertices_append]

theorem masterDensity_physical_antifield {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    masterActionDensity e g =
      freeGluonDensity G + freeGhostDensity G + auxiliarySquareDensity G +
      densityOfVertices g (physicalCubicVertices e) +
      densityOfVertices g (physicalQuarticVertices e) +
      densityOfVertices g (physicalGhostVertices e) + fullAntifieldDensity e g := by
  rw [masterActionDensity, freeDensity_physical_antifield, interactionDensity,
    densityOfVertices_append, physicalDensity_split, antifieldDensity_eq_nonlinearSource]
  unfold fullAntifieldDensity
  abel

theorem kineticDensity_gaugeFixing :
    freeGluonDensity G + kineticCurrentDivergence G =
      abelianCurvatureDensity G + gaugeFixingSquareDensity G := by
  unfold freeGluonDensity kineticCurrentDivergence abelianCurvatureDensity gaugeFixingSquareDensity
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ a : Fin G.dimension,
      ((∑ mu : Fin 4, ∑ nu : Fin 4,
        (1 / 4 : ℂ) • (abelianCurvatureJet G mu nu a * abelianCurvatureJet G mu nu a)) +
        (1 / 2 : ℂ) • (gaugeDivergence G a * gaugeDivergence G a)) := by
      apply Finset.sum_congr rfl; intro a ha
      exact freeGluon_curvature_decomposition a
    _ = _ := by
      rw [Finset.sum_add_distrib, sum_rotate_three]

theorem ghostDensity_gaugeFixing {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    gaugeFixingSquareDensity G + auxiliarySquareDensity G + freeGhostDensity G +
      densityOfVertices g (physicalGhostVertices e) + ghostCurrentDivergence e g =
      classicalLocalSTDensity e g (gaugeFermionDensity G) := by
  have hp := physicalGhost_sector_same_vertices e g
  change (∑ mu : Fin 4, ∑ a : Fin G.dimension,
    jet ⟨.inl (.antighost a), Pi.single mu 1⟩ *
      stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a))) =
      freeGhostDensity G + densityOfVertices g (physicalGhostVertices e) at hp
  rw [add_assoc (gaugeFixingSquareDensity G + auxiliarySquareDensity G), ← hp]
  have hs := gaugeFixedSector_gaugeFermion e g
  unfold gaugeFixedGhostAuxiliaryDensity at hs
  simp only [Finset.sum_add_distrib] at hs
  change (∑ a : Fin G.dimension,
    (1 / 2 : ℂ) • (gaugeDivergence G a * gaugeDivergence G a)) +
    (∑ a : Fin G.dimension, (1 / 2 : ℂ) • (auxiliaryJet G a * auxiliaryJet G a)) +
    (∑ a : Fin G.dimension, ∑ mu : Fin 4,
      jet ⟨.inl (.antighost a), Pi.single mu 1⟩ *
        stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a))) +
    ghostCurrentDivergence e g = _ at hs
  rw [Finset.sum_comm (f := fun a mu =>
    jet (G := G) ⟨.inl (.antighost a), Pi.single mu 1⟩ *
      stCharacteristic (masterActionDensity e g) (.inl (.gauge mu a)))] at hs
  exact hs

/-- The full actual BV master density has the fixed gauge-invariant
curvature action, the actual ST gauge-fermion term and its actual antifield
sources, with a completely explicit divergence. No master equation or
BRST invariance is postulated in this identity. -/
theorem masterDensity_gaugeFermion_curvature {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    masterActionDensity e g + kineticCurrentDivergence G + ghostCurrentDivergence e g =
      gluonCurvatureDensity e g + classicalLocalSTDensity e g (gaugeFermionDensity G) +
        fullAntifieldDensity e g := by
  have hc : gluonCurvatureDensity e g = abelianCurvatureDensity G +
      densityOfVertices g (physicalCubicVertices e) +
      densityOfVertices g (physicalQuarticVertices e) := nonabelianCurvature_square_expansion e g
  rw [masterDensity_physical_antifield]
  calc
    _ = (freeGluonDensity G + kineticCurrentDivergence G) +
      freeGhostDensity G + auxiliarySquareDensity G +
      densityOfVertices g (physicalCubicVertices e) +
      densityOfVertices g (physicalQuarticVertices e) +
      densityOfVertices g (physicalGhostVertices e) + ghostCurrentDivergence e g +
      fullAntifieldDensity e g := by abel
    _ = _ := by
      rw [kineticDensity_gaugeFixing, hc, ← ghostDensity_gaugeFixing]
      abel

end YangMills.FullBV
