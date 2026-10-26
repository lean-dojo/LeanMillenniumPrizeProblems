import Problems.YangMills.FullBVPhysicalGhostDecomposition

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

def gaugePotentialJet (G : CompactSimpleGaugeGroup) (mu : Fin 4) (a : Fin G.dimension) :
    JetAlgebra G := jet ⟨.inl (.gauge mu a), 0⟩
def gaugeFirstJet (G : CompactSimpleGaugeGroup) (mu nu : Fin 4) (a : Fin G.dimension) :
    JetAlgebra G := jet ⟨.inl (.gauge nu a), Pi.single mu 1⟩
def abelianCurvatureJet (G : CompactSimpleGaugeGroup) (mu nu : Fin 4) (a : Fin G.dimension) :
    JetAlgebra G := gaugeFirstJet G mu nu a - gaugeFirstJet G nu mu a

/-- The explicit current connecting the actual Feynman-gauge kinetic
representative with curvature squared plus gauge fixing. -/
def gluonKineticCurrent (G : CompactSimpleGaugeGroup) (a : Fin G.dimension) (mu : Fin 4) :
    JetAlgebra G :=
  (1 / 2 : ℂ) • (gaugePotentialJet G mu a * gaugeDivergence G a -
    ∑ nu : Fin 4, gaugePotentialJet G nu a * gaugeFirstJet G nu mu a)

theorem totalDerivative_gaugeFirst (rho mu nu : Fin 4) (a : Fin G.dimension) :
    totalDerivative rho (gaugeFirstJet G mu nu a) =
      jet ⟨.inl (.gauge nu a), Pi.single mu 1 + Pi.single rho 1⟩ := by
  exact totalDerivative_jet rho _

theorem gaugeFirst_commute (mu nu rho sigma : Fin 4) (a b : Fin G.dimension) :
    gaugeFirstJet G mu nu a * gaugeFirstJet G rho sigma b =
      gaugeFirstJet G rho sigma b * gaugeFirstJet G mu nu a :=
  gaugeJet_commute _ _ _ _

/-- The second derivatives in the current cancel by the actual jet
multiindex symmetry, with no boundary-condition assumption. -/
theorem gluonKineticCurrent_divergence (a : Fin G.dimension) :
    (∑ mu : Fin 4, totalDerivative mu (gluonKineticCurrent G a mu)) =
      (1 / 2 : ℂ) • (gaugeDivergence G a * gaugeDivergence G a -
        ∑ mu : Fin 4, ∑ nu : Fin 4, gaugeFirstJet G mu nu a * gaugeFirstJet G nu mu a) := by
  have hp (mu nu : Fin 4) :
      totalDerivative mu (gaugePotentialJet G mu a * gaugeFirstJet G nu nu a) =
        gaugeFirstJet G mu mu a * gaugeFirstJet G nu nu a +
          gaugePotentialJet G mu a *
            jet ⟨.inl (.gauge nu a), Pi.single nu 1 + Pi.single mu 1⟩ := by
    unfold gaugePotentialJet gaugeFirstJet
    rw [totalDerivative_mul_jet_ordinary, totalDerivative_jet, totalDerivative_jet]
    simp only [Jet.shift, zero_add]
  have hq (mu nu : Fin 4) :
      totalDerivative mu (gaugePotentialJet G nu a * gaugeFirstJet G nu mu a) =
        gaugeFirstJet G mu nu a * gaugeFirstJet G nu mu a +
          gaugePotentialJet G nu a *
            jet ⟨.inl (.gauge mu a), Pi.single nu 1 + Pi.single mu 1⟩ := by
    unfold gaugePotentialJet gaugeFirstJet
    rw [totalDerivative_mul_jet_ordinary, totalDerivative_jet, totalDerivative_jet]
    simp only [Jet.shift, zero_add]
  have hc : (∑ mu : Fin 4, ∑ nu : Fin 4, gaugePotentialJet G mu a *
      jet ⟨.inl (.gauge nu a), Pi.single nu 1 + Pi.single mu 1⟩) =
      ∑ mu : Fin 4, ∑ nu : Fin 4, gaugePotentialJet G nu a *
        jet ⟨.inl (.gauge mu a), Pi.single nu 1 + Pi.single mu 1⟩ := by
    rw [Finset.sum_comm]
    simp only [add_comm]
  have hd (mu : Fin 4) (P Q : JetAlgebra G) :
      totalDerivative mu (P - Q) = totalDerivative mu P - totalDerivative mu Q :=
    map_sub (totalDerivativeLinear mu) P Q
  unfold gluonKineticCurrent
  simp only [totalDerivative_smul, hd, gaugeDivergence, Finset.mul_sum, totalDerivative_sum]
  change (∑ mu : Fin 4, (1 / 2 : ℂ) •
    ((∑ nu : Fin 4, totalDerivative mu (gaugePotentialJet G mu a * gaugeFirstJet G nu nu a)) -
      ∑ nu : Fin 4, totalDerivative mu (gaugePotentialJet G nu a * gaugeFirstJet G nu mu a))) = _
  simp only [hp, hq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.smul_sum]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hc]
  unfold gaugeFirstJet
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i mu : Fin 4 =>
    jet (G := G) ⟨.inl (.gauge mu a), Pi.single mu 1⟩ *
      jet ⟨.inl (.gauge i a), Pi.single i 1⟩)]
  module

/-- Abelian curvature squared plus the fixed gauge-fixing square is the
same actual free gluon density up to the computed current. -/
theorem freeGluon_curvature_decomposition (a : Fin G.dimension) :
    (∑ mu : Fin 4, ∑ nu : Fin 4,
      (1 / 2 : ℂ) • (gaugeFirstJet G mu nu a * gaugeFirstJet G mu nu a)) +
      (∑ mu : Fin 4, totalDerivative mu (gluonKineticCurrent G a mu)) =
      (∑ mu : Fin 4, ∑ nu : Fin 4,
        (1 / 4 : ℂ) • (abelianCurvatureJet G mu nu a * abelianCurvatureJet G mu nu a)) +
      (1 / 2 : ℂ) • (gaugeDivergence G a * gaugeDivergence G a) := by
  rw [gluonKineticCurrent_divergence]
  have hs : (∑ mu : Fin 4, ∑ nu : Fin 4, gaugeFirstJet G nu mu a * gaugeFirstJet G nu mu a) =
      ∑ mu : Fin 4, ∑ nu : Fin 4, gaugeFirstJet G mu nu a * gaugeFirstJet G mu nu a :=
    Finset.sum_comm
  unfold abelianCurvatureJet
  simp only [sub_mul, mul_sub, gaugeFirst_commute, Finset.smul_sum,
    smul_sub, Finset.sum_sub_distrib]
  simp only [← Finset.smul_sum]
  rw [hs]
  module

end YangMills.FullBV
