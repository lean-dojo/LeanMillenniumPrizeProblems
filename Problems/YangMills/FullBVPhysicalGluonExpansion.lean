import Problems.YangMills.FullBVGluonKineticDecomposition
import Problems.YangMills.FullBVActualQuarticColor

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
open YangMills.PerturbativeFlow YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

def liftInteractionVertex (m : InteractionMonomial G) : LocalVertex G :=
  { coefficient := (m.coefficient : ℂ), couplingOrder := m.couplingOrder,
    legs := m.legs.map (fun k => ⟨.inl k.field, k.derivatives⟩) }
def physicalCubicVertices {B : InvariantForm G} (e : ColorFrame B) : List (LocalVertex G) :=
  (cubicMonomials e).map liftInteractionVertex
def physicalQuarticVertices {B : InvariantForm G} (e : ColorFrame B) : List (LocalVertex G) :=
  (quarticMonomials e).map liftInteractionVertex

def gluonBracketJet {B : InvariantForm G} (e : ColorFrame B)
    (mu nu : Fin 4) (a : Fin G.dimension) : JetAlgebra G :=
  ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
    (structureConstant e a b c : ℂ) • (gaugePotentialJet G mu b * gaugePotentialJet G nu c)

def nonabelianCurvatureJet {B : InvariantForm G} (e : ColorFrame B) (g : ℝ)
    (mu nu : Fin 4) (a : Fin G.dimension) : JetAlgebra G :=
  abelianCurvatureJet G mu nu a + (g : ℂ) • gluonBracketJet e mu nu a

theorem physicalCubicDensity_expansion {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    densityOfVertices g (physicalCubicVertices e) =
      ∑ mu : Fin 4, ∑ nu : Fin 4, ∑ a : Fin G.dimension,
        ∑ b : Fin G.dimension, ∑ c : Fin G.dimension,
          (((1 / 2 : ℂ) * (structureConstant e a b c : ℂ) * (g : ℂ)) •
            ((gaugeFirstJet G mu nu a * gaugePotentialJet G mu b) * gaugePotentialJet G nu c) +
          ((-(1 / 2 : ℂ)) * (structureConstant e a b c : ℂ) * (g : ℂ)) •
            ((gaugeFirstJet G nu mu a * gaugePotentialJet G mu b) * gaugePotentialJet G nu c)) := by
  unfold densityOfVertices physicalCubicVertices cubicMonomials
  simp only [List.bind_eq_flatMap, List.map_map, Function.comp_def, List.map_flatMap,
    sum_list_flatMap, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  simp only [← List.ofFn_eq_map, List.map_ofFn, List.sum_ofFn, Function.comp_def,
    List.map_cons, List.map_nil, liftInteractionVertex, densityOfVertex_triple,
    vertexJet_nil, vertexJet_single, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_neg]
  rfl

theorem densityOfVertex_quartic (c : ℂ) (g : ℝ) (i j k l : LocalVertexLeg G) :
    densityOfVertex g (⟨c, 2, [i,j,k,l]⟩ : LocalVertex G) =
      (c * (g : ℂ)^2) •
        (((jet (vertexJet i) * jet (vertexJet j)) * jet (vertexJet k)) * jet (vertexJet l)) := by
  simp [densityOfVertex, monomial, vertexJet, mul_assoc]

theorem physicalQuarticDensity_expansion {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    densityOfVertices g (physicalQuarticVertices e) =
      ∑ mu : Fin 4, ∑ nu : Fin 4, ∑ a : Fin G.dimension,
        ∑ b : Fin G.dimension, ∑ c : Fin G.dimension, ∑ d : Fin G.dimension,
          (((1 / 4 : ℂ) * (fourColor B (e.basis a) (e.basis b) (e.basis c) (e.basis d) : ℂ) *
            (g : ℂ)^2) • (((gaugePotentialJet G mu a * gaugePotentialJet G nu b) *
              gaugePotentialJet G mu c) * gaugePotentialJet G nu d)) := by
  unfold densityOfVertices physicalQuarticVertices quarticMonomials
  simp only [List.bind_eq_flatMap, List.map_map, Function.comp_def, List.map_flatMap,
    sum_list_flatMap, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  simp only [← List.ofFn_eq_map, List.map_ofFn, List.sum_ofFn, Function.comp_def,
    List.map_cons, List.map_nil, liftInteractionVertex, densityOfVertex_quartic,
    vertexJet_nil, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
  rfl

/-- The cubic terms obtained from expanding the same nonabelian curvature. -/
theorem physicalCubicDensity_curvature {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) :
    densityOfVertices g (physicalCubicVertices e) =
      ∑ mu : Fin 4, ∑ nu : Fin 4, ∑ a : Fin G.dimension,
        ((1 / 2 : ℂ) * (g : ℂ)) •
          (abelianCurvatureJet G mu nu a * gluonBracketJet e mu nu a) := by
  rw [physicalCubicDensity_expansion]
  unfold abelianCurvatureJet gluonBracketJet
  simp only [Finset.mul_sum, mul_smul_comm, Finset.smul_sum, sub_mul, smul_sub,
    mul_assoc, smul_smul]
  apply Finset.sum_congr rfl
  intro mu hmu
  apply Finset.sum_congr rfl
  intro nu hnu
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  module

end YangMills.FullBV
