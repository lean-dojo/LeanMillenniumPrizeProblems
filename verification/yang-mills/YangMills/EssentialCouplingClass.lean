import YangMills.CanonicalJetEuler
noncomputable section
set_option maxHeartbeats 600000
open scoped BigOperators
namespace YangMills.FullBV
open YangMills.Perturbative YangMills.PerturbativeFlow YangMills.FieldParameter YangMills.ScaleInsertion
variable {G : CompactSimpleGaugeGroup}

/-- Antifield-free part of the literal fixed action. Gauge fixing and
physical ghosts are retained; cohomological removal is a separate identity. -/
def antifieldFreeDensity (g : ℝ) (terms : List (LocalVertex G)) : JetAlgebra G :=
  (terms.map (fun v => if isPhysicalVertex v then densityOfVertex g v else 0)).sum

theorem couplingVariation_densityVertex (v : LocalVertex G) (g : ℝ) :
    (g : ℂ) • densityOfVertex g (differentiateCouplingVertex v) =
      (v.couplingOrder : ℂ) • densityOfVertex g v := by
  unfold densityOfVertex differentiateCouplingVertex
  rw [smul_smul, smul_smul]
  apply congrArg (fun c : ℂ => c • monomial v.legs)
  cases h : v.couplingOrder with
  | zero => simp
  | succ n => simp only [Nat.add_sub_cancel, pow_succ]; ring

theorem jetEuler_densityVertex (v : LocalVertex G) (g : ℝ) :
    jetEuler allCanonicalWeights (densityOfVertex g v) =
      (vertexEulerWeight v : ℂ) • densityOfVertex g v := by
  rw [densityOfVertex, jetEuler_smul, jetEuler_monomial]
  rw [smul_smul, smul_smul]
  congr 1
  unfold vertexEulerWeight
  ring

theorem masterVertex_density_euler {B : InvariantForm G} (frame : ColorFrame B)
    (v : LocalVertex G) (hv : v ∈ freeActionVertices G ++ treeActionVertices frame) (g : ℝ) :
    jetEuler allCanonicalWeights (densityOfVertex g v) =
      (g : ℂ) • densityOfVertex g (differentiateCouplingVertex v) +
        (2 : ℂ) • (if isPhysicalVertex v then densityOfVertex g v else 0) := by
  rw [jetEuler_densityVertex, couplingVariation_densityVertex, masterVertex_homogeneity frame v hv]
  by_cases hp : isPhysicalVertex v = true <;> simp [hp, add_smul]

theorem vertices_density_euler {B : InvariantForm G} (frame : ColorFrame B)
    (terms : List (LocalVertex G))
    (subset : ∀ v ∈ terms, v ∈ freeActionVertices G ++ treeActionVertices frame) (g : ℝ) :
    jetEuler allCanonicalWeights (densityOfVertices g terms) =
      (g : ℂ) • densityOfVertices g (terms.map differentiateCouplingVertex) +
        (2 : ℂ) • antifieldFreeDensity g terms := by
  induction terms with
  | nil => simp [densityOfVertices, antifieldFreeDensity, jetEuler, coordinateDifferential]
  | cons v vs ih =>
    have hv := subset v (by simp)
    have hs : ∀ w ∈ vs, w ∈ freeActionVertices G ++ treeActionVertices frame :=
      fun w hw => subset w (by simp [hw])
    simp only [densityOfVertices, antifieldFreeDensity, List.map_cons, List.sum_cons, jetEuler_add]
    change jetEuler allCanonicalWeights (densityOfVertex g v) +
      jetEuler allCanonicalWeights (densityOfVertices g vs) = _
    rw [masterVertex_density_euler frame v hv g, ih hs]
    simp only [smul_add]
    abel

theorem freeVertex_couplingOrder (v : LocalVertex G) (hv : v ∈ freeActionVertices G) :
    v.couplingOrder = 0 := by
  simp [freeActionVertices] at hv
  aesop

theorem freeDensity_coupling_independent (g : ℝ) :
    densityOfVertices g (freeActionVertices G) = freeActionDensity G := by
  unfold freeActionDensity densityOfVertices
  apply congrArg List.sum
  apply List.map_congr_left
  intro v hv
  simp [densityOfVertex, freeVertex_couplingOrder v hv]

theorem masterDensity_eq_vertices {B : InvariantForm G} (frame : ColorFrame B) (g : ℝ) :
    masterActionDensity frame g = densityOfVertices g (freeActionVertices G ++ treeActionVertices frame) := by
  rw [densityOfVertices, List.map_append, List.sum_append]
  change _ = densityOfVertices g (freeActionVertices G) + densityOfVertices g (treeActionVertices frame)
  rw [freeDensity_coupling_independent]
  rfl

/-- The essential-coupling normalization bridge in the ACTUAL local
functional quotient of the same master action. No nontriviality or
classification of the remaining physical-action class is assumed here. -/
theorem essentialCoupling_class_relation {B : InvariantForm G} (frame : ColorFrame B) (g : ℝ) :
    (g : ℂ) • localClass (couplingVariationDensity frame g) +
      (2 : ℂ) • localClass (antifieldFreeDensity g (freeActionVertices G ++ treeActionVertices frame)) =
    localSTFunctional (masterActionDensity frame g)
      (localClass (rescalingGenerator allCanonicalWeights)) := by
  rw [← jetEuler_exact, masterDensity_eq_vertices,
    vertices_density_euler frame _ (fun _ h => h)]
  change _ = (divergences G).mkQ _
  rw [map_add, map_smul, map_smul]
  rfl

end YangMills.FullBV
