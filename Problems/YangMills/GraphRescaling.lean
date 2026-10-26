import Problems.YangMills.EssentialCouplingClass

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 600000
open scoped BigOperators TensorProduct
namespace YangMills.FullBV
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- Graph grading scales every extended jet, including antifields, equally.
This is an actual superalgebra map; it is NOT a canonical BV scheme change. -/
def graphRescale (t : ℂ) : JetAlgebra G →ₐ[ℂ] JetAlgebra G :=
  Algebra.TensorProduct.map
    (MvPolynomial.aeval (fun j : EvenJet G => t • MvPolynomial.X j))
    (ExteriorAlgebra.map (t • (LinearMap.id : (OddJet G →₀ ℂ) →ₗ[ℂ] (OddJet G →₀ ℂ))))

@[simp] theorem graphRescale_evenJet (t : ℂ) (j : EvenJet G) :
    graphRescale t (evenJet j) = t • evenJet j := by
  simp [graphRescale, evenJet, Algebra.TensorProduct.map_tmul, TensorProduct.smul_tmul']

@[simp] theorem graphRescale_oddJet (t : ℂ) (j : OddJet G) :
    graphRescale t (oddJet j) = t • oddJet j := by
  simp only [graphRescale, oddJet, Algebra.TensorProduct.map_tmul, map_one,
    ExteriorAlgebra.map_apply_ι, LinearMap.smul_apply, LinearMap.id_apply]
  rw [map_smul, TensorProduct.tmul_smul]

@[simp] theorem graphRescale_jet (t : ℂ) (j : Jet G) :
    graphRescale t (jet j) = t • jet j := by
  by_cases hj : j.field.parity = true <;> simp [jet, hj]

/-- Full ordered superwords have their literal nonnegative graph degree. -/
theorem graphRescale_monomial (t : ℂ) (source : List (LocalVertexLeg G)) :
    graphRescale t (monomial source) = t^source.length • monomial source := by
  induction source with
  | nil => simp [monomial]
  | cons k source ih =>
    rw [monomial_cons, map_mul, graphRescale_jet, ih]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    simp only [List.length_cons, pow_succ]
    congr 1
    ring

/-- The fixed source and physical master vertices share the same graph
count; the antifield variables count as genuine extended legs here. -/
theorem masterVertex_graph_count {B : InvariantForm G} (frame : ColorFrame B)
    (v : LocalVertex G) (hv : v ∈ freeActionVertices G ++ treeActionVertices frame) :
    v.couplingOrder + 2 = v.legs.length := by
  simp only [List.mem_append] at hv
  rcases hv with hv | hv
  · simp [freeActionVertices] at hv
    aesop
  · simp [treeActionVertices, physicalActionVertices, actionMonomials, cubicMonomials,
      quarticMonomials, ghostMonomials, antifieldActionVertices] at hv
    aesop

theorem graphRescale_masterVertex {B : InvariantForm G} (frame : ColorFrame B)
    (v : LocalVertex G) (hv : v ∈ freeActionVertices G ++ treeActionVertices frame) (g : ℝ) :
    graphRescale (g : ℂ) (densityOfVertex 1 v) = (g : ℂ)^2 • densityOfVertex g v := by
  simp only [densityOfVertex, map_smul, graphRescale_monomial]
  simp only [Complex.ofReal_one, one_pow, mul_one]
  rw [smul_smul, smul_smul, ← masterVertex_graph_count frame v hv, pow_add]
  congr 1
  ring

/-- Division-free graph normalization of the SAME actual master action,
valid also at g=0. No Laurent or independently chosen action is introduced. -/
theorem graphRescale_masterDensity {B : InvariantForm G} (frame : ColorFrame B) (g : ℝ) :
    graphRescale (g : ℂ) (masterActionDensity frame 1) = (g : ℂ)^2 • masterActionDensity frame g := by
  rw [masterDensity_eq_vertices, masterDensity_eq_vertices]
  unfold densityOfVertices
  rw [map_list_sum, List.map_map, List.smul_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro v hv
  exact graphRescale_masterVertex frame v hv g

end YangMills.FullBV
