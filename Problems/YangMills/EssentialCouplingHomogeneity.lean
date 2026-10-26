import Problems.YangMills.LegendreFlowAdapters
import Problems.YangMills.ActionProbeSupport

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 600000
open scoped BigOperators
namespace YangMills.ScaleInsertion
open YangMills.Perturbative YangMills.PerturbativeFlow YangMills.FieldParameter
variable {G : CompactSimpleGaugeGroup}

def allCanonicalWeights : BasicScales := ⟨1,1,1,1⟩
def vertexEulerWeight (v : LocalVertex G) : ℝ :=
  (v.legs.map (fun j => eulerWeight allCanonicalWeights j.field)).sum

def isPhysicalLeg : ExternalLeg G → Bool
  | .inl _ => true
  | .inr _ => false

def isPhysicalVertex (v : LocalVertex G) : Bool := v.legs.all (fun j => isPhysicalLeg j.field)

theorem eulerWeight_basic (K : BasicField G) :
    eulerWeight allCanonicalWeights (.inl K) = 1 := by
  cases K <;> rfl

theorem eulerWeight_antifield (K : BasicField G) :
    eulerWeight allCanonicalWeights (.inr K) = -1 := by
  cases K <;> rfl

/-- The actual ordered derivative has the same signed basic/antifield
weight as its consumed source monomial, with no commuting-ghost evaluation. -/
theorem eulerAction_vertex (v : LocalVertex G) (g : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    eulerAction allCanonicalWeights (localVertexAmplitude v g) legs q =
      (vertexEulerWeight v : ℂ) * localVertexAmplitude v g legs q := by
  by_cases hz : localVertexAmplitude v g legs q = 0
  · simp [eulerAction, hz]
  · have hd : localMonomialDerivative v.legs (List.ofFn (fun i => (legs.get i, q i))) ≠ 0 := by
      intro h
      apply hz
      unfold localVertexAmplitude
      rw [h, mul_zero]
    have hp := YangMills.WardAction.localDerivative_support _ _ hd
    have he : (List.ofFn (fun i => (legs.get i, q i))).map Prod.fst = legs := by
      simp only [List.map_ofFn, Function.comp_def, List.ofFn_get]
    rw [he] at hp
    have hw := (hp.map (eulerWeight allCanonicalWeights)).sum_eq
    unfold eulerAction vertexEulerWeight
    rw [← hw, List.map_map]
    rfl

theorem couplingVariation_vertex (v : LocalVertex G) (g : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    (g : ℂ) * localVertexAmplitude (differentiateCouplingVertex v) g legs q =
      (v.couplingOrder : ℂ) * localVertexAmplitude v g legs q := by
  cases h : v.couplingOrder with
  | zero => simp [localVertexAmplitude, differentiateCouplingVertex, h]
  | succ n => simp only [localVertexAmplitude, differentiateCouplingVertex, h, Nat.add_sub_cancel,
      pow_succ]; ring

/-- Physical vertices have two more canonical field weights than powers
of g; antifield source vertices have equal weight and coupling power. -/
theorem masterVertex_homogeneity {B : InvariantForm G} (frame : ColorFrame B)
    (v : LocalVertex G) (hv : v ∈ freeActionVertices G ++ treeActionVertices frame) :
    vertexEulerWeight v = (v.couplingOrder : ℝ) + if isPhysicalVertex v then 2 else 0 := by
  have htwo : (1 : ℝ)+1=2 := by norm_num
  have hthree : (1 : ℝ)+2=3 := by norm_num
  have hfour : (1 : ℝ)+3=4 := by norm_num
  have hfour' : (2 : ℝ)+2=4 := by norm_num
  simp only [List.mem_append] at hv
  rcases hv with hv | hv
  · simp [freeActionVertices] at hv
    aesop (add simp [vertexEulerWeight, eulerWeight_basic, eulerWeight_antifield,
      isPhysicalVertex, isPhysicalLeg, htwo, hthree, hfour, hfour'])
  · simp [treeActionVertices, physicalActionVertices, actionMonomials, cubicMonomials,
      quarticMonomials, ghostMonomials, antifieldActionVertices] at hv
    aesop (add simp [vertexEulerWeight, eulerWeight_basic, eulerWeight_antifield,
      isPhysicalVertex, isPhysicalLeg, htwo, hthree, hfour, hfour'])


def physicalMasterAmplitude {B : InvariantForm G} (frame : ColorFrame B) (g : ℝ) : OrderedAmplitude G :=
  fun legs q => ((freeActionVertices G ++ treeActionVertices frame).map
    (fun v => if isPhysicalVertex v then localVertexAmplitude v g legs q else 0)).sum

def masterCouplingVariation {B : InvariantForm G} (frame : ColorFrame B) (g : ℝ) : OrderedAmplitude G :=
  localPolynomialAmplitude
    ((freeActionVertices G ++ treeActionVertices frame).map differentiateCouplingVertex) g

theorem masterVertex_euler_identity {B : InvariantForm G} (frame : ColorFrame B)
    (v : LocalVertex G) (hv : v ∈ freeActionVertices G ++ treeActionVertices frame)
    (g : ℝ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    eulerAction allCanonicalWeights (localVertexAmplitude v g) legs q =
      (g : ℂ) * localVertexAmplitude (differentiateCouplingVertex v) g legs q +
        2 * (if isPhysicalVertex v then localVertexAmplitude v g legs q else 0) := by
  rw [eulerAction_vertex, couplingVariation_vertex, masterVertex_homogeneity frame v hv]
  by_cases hp : isPhysicalVertex v = true <;> simp [hp]
  ring

/-- Exact normalization bridge for the actual G-specific fixed master
vertices: its essential coupling deformation differs from canonical field
rescaling by twice the antifield-free physical action. The remaining
cohomology argument must identify the rescaling/gauge-fixing terms as exact
and prove that the curvature-square class survives. -/
theorem master_coupling_euler_identity {B : InvariantForm G} (frame : ColorFrame B) (g : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    eulerAction allCanonicalWeights
      (localPolynomialAmplitude (freeActionVertices G ++ treeActionVertices frame) g) legs q =
    (g : ℂ) * masterCouplingVariation frame g legs q + 2 * physicalMasterAmplitude frame g legs q := by
  unfold eulerAction localPolynomialAmplitude masterCouplingVariation physicalMasterAmplitude
  rw [← List.sum_map_mul_left]
  have hterms := List.map_congr_left (l := freeActionVertices G ++ treeActionVertices frame)
    (fun v hv => masterVertex_euler_identity frame v hv g legs q)
  change (List.map (fun v => eulerAction allCanonicalWeights (localVertexAmplitude v g) legs q)
    (freeActionVertices G ++ treeActionVertices frame)).sum = _
  rw [hterms, List.sum_map_add, List.sum_map_mul_left, List.sum_map_mul_left]
  simp only [localPolynomialAmplitude, List.map_map, Function.comp_def]


/-- The deformation in the normalization bridge is the actual real
coupling derivative of every ordered master-action amplitude. -/
theorem masterCouplingVariation_hasDerivAt {B : InvariantForm G} (frame : ColorFrame B)
    (g : ℝ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    HasDerivAt (fun t : ℝ => localPolynomialAmplitude
      (freeActionVertices G ++ treeActionVertices frame) t legs q)
      (masterCouplingVariation frame g legs q) g :=
  polynomialCoupling_hasDerivAt _ legs q g

end YangMills.ScaleInsertion
