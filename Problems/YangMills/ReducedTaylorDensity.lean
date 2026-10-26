import Problems.YangMills.IntegratedWardFlow
import Problems.YangMills.RegulatedWardInsertion

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
open scoped BigOperators
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- A reduced ordered momentum direction is placed on its actual field
factor. No derivative is placed on the eliminated last momentum. -/
def directionBucket {legs : List (ExternalLeg G)}
    (directions : List (Fin legs.length × Fin 4)) (i : Fin legs.length) : List (Fin 4) :=
  directions.filterMap fun d => if d.1 = i then some d.2 else none

def reducedTaylorSource (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4)) : List (LocalVertexLeg G) :=
  List.ofFn fun i : Fin legs.length => ⟨legs.get i, directionBucket directions i⟩

theorem directionBucket_lengths {legs : List (ExternalLeg G)}
    (directions : List (Fin legs.length × Fin 4)) :
    (∑ i : Fin legs.length, (directionBucket directions i).length) = directions.length := by
  classical
  induction directions with
  | nil => simp [directionBucket]
  | cons d ds ih =>
    have h (i : Fin legs.length) :
        (directionBucket (d :: ds) i).length =
          (directionBucket ds i).length + if i = d.1 then 1 else 0 := by
      by_cases hi : i = d.1
      · subst i
        simp [directionBucket, Nat.add_comm]
      · simp [directionBucket, Ne.symm hi, hi]
    simp only [h, Finset.sum_add_distrib, ih, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      List.length_cons]

theorem reducedTaylorSource_degree (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4)) :
    ((reducedTaylorSource legs directions).map
      (fun k => k.field.dimension + k.derivatives.length)).sum =
        totalDimension legs + directions.length := by
  classical
  simp only [reducedTaylorSource, List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  rw [Finset.sum_add_distrib, directionBucket_lengths]
  congr 1
  have h := congrArg (fun l : List (ExternalLeg G) => (l.map ExternalLeg.dimension).sum)
    (List.ofFn_get legs)
  simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, totalDimension] using h

/-- Every coefficient is an actual finite Taylor jet. The factors i^k/k!
and 1/n! respectively invert the Fourier derivative phase and external
functional-derivative multiplicities. Polynomial evaluation performs the
actual graded symmetrization; no commuting ghost evaluation is substituted. -/
def reducedTaylorVertex (F : OrderedAmplitude G) (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4)) : LocalVertex G where
  coefficient :=
    (Complex.I^directions.length /
      ((Nat.factorial legs.length : ℂ) * (Nat.factorial directions.length : ℂ))) *
        momentumJet directions (F legs) 0
  couplingOrder := 0
  legs := reducedTaylorSource legs directions

theorem reducedTaylorVertex_degree (F : OrderedAmplitude G) (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4)) :
    (reducedTaylorVertex F legs directions).degree = totalDimension legs + directions.length :=
  reducedTaylorSource_degree legs directions

/-- Finite local Taylor lift through weighted engineering degree D.
The last momentum is eliminated BEFORE jets are extracted. Summing words
in the actual superalgebra retains all Koszul signs. -/
def reducedTaylorVertices (D : ℕ) (F : OrderedAmplitude G) : List (LocalVertex G) := by
  classical
  exact (List.range (D+1)).flatMap fun n =>
    if n = 0 then [] else
    ((Finset.univ : Finset (Fin n → ExternalLeg G)).toList).flatMap fun fields =>
      let legs := List.ofFn fields
      (List.range (D+1)).flatMap fun k =>
        ((Finset.univ : Finset (Fin k → (Fin legs.length × Fin 4))).toList).filterMap fun dirs =>
          let directions := List.ofFn dirs
          if totalDimension legs + k ≤ D ∧ ReducedDirections legs directions then
            some (reducedTaylorVertex F legs directions) else none

theorem reducedTaylorVertices_degree (D : ℕ) (F : OrderedAmplitude G)
    (v : LocalVertex G) (hv : v ∈ reducedTaylorVertices D F) : v.degree ≤ D := by
  classical
  unfold reducedTaylorVertices at hv
  obtain ⟨n, hn, hv⟩ := List.mem_flatMap.mp hv
  split_ifs at hv with hn0
  · simp at hv
  · obtain ⟨fields, hfields, hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨k, hk, hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨dirs, hdirs, hv⟩ := List.mem_filterMap.mp hv
    dsimp only at hv
    split_ifs at hv with hc
    · have he : reducedTaylorVertex F (List.ofFn fields) (List.ofFn dirs) = v :=
        Option.some.inj hv
      rw [← he, reducedTaylorVertex_degree, List.length_ofFn]
      exact hc.1

def reducedTaylorDensity (D : ℕ) (F : OrderedAmplitude G) : FullBV.JetAlgebra G :=
  FullBV.densityOfVertices 1 (reducedTaylorVertices D F)

/-- The proposed finite normalization map is computed from the integrated
kernel's actual subtraction-scale jets. Its reconstruction theorem must
establish balanced-jet recovery; no such equality is postulated here. -/
def integratedTaylorDensity (D : ℕ) (I : ScaleCouplingFamily G)
    (μ g : ℝ) (loop : ℕ) (UV : ℝ) : FullBV.JetAlgebra G :=
  reducedTaylorDensity D (I μ g loop μ UV)

end YangMills.IntegratedNormalization
