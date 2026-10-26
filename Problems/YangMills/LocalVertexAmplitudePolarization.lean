import Problems.YangMills.FourierTaylorEnumeration

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

noncomputable section
open scoped BigOperators
namespace YangMills.IntegratedNormalization
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- Exact all-arity polarization of an actual local vertex, with its source
indices transported to the external index type. Its own coefficient and
coupling order are retained literally. -/
theorem localVertexAmplitude_permutation_sum (v : LocalVertex G) (g : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (arity : v.legs.length = legs.length) :
    localVertexAmplitude v g legs q =
      (v.coefficient * (g : ℂ)^v.couplingOrder) *
        ∑ π : Equiv.Perm (Fin legs.length),
          assignedVertexTerm
            (fun j => v.legs.get (Fin.cast arity.symm j))
            (fun i => (legs.get i, q i)) π := by
  have hs : v.legs = List.ofFn (fun j => v.legs.get (Fin.cast arity.symm j)) := by
    conv_lhs => rw [← List.ofFn_get v.legs]
    rw [List.ofFn_congr arity]
  unfold localVertexAmplitude
  conv_lhs => rw [hs]
  rw [localMonomialDerivative_permutation_sum]

/-- Literal Taylor-vertex specialization of the all-arity expansion. Source
momentum directions are transported together with their source fields. -/
theorem reducedTaylorVertex_permutation_sum (F : OrderedAmplitude G)
    (source legs : List (ExternalLeg G))
    (directions : List (Fin source.length × Fin 4))
    (q : Fin legs.length → Spacetime) (arity : source.length = legs.length) :
    localVertexAmplitude (reducedTaylorVertex F source directions) 1 legs q =
      (Complex.I^directions.length /
        ((Nat.factorial source.length : ℂ) * (Nat.factorial directions.length : ℂ)) *
          momentumJet directions (F source) 0) *
        ∑ π : Equiv.Perm (Fin legs.length),
          assignedVertexTerm
            (fun j => ⟨source.get (Fin.cast arity.symm j),
              directionBucket directions (Fin.cast arity.symm j)⟩)
            (fun i => (legs.get i, q i)) π := by
  have ha : (reducedTaylorVertex F source directions).legs.length = legs.length := by
    simpa only [reducedTaylorVertex, reducedTaylorSource, List.length_ofFn] using arity
  have he := localVertexAmplitude_permutation_sum
    (reducedTaylorVertex F source directions) 1 legs q ha
  simpa only [reducedTaylorVertex, pow_zero, mul_one, reducedTaylorSource,
    List.get_ofFn, Fin.cast_cast] using he

end YangMills.IntegratedNormalization
