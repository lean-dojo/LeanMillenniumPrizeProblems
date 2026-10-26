import YangMills.InsertionContractionDilation

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators ContDiff
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative MeasureTheory
variable {G : CompactSimpleGaugeGroup}

def dilateInsertionIndex (a : ℝ) (input : List (PositionedInsertion G)) :
    Fin input.length ≃ Fin (dilateInsertionPoints a input).length :=
  finCongr (by simp [dilateInsertionPoints])

@[simp] lemma get_dilateInsertionPoints (a : ℝ) (input : List (PositionedInsertion G))
    (k : Fin input.length) :
    (dilateInsertionPoints a input).get (dilateInsertionIndex a input k) =
      ⟨(input.get k).monomial,a⁻¹ • (input.get k).position⟩ := by
  simp [dilateInsertionPoints,dilateInsertionIndex,finCongr]

lemma positionedInsertionDegreeSum_spectators (input : List (PositionedInsertion G))
    (k l : Fin input.length) (ordered : k < l) :
    positionedInsertionDegreeSum input = (input.get k).monomial.dimension +
      (input.get l).monomial.dimension + positionedInsertionDegreeSum (insertionSpectators input k l) := by
  have distinct : k ≠ l := ne_of_lt ordered
  have sum_input : positionedInsertionDegreeSum input = ∑ i : Fin input.length, (input.get i).monomial.dimension := by
    unfold positionedInsertionDegreeSum
    have eq : input.map (fun A => A.monomial.dimension) =
        List.ofFn (fun i : Fin input.length => (input.get i).monomial.dimension) := by
      simpa only [List.ofFn_get] using
        (List.ofFn_comp' input.get (fun A => A.monomial.dimension)).symm
    rw [eq,List.sum_ofFn]
  have sum_rest : positionedInsertionDegreeSum (insertionSpectators input k l) =
      ∑ i ∈ Finset.univ \ ({k,l} : Finset (Fin input.length)), (input.get i).monomial.dimension := by
    unfold positionedInsertionDegreeSum insertionSpectators
    simp only [List.map_map,Function.comp_def]
    rw [← List.sum_toFinset _ (Finset.sort_nodup _ _),Finset.sort_toFinset]
  rw [sum_input,sum_rest]
  have partition := Finset.sum_add_sum_compl ({k,l} : Finset (Fin input.length))
    (fun i => (input.get i).monomial.dimension)
  change (∑ i, (input.get i).monomial.dimension) = _ +
    ∑ i ∈ ({k,l} : Finset (Fin input.length))ᶜ, (input.get i).monomial.dimension
  simpa only [Finset.sum_pair distinct] using partition.symm

lemma flowProduct_scaleFlow_left (c : ℂ) (A B : FlowFamily G) :
    flowProduct (scaleFlow c A) B = scaleFlow c (flowProduct A B) := by
  funext loop Λ UV legs q
  simp only [flowProduct,amplitudeProduct,scaleFlow]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro s _
  ring

lemma insertionPairSign_dilate (a : ℝ) (input : List (PositionedInsertion G))
    (k l : Fin input.length) :
    insertionPairSign (dilateInsertionPoints a input)
      (dilateInsertionIndex a input k) (dilateInsertionIndex a input l) =
      insertionPairSign input k l := by
  unfold insertionPairSign
  apply congrArg (fun n : ℕ => (-1 : ℂ)^n)
  symm
  let e := dilateInsertionIndex a input
  apply Finset.sum_equiv e
  · intro i
    change i ∈ ({k,l} : Finset _) ↔ e i ∈ ({e k,e l} : Finset _)
    simp
  · intro i _
    apply Finset.sum_equiv e
    · intro j
      change j ∈ Finset.univ \ ({k,l} : Finset _) ↔ e j ∈ Finset.univ \ ({e k,e l} : Finset _)
      simp
    · intro j _
      simp only [e,get_dilateInsertionPoints]
      have order : (dilateInsertionIndex a input j < dilateInsertionIndex a input i) = (j < i) := by rfl
      simp only [order]

lemma insertionSpectators_dilate (a : ℝ) (input : List (PositionedInsertion G))
    (k l : Fin input.length) :
    insertionSpectators (dilateInsertionPoints a input)
      (dilateInsertionIndex a input k) (dilateInsertionIndex a input l) =
      dilateInsertionPoints a (insertionSpectators input k l) := by
  let e := dilateInsertionIndex a input
  have sets : (Finset.univ \ ({k,l} : Finset (Fin input.length))).map e.toEmbedding =
      Finset.univ \ {e k,e l} := by
    ext i
    obtain ⟨j,rfl⟩ := e.surjective i
    simp
  have sorted : ((Finset.univ \ ({k,l} : Finset (Fin input.length))).sort (· ≤ ·)).map e =
      ((Finset.univ \ {e k,e l}).sort (· ≤ ·)) := by
    have mapped := Finset.map_sort (s := Finset.univ \ ({k,l} : Finset (Fin input.length)))
      (r := fun x y : Fin input.length => x ≤ y)
      (r' := fun x y : Fin (dilateInsertionPoints a input).length => x ≤ y)
      (f := e.toEmbedding) (by intro i _ j _; rfl)
    rw [sets] at mapped
    exact mapped
  unfold insertionSpectators
  change List.map _ ((Finset.univ \ {e k,e l}).sort (· ≤ ·)) = _
  rw [← sorted,List.map_map]
  unfold dilateInsertionPoints
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  exact get_dilateInsertionPoints a input i

lemma independentContractionRHS_rescaleFamily (a : ℝ) (positive : 0 < a)
    (D E : ℕ) (parity : Bool) (A B : FlowFamily G) :
    (fun r scale uv external momenta => independentContractionRHS parity
      (rescaleDegree a D A) (rescaleDegree a E B) r scale uv external momenta) =
      scaleFlow (a : ℂ) (rescaleDegree a (D+E)
        (fun r scale uv external momenta => independentContractionRHS parity A B r scale uv external momenta)) := by
  have nonzero : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt positive)
  funext loop Λ UV legs q
  rw [independentContractionRHS_rescaleDegree a positive]
  simp only [scaleFlow,rescaleDegree,Complex.ofReal_zpow,Nat.cast_add]
  rw [zpow_add_one₀ nonzero]
  have power : (totalDimension legs : ℤ)-D-E = (totalDimension legs : ℤ)-(D+E) := by ring
  rw [power]
  ring

/-- The pair channel and its actual graded spectator product transform as
one fixed inhomogeneous source. The additional scalar is the scale derivative. -/
theorem insertionPairSource_rescale (a : ℝ) (positive : 0 < a) (L : InsertedFlowFamily G)
    (input : List (PositionedInsertion G)) (k l : Fin input.length) (ordered : k < l) :
    insertionPairSource (rescaleInsertedFlow a L) input k l =
      scaleFlow (a : ℂ) (rescaleDegree a (positionedInsertionDegreeSum input)
        (insertionPairSource L (dilateInsertionPoints a input)
          (dilateInsertionIndex a input k) (dilateInsertionIndex a input l))) := by
  have singleton (i : Fin input.length) :
      rescaleInsertedFlow a L [input.get i] =
        rescaleDegree a (input.get i).monomial.dimension
          (L [(dilateInsertionPoints a input).get (dilateInsertionIndex a input i)]) := by
    rw [get_dilateInsertionPoints]
    exact rescaleInsertedFlow_single a L (input.get i).monomial (input.get i).position
  have source_degree := positionedInsertionDegreeSum_spectators input k l ordered
  unfold insertionPairSource
  simp only [get_dilateInsertionPoints,insertionPairSign_dilate,insertionSpectators_dilate]
  rw [singleton,singleton,independentContractionRHS_rescaleFamily a positive,
    singleInsertionProduct_rescale a positive,flowProduct_scaleFlow_left,
    flowProduct_rescaleDegree a positive]
  rw [← source_degree]
  funext loop Λ UV legs q
  simp only [scaleFlow,rescaleDegree,get_dilateInsertionPoints]
  ring

/-- The complete k<l source transforms by the same dilation; pair counting
and independent contraction signs remain exactly those of the fixed equation. -/
theorem oversubtractionSource_rescale (a : ℝ) (positive : 0 < a) (L : InsertedFlowFamily G)
    (input : List (PositionedInsertion G)) :
    oversubtractionSource (rescaleInsertedFlow a L) input =
      scaleFlow (a : ℂ) (rescaleDegree a (positionedInsertionDegreeSum input)
        (oversubtractionSource L (dilateInsertionPoints a input))) := by
  funext loop Λ UV legs q
  simp only [oversubtractionSource,scaleFlow,rescaleDegree]
  simp_rw [Finset.mul_sum]
  let e := dilateInsertionIndex a input
  apply Fintype.sum_equiv e
  intro k
  apply Fintype.sum_equiv e
  intro l
  have order : e k < e l ↔ k < l := Iff.rfl
  by_cases ordered : k < l
  · simp only [order,ordered,ite_true]
    rw [insertionPairSource_rescale a positive L input k l ordered]
    rfl
  · simp only [order,ordered,ite_false,mul_zero]

/-- The complete inhomogeneous oversubtraction equation, rather than just
its numerical regulator, has its correct actual input degree. -/
theorem oversubtractionFlowRHS_rescale (a : ℝ) (positive : 0 < a)
    (background : FlowFamily G) (L : InsertedFlowFamily G) (F : OversubtractedFamily G)
    (D : ℕ) (input : List (PositionedInsertion G)) (loop : ℕ) (Λ UV : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    oversubtractionFlowRHS (rescaleFlow a background) (rescaleInsertedFlow a L)
      (rescaleOversubtractions a F) D input loop Λ UV legs q =
      (a : ℂ)^((totalDimension legs : ℤ)-positionedInsertionDegreeSum input+1) *
        oversubtractionFlowRHS background L F D (dilateInsertionPoints a input)
          loop (a*Λ) (a*UV) legs (a • q) := by
  have nonzero : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt positive)
  unfold oversubtractionFlowRHS rescaleOversubtractions
  rw [insertionHomogeneousRHS_rescaleDegree a positive,oversubtractionSource_rescale a positive]
  simp only [scaleFlow,rescaleDegree,Complex.ofReal_zpow]
  rw [zpow_add_one₀ nonzero]
  ring

end YangMills.PerturbativeFlow
