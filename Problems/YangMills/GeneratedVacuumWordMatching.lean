import Problems.YangMills.VacuumWordContinuation
import Problems.YangMills.LocalWardFlowFamily
import Problems.YangMills.MultiRenormalizationGroup

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Generated physical words as UV germs of the same physical C-fields

Jaffe--Witten section4 p6 separately requires short-distance CORRELATION
agreement, in addition to the OPE coefficient clause. The series below is
fixed by the same local Ward/flow family, corrected dictionary and invariant
spectators, with no elementary gauge/ghost legs. Setting hbar=1 is finite at
each g order by that family's graph-order guard. The ACTUAL C vacuum-word
observations obey an all-order asymptotic remainder at shrinking distances.
The homogeneous RG/vacuum-subtracted reference lift is an auxiliary scheme
presentation: its source-equivalence must be justified, not assumed for
arbitrary raw mu-subtracted operators with lower-dimensional identity mixing.
Flat nonperturbative corrections are allowed; no summation/convergence of
the perturbative series and no nonperturbative ghost Hilbert space is imposed.
-/
noncomputable section
open Filter MeasureTheory
namespace YangMills.PhysicalWords
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

/-- Drop the unique zero-dimensional empty momentum tuple. This is a genuine
linear coordinate equivalence, not an independently chosen physical test. -/
def wordJointCoordinates (arity : ℕ) :
    JointVariableSpace arity 0 ≃ₗ[ℝ] (Fin arity → Spacetime) where
  toFun xq := xq.1
  invFun x := (x, fun i : Fin 0 => Fin.elim0 i)
  left_inv := by
    intro xq
    apply Prod.ext
    · rfl
    · funext i; exact Fin.elim0 i
  right_inv := by intro x; rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

def invariantWordTest (arity : ℕ) : WordTest arity →L[ℂ]
    JointMomentumTest arity ([] : List (ExternalLeg G)) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (wordJointCoordinates arity).toContinuousLinearEquiv

/-- The exact finite loop assembly of the same corrected physical word.
The required vanishing above order/2 is family.physical_word_graph. -/
def generatedInvariantWord {form : InvariantForm G} {e : ColorFrame form}
    {S : FixedFlowSystem e} (family : LocalWardFlowFamily S) (mu : RenormalizationScale)
    (order arity : ℕ) (labels : Fin arity → InvariantInsertionLabel G) : WordDistribution arity :=
  (∑ loop ∈ Finset.range (order / 2 + 1),
    physicalInvariantWord (family.continuum mu) (family.lift mu) labels order loop).comp
      (invariantWordTest (G := G) arity).toLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Q : WightmanData H} {C : RenormalizedCompositeMap Q G}

/-- With Q_E(v)=Q_M(Wv), the high-scale incoming label is R_t^-1 Wv.
There is NO outgoing transport factor in a vacuum word. Canonical scaling
uses the actual intrinsic dimensions, and all insertions belong to C. -/
def strippedVacuumWord {m : ℕ}
    {labels : Fin m → CurvatureJetPolynomial.invariantAlgebra G}
    {betaSeries : ℕ → ℝ} {gammaSeries : ℕ → Fin m → Fin m → ℂ}
    {K : OPE.MultiKernels C} (V : VacuumWordContinuation K)
    (F : RG.Frame labels betaSeries gammaSeries) (rotation : Wick.LabelRotation labels)
    (mu : RenormalizationScale) (scale : ℝ) (n : ℕ) (inputs : Fin (n + 1) → Fin m)
    (test : WordTest (n + 1)) : ℂ :=
  ∑ indices : Fin (n + 1) → Fin m,
    (∏ r : Fin (n + 1),
      ((F.transport (RG.time scale)).symm (rotation.map (Pi.single (inputs r) 1))) (indices r)) *
      ((scale ^ (∑ r : Fin (n + 1), intrinsicEngineeringDimension (labels (indices r))) : ℝ) : ℂ) *
        V.scaledEuclideanObservation n mu (fun r => labels (indices r)) scale test

/-- Every finite-order weak UV remainder of actual physical vacuum words.
The last retained running-coupling power is included, permitting flat terms.
Only arities at least two and compact, separated, strictly Euclidean-ordered
observations occur. One-point condensates are not independently prescribed.
This condition is independent of the OPE coefficient matching obligation. -/
def AllOrderVacuumWordMatch {m : ℕ}
    {labels : Fin m → CurvatureJetPolynomial.invariantAlgebra G}
    {betaSeries : ℕ → ℝ} {gammaSeries : ℕ → Fin m → Fin m → ℂ}
    {K : OPE.MultiKernels C} (V : VacuumWordContinuation K)
    (F : RG.Frame labels betaSeries gammaSeries) (rotation : Wick.LabelRotation labels)
    (mu : RenormalizationScale)
    (series : ℕ → (n : ℕ) → (Fin (n + 1) → Fin m) → WordDistribution (n + 1)) : Prop :=
  ∀ n, 0 < n → ∀ inputs (test : WordTest (n + 1)), OrderedEuclideanTest test →
    ∀ N : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∀ scale : ℝ, 0 < scale → scale < delta →
      ‖strippedVacuumWord V F rotation mu scale n inputs test -
        ∑ k ∈ Finset.range (N + 1),
          ((F.running.coupling (RG.time scale) : ℂ) ^ k) * series k n inputs test‖ ≤
        epsilon * F.running.coupling (RG.time scale) ^ N

/-- Equality only in the physical UV germ: every running-coupling power
annihilates the difference asymptotically. This permits nonzero flat
nonperturbative corrections and is not equality of Hilbert-space vectors. -/
def UVWordEquivalent {m : ℕ}
    {labels : Fin m → CurvatureJetPolynomial.invariantAlgebra G}
    {betaSeries : ℕ → ℝ} {gammaSeries : ℕ → Fin m → Fin m → ℂ}
    {K : OPE.MultiKernels C} (V : VacuumWordContinuation K)
    (F : RG.Frame labels betaSeries gammaSeries) (rotation : Wick.LabelRotation labels)
    (mu : RenormalizationScale) (n : ℕ) (left right : Fin (n + 1) → Fin m) : Prop :=
  ∀ test : WordTest (n + 1), OrderedEuclideanTest test →
    ∀ N : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∀ scale : ℝ, 0 < scale → scale < delta →
      ‖strippedVacuumWord V F rotation mu scale n left test -
        strippedVacuumWord V F rotation mu scale n right test‖ ≤
        epsilon * F.running.coupling (RG.time scale) ^ N

/-- The formal physical quotient is realized by UV germs of these ACTUAL
C-word observations: equal prescribed word series give a flat difference.
No exact nonperturbative BRST state quotient is inferred from formal data. -/
theorem AllOrderVacuumWordMatch.flat_of_series_eq {m : ℕ}
    {labels : Fin m → CurvatureJetPolynomial.invariantAlgebra G}
    {betaSeries : ℕ → ℝ} {gammaSeries : ℕ → Fin m → Fin m → ℂ}
    {K : OPE.MultiKernels C} {V : VacuumWordContinuation K}
    {F : RG.Frame labels betaSeries gammaSeries} {rotation : Wick.LabelRotation labels}
    {mu : RenormalizationScale}
    {series : ℕ → (n : ℕ) → (Fin (n + 1) → Fin m) → WordDistribution (n + 1)}
    (matching : AllOrderVacuumWordMatch V F rotation mu series)
    (n : ℕ) (arity_positive : 0 < n) (left right : Fin (n + 1) → Fin m)
    (same : ∀ order (test : WordTest (n + 1)), OrderedEuclideanTest test →
      series order n left test = series order n right test) :
    UVWordEquivalent V F rotation mu n left right := by
  intro test ordered N epsilon positive
  have half : 0 < epsilon / 2 := by positivity
  obtain ⟨dl, hdl, hdl_one, left_bound⟩ := matching n arity_positive left test ordered N (epsilon / 2) half
  obtain ⟨dr, hdr, hdr_one, right_bound⟩ := matching n arity_positive right test ordered N (epsilon / 2) half
  refine ⟨min dl dr, lt_min hdl hdr, (min_le_left _ _).trans hdl_one, ?_⟩
  intro scale scale_positive small
  have hl := left_bound scale scale_positive (small.trans_le (min_le_left _ _))
  have hr := right_bound scale scale_positive (small.trans_le (min_le_right _ _))
  have same_partial :
      (∑ k ∈ Finset.range (N + 1), ((F.running.coupling (RG.time scale) : ℂ) ^ k) *
        series k n left test) =
      ∑ k ∈ Finset.range (N + 1), ((F.running.coupling (RG.time scale) : ℂ) ^ k) *
        series k n right test := by
    apply Finset.sum_congr rfl
    intro k _hk
    rw [same k test ordered]
  rw [← same_partial] at hr
  calc
    _ = ‖(strippedVacuumWord V F rotation mu scale n left test -
          ∑ k ∈ Finset.range (N + 1), ((F.running.coupling (RG.time scale) : ℂ) ^ k) *
            series k n left test) -
        (strippedVacuumWord V F rotation mu scale n right test -
          ∑ k ∈ Finset.range (N + 1), ((F.running.coupling (RG.time scale) : ℂ) ^ k) *
            series k n left test)‖ := by congr 1; ring
    _ ≤ _ := norm_sub_le _ _
    _ ≤ (epsilon / 2) * F.running.coupling (RG.time scale) ^ N +
          (epsilon / 2) * F.running.coupling (RG.time scale) ^ N := add_le_add hl hr
    _ = _ := by ring

/-- SAME common exhaustive frame as the physical OPE and stress sector.
The series argument is fixed here, so a proof author cannot select different
word predictions. C.Compatible retains same-domain Hermiticity/unit/relations
and C-word cyclicity on the actual physical Hilbert space. -/
def GeneratedVacuumWordBridge
    {form : InvariantForm G} {e : ColorFrame form} {S : FixedFlowSystem e}
    (family : LocalWardFlowFamily S) (basis : OPE.FilteredBasis G)
    (K : OPE.MultiKernels C) (V : VacuumWordContinuation K)
    {betaSeries : ℕ → ℝ} {gammaSeries : ℕ → basis.Index → basis.Index → ℂ}
    {coeff : OPE.MultiCoefficients basis} {physical : ℕ → OPE.MultiCoefficients basis}
    (X : RG.ExhaustiveMatching basis C S.referenceScale betaSeries gammaSeries
      (RG.pairFromMulti coeff) (fun k => RG.pairFromMulti (physical k)))
    (rotation : (D : ℕ) → Wick.LabelRotation (fun i => basis.label (X.index D i))) : Prop :=
  C.Compatible ∧ ∀ D,
    AllOrderVacuumWordMatch V (X.frame D) (rotation D) S.referenceScale
      (fun order n inputs => generatedInvariantWord family S.referenceScale order (n + 1)
        (fun r => basis.label (X.index D (inputs r))))

end YangMills.PhysicalWords
