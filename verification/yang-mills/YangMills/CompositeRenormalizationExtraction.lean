import YangMills.QuantumOutputRecovery
import YangMills.FormalRenormalization
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Actual bare-boundary extraction of composite RG coordinates

IZ pp.678–684 requires the counterterms of the inserted operator, not merely
coefficients combining renormalized normal products. V below therefore
projects the SAME lifted insertion at Lambda=UV, including the entire bare
single-insertion counterterm matrix. The source bare connection scales by
Z1/Z3 since g0 A0_can = (Z1/Z3) g A_can (IZ 12-125).

The Gram dual fixes a coordinate splitting, not a BRST cohomology theorem.
Physical authorization uses a full bare decomposition witness; the optional
Gram-compatible closure is a stronger presentation. It also needs
same-prescription finite Ward transport. No existence claim is made.
-/
noncomputable section
set_option maxHeartbeats 1200000
namespace YangMills.CompositeRG
open YangMills.Perturbative YangMills.PerturbativeFlow
variable {G : CompactSimpleGaugeGroup}

abbrev Row (G : CompactSimpleGaugeGroup) (D : ℕ) := ↥(monomialsBelow G D)

noncomputable instance rowFintype (G : CompactSimpleGaugeGroup) (D : ℕ) : Fintype (Row G D) :=
  Finset.fintypeCoeSort _

noncomputable instance rowDecidableEq (G : CompactSimpleGaugeGroup) (D : ℕ) : DecidableEq (Row G D) :=
  Classical.decEq _

/-- Classical normalized source-observable coefficients in all local rows. -/
def classicalMatrix {B : InvariantForm G} (e : ColorFrame B) {n : ℕ}
    (labels : Fin n → InvariantInsertionLabel G) (D : ℕ) : Matrix (Row G D) (Fin n) ℂ :=
  fun m i => normalizedObservableExpansion e (labels i : CurvatureJetPolynomial G) 1 m.val

def classicalGram {B : InvariantForm G} (e : ColorFrame B) {n : ℕ}
    (labels : Fin n → InvariantInsertionLabel G) (D : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  (classicalMatrix e labels D).conjTranspose * classicalMatrix e labels D

/-- Only admitted with nonzero Gram determinant; no singular inverse is
allowed to erase an output direction. -/
def classicalDual {B : InvariantForm G} (e : ColorFrame B) {n : ℕ}
    (labels : Fin n → InvariantInsertionLabel G) (D : ℕ) : Matrix (Fin n) (Row G D) ℂ :=
  (classicalGram e labels D)⁻¹ * (classicalMatrix e labels D).conjTranspose

theorem classicalDual_leftInverse {B : InvariantForm G} (e : ColorFrame B) {n : ℕ}
    (labels : Fin n → InvariantInsertionLabel G) (D : ℕ)
    (h : (classicalGram e labels D).det ≠ 0) :
    classicalDual e labels D * classicalMatrix e labels D = 1 := by
  rw [classicalDual, Matrix.mul_assoc]
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h)

/-- Bare source connection A0_source=(Z1/Z3) A_source. -/
def sourceFieldRatio (Z1 Z3 : FormalRG.Series) : FormalRG.Series := Z1 * Z3⁻¹

/-- Actual bare CLASSICAL source-polynomial columns. Each monomial's own
number of potential legs controls the bare-connection rescaling. -/
def bareClassicalMatrix {B : InvariantForm G} (e : ColorFrame B) {n : ℕ}
    (labels : Fin n → InvariantInsertionLabel G) (D : ℕ)
    (Z1 Z3 : FormalRG.Series) (order : ℕ) : Matrix (Row G D) (Fin n) ℂ :=
  fun m i => classicalMatrix e labels D m i *
    ((PowerSeries.coeff order ((sourceFieldRatio Z1 Z3) ^ m.val.legs.length) : ℝ) : ℂ)

/-- Correct V matrix: actual UV counterterms of the lifted local operator.
Using lift.coefficient alone would OMIT the L[O_m] bare counterterms. Source
powers g^(number of row legs) have been stripped using graph homogeneity;
each loop then contributes the even power g^(2l). -/
def liftedBareMatrix (L : ℝ → InsertedFlowFamily G) (lift : QuantumObservableLift G)
    {n : ℕ} (labels : Fin n → InvariantInsertionLabel G) (D : ℕ)
    (UV : ℝ) (order : ℕ) : Matrix (Row G D) (Fin n) ℂ :=
  fun m i => if order % 2 = 0 then
    extractCoefficient m.val
      (lift.finiteInsertion (L 1) 1 (labels i) 0 (order / 2) UV UV)
      (fun _ => 0)
  else 0

/-- Formal matrix Cauchy product, including rectangular matrices. -/
def seriesMatrixMul {a b c : ℕ}
    (A : ℕ → Matrix (Fin a) (Fin b) ℂ) (B : ℕ → Matrix (Fin b) (Fin c) ℂ)
    (order : ℕ) : Matrix (Fin a) (Fin c) ℂ :=
  ∑ k : Fin (order + 1), A k.val * B (order - k.val)

/-- Square, constant-identity bare classical coordinate change. -/
def projectedBareClassical {B : InvariantForm G} (e : ColorFrame B) {n : ℕ}
    (labels : Fin n → InvariantInsertionLabel G) (D : ℕ)
    (Z1 Z3 : FormalRG.Series) (order : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  classicalDual e labels D * bareClassicalMatrix e labels D Z1 Z3 order

def projectedBareInsertion {B : InvariantForm G} (e : ColorFrame B) {n : ℕ}
    (labels : Fin n → InvariantInsertionLabel G) (D : ℕ)
    (L : ℝ → InsertedFlowFamily G) (lift : QuantumObservableLift G)
    (UV : ℝ) (order : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  classicalDual e labels D * liftedBareMatrix L lift labels D UV order

/-- Columns are renormalized operators written in the bare invariant basis:
Vbare=Mbare Z modulo the explicitly tested exact/EOM residual. This is the
orientation giving Gamma=-Z^-1 (mu*d_mu+beta*d_g) Z. -/
def projectedCompositeZCoeff {B : InvariantForm G} (e : ColorFrame B) {n : ℕ}
    (labels : Fin n → InvariantInsertionLabel G) (D : ℕ)
    (L : ℝ → InsertedFlowFamily G) (lift : QuantumObservableLift G)
    (Z1 Z3 : FormalRG.Series) (UV : ℝ) (order : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  seriesMatrixMul
    (FormalRG.inverseMatrixCoeff (projectedBareClassical e labels D Z1 Z3))
    (projectedBareInsertion e labels D L lift UV) order

/-- Exact constant-term guards for BOTH inverse operations and tree data.
This is a fixed test on the actual matrices, never an independently chosen Z. -/
structure CompositeCoordinateGuards {B : InvariantForm G} (e : ColorFrame B) {n : ℕ}
    (labels : Fin n → InvariantInsertionLabel G) (D : ℕ)
    (L : ℝ → InsertedFlowFamily G) (lift : QuantumObservableLift G)
    (Z1 Z3 : FormalRG.Series) (UV : ℝ) : Prop where
  label_degree : ∀ i, intrinsicEngineeringDimension (labels i) < D
  gram_nonsingular : (classicalGram e labels D).det ≠ 0
  vertex_tree : PowerSeries.constantCoeff Z1 = 1
  wavefunction_tree : PowerSeries.constantCoeff Z3 = 1
  bare_classical_tree : bareClassicalMatrix e labels D Z1 Z3 0 = classicalMatrix e labels D
  insertion_tree : liftedBareMatrix L lift labels D UV 0 = classicalMatrix e labels D
  source_graph : ∀ g i loop legs q, 0 < UV →
    lift.finiteInsertion (L g) g (labels i) 0 loop UV UV legs q =
      (g : ℂ) ^ (legs.length + 2 * loop) *
        lift.finiteInsertion (L 1) 1 (labels i) 0 loop UV UV legs q

/-- Actual same-prescription quantum image of a finite local primitive,
inserted through the same bare L fields. BV antifields include EOM images. -/
def bareExactInsertion {B : InvariantForm G} (e : ColorFrame B)
    (L : InsertedFlowFamily G) (coeff : LocalAnomalyCoefficients G)
    (primitive : ℕ → LocalMonomial G →₀ ℂ) (D : ℕ) (loop : ℕ) (UV : ℝ) : OrderedAmplitude G :=
  fun legs q => ∑ a : Fin (loop + 1), (primitive a.val).sum fun input c =>
    c * ∑ b : Fin (loop - a.val + 1), ∑ output ∈ monomialsBelow G D,
      generatedQuantumWardCoefficient e 1 coeff b.val UV input output *
        L [⟨output, 0⟩] (loop - a.val - b.val) UV UV legs q

def bareExactMatrix {B : InvariantForm G} (e : ColorFrame B) {n : ℕ}
    (L : InsertedFlowFamily G) (coeff : LocalAnomalyCoefficients G)
    (primitive : Fin n → ℕ → LocalMonomial G →₀ ℂ) (D : ℕ)
    (UV : ℝ) (order : ℕ) : Matrix (Row G D) (Fin n) ℂ :=
  fun m i => if order % 2 = 0 then
    extractCoefficient m.val (bareExactInsertion e L coeff (primitive i) D (order / 2) UV)
      (fun _ => 0)
  else 0

/-- Strong finite closure/splitting condition, not a theorem about the raw
regulated flow. Gram projection alone cannot kill Q-exact/EOM components.
If only UV closure is proved, an explicit residual and its SCALE-DERIVATIVE
limit are required instead; bare coefficient convergence alone is insufficient.
Finite Ward restoration must authorize the generated finite Q used here. -/
def GramCompatibleFiniteClosure {B : InvariantForm G} (e : ColorFrame B) {n : ℕ}
    (labels : Fin n → InvariantInsertionLabel G) (D : ℕ)
    (L : ℝ → InsertedFlowFamily G) (lift : QuantumObservableLift G)
    (coeff : LocalAnomalyCoefficients G) (Z1 Z3 : FormalRG.Series) (UV : ℝ) : Prop :=
  ∃ primitive : Fin n → ℕ → LocalMonomial G →₀ ℂ,
    (∀ i loop m, primitive i loop m ≠ 0 →
      m.Admissible ∧ m.dimension + 1 < D ∧ m.ghostNumber = -1 ∧ m.parity = true) ∧
    ∀ order,
      liftedBareMatrix L lift labels D UV order =
        (∑ k : Fin (order + 1), bareClassicalMatrix e labels D Z1 Z3 k.val *
          projectedCompositeZCoeff e labels D L lift Z1 Z3 UV (order - k.val)) +
        bareExactMatrix e (L 1) coeff primitive D UV order

/-- Scale family of the SAME extracted matrices, suitable as the Z argument
of FormalRG.IsGammaLimit. The caller must authorize Z1/Z3 by the same action
and bind each scale's actual L/lift/anomaly normalization problem. -/
def projectedCompositeZFamily {B : InvariantForm G} (e : ColorFrame B) {n : ℕ}
    (labels : Fin n → InvariantInsertionLabel G) (D : ℕ)
    (L : ℝ → ℝ → InsertedFlowFamily G) (lift : ℝ → QuantumObservableLift G)
    (Z1 Z3 : ℝ → ℝ → FormalRG.Series) (UV mu : ℝ) (order : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  projectedCompositeZCoeff e labels D (L mu) (lift mu) (Z1 UV mu) (Z3 UV mu) UV order

/-- Gamma is the UV limit of this fixed composite extraction and the SAME
bare-action coupling formula. It is not a free normalization matrix. -/
def IsProjectedGammaLimit {B : InvariantForm G} (e : ColorFrame B) {n : ℕ}
    (labels : Fin n → InvariantInsertionLabel G) (D : ℕ)
    (L : ℝ → ℝ → InsertedFlowFamily G) (lift : ℝ → QuantumObservableLift G)
    (Z1 Z3 : ℝ → ℝ → FormalRG.Series) (mu : ℝ)
    (gamma : ℕ → Fin n → Fin n → ℂ) : Prop :=
  FormalRG.IsGammaLimit (projectedCompositeZFamily e labels D L lift Z1 Z3)
    (fun UV scale => FormalRG.bareCoupling (Z1 UV scale) (Z3 UV scale)) mu gamma


/-- Full bare mixing data. Its entries are constrained by the actual bare
operator equality below; no Gram orthogonality or cohomological injectivity
is demanded. Exact invariant directions may retain legitimate scheme freedom. -/
structure CompositeBareNormalization (G : CompactSimpleGaugeGroup) (n : ℕ) where
  Z : ℝ → ℝ → ℕ → Matrix (Fin n) (Fin n) ℂ
  primitive : ℝ → ℝ → Fin n → ℕ → LocalMonomial G →₀ ℂ

/-- Computed residual of the full bare decomposition. It is not extra
freely chosen error data. The primitive is inserted with the SAME generated
finite Ward coefficients and the SAME bare L counterterm matrix. -/
def CompositeBareNormalization.residual {B : InvariantForm G} (e : ColorFrame B) {n : ℕ}
    (labels : Fin n → InvariantInsertionLabel G) (D : ℕ)
    (L : ℝ → ℝ → InsertedFlowFamily G) (lift : ℝ → QuantumObservableLift G)
    (anomalyCoeff : ℝ → LocalAnomalyCoefficients G)
    (Z1 Z3 : ℝ → ℝ → FormalRG.Series) (norm : CompositeBareNormalization G n)
    (UV mu : ℝ) (order : ℕ) : Matrix (Row G D) (Fin n) ℂ :=
  liftedBareMatrix (L mu) (lift mu) labels D UV order -
    (∑ k : Fin (order + 1), bareClassicalMatrix e labels D (Z1 UV mu) (Z3 UV mu) k.val *
      norm.Z UV mu (order - k.val)) -
    bareExactMatrix e (L mu 1) (anomalyCoeff mu) (norm.primitive UV mu) D UV order

/-- Concrete normalization/graph/degree conditions common to exact and
asymptotic bare closure. Finite Ward restoration is still needed to authorize
the finite generated-Q image as the physical exact/EOM sector. -/
structure CompositeBareNormalization.Guards {B : InvariantForm G} (e : ColorFrame B) {n : ℕ}
    (labels : Fin n → InvariantInsertionLabel G) (D : ℕ)
    (L : ℝ → ℝ → InsertedFlowFamily G) (lift : ℝ → QuantumObservableLift G)
    (Z1 Z3 : ℝ → ℝ → FormalRG.Series) (norm : CompositeBareNormalization G n) : Prop where
  label_degree : ∀ i, intrinsicEngineeringDimension (labels i) < D
  tree : ∀ UV mu, 0 < mu → mu < UV → norm.Z UV mu 0 = 1
  vertex_tree : ∀ UV mu, 0 < mu → mu < UV → PowerSeries.constantCoeff (Z1 UV mu) = 1
  wavefunction_tree : ∀ UV mu, 0 < mu → mu < UV → PowerSeries.constantCoeff (Z3 UV mu) = 1
  primitive_degree : ∀ UV mu i loop m, 0 < mu → mu < UV →
    norm.primitive UV mu i loop m ≠ 0 →
    m.Admissible ∧ m.dimension + 1 < D ∧ m.ghostNumber = -1 ∧ m.parity = true
  source_graph : ∀ mu UV g i loop legs q, 0 < mu → mu < UV →
    (lift mu).finiteInsertion (L mu g) g (labels i) 0 loop UV UV legs q =
      (g : ℂ) ^ (legs.length + 2 * loop) *
        (lift mu).finiteInsertion (L mu 1) 1 (labels i) 0 loop UV UV legs q
  bare_degree : ∀ mu UV i loop m, 0 < mu → mu < UV →
    m.Admissible → D ≤ m.dimension →
    extractCoefficient m
      ((lift mu).finiteInsertion (L mu 1) 1 (labels i) 0 loop UV UV) (fun _ => 0) = 0
  scale_smooth : ∀ UV order i j mu, 0 < mu → mu < UV →
    DifferentiableAt ℝ (fun scale => norm.Z UV scale order i j) mu

/-- Exact full decomposition, which need not coincide with Gram projection.
This is a concrete sufficient normalization equation, not an existence claim
or a theorem that raw regulated amplitudes obey an unregulated Ward identity. -/
def CompositeBareNormalization.ExactClosure {B : InvariantForm G} (e : ColorFrame B) {n : ℕ}
    (labels : Fin n → InvariantInsertionLabel G) (D : ℕ)
    (L : ℝ → ℝ → InsertedFlowFamily G) (lift : ℝ → QuantumObservableLift G)
    (anomalyCoeff : ℝ → LocalAnomalyCoefficients G)
    (Z1 Z3 : ℝ → ℝ → FormalRG.Series) (norm : CompositeBareNormalization G n) : Prop :=
  norm.Guards e labels D L lift Z1 Z3 ∧ ∀ UV mu order, 0 < mu → mu < UV →
    norm.residual e labels D L lift anomalyCoeff Z1 Z3 UV mu order = 0

/-- Controlled cutoff remainder alternative. Its scale derivative is tested
separately: a small residual alone does not justify the gamma scale identity.
All coefficients and derivatives refer to the computed residual above. -/
def CompositeBareNormalization.AsymptoticClosure {B : InvariantForm G} (e : ColorFrame B) {n : ℕ}
    (labels : Fin n → InvariantInsertionLabel G) (D : ℕ)
    (L : ℝ → ℝ → InsertedFlowFamily G) (lift : ℝ → QuantumObservableLift G)
    (anomalyCoeff : ℝ → LocalAnomalyCoefficients G)
    (Z1 Z3 : ℝ → ℝ → FormalRG.Series) (norm : CompositeBareNormalization G n) : Prop :=
  norm.Guards e labels D L lift Z1 Z3 ∧
  (∀ UV order m i mu, 0 < mu → mu < UV →
    DifferentiableAt ℝ (fun scale =>
      norm.residual e labels D L lift anomalyCoeff Z1 Z3 UV scale order m i) mu) ∧
  ∀ mu order m i, 0 < mu →
    Filter.Tendsto (fun UV =>
      norm.residual e labels D L lift anomalyCoeff Z1 Z3 UV mu order m i)
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun UV => (mu : ℂ) * deriv (fun scale =>
      norm.residual e labels D L lift anomalyCoeff Z1 Z3 UV scale order m i) mu)
      Filter.atTop (nhds 0)

/-- Gamma binding for the full same-bare-decomposition matrix. This avoids
requiring a potentially false Gram orthogonal splitting of exact directions.
Action Ward transport and the corresponding scale-insertion theorem must
still authorize this finite normalization before physical RG admission. -/
def IsFullBareGammaLimit {n : ℕ} (norm : CompositeBareNormalization G n)
    (Z1 Z3 : ℝ → ℝ → FormalRG.Series) (mu : ℝ)
    (gamma : ℕ → Fin n → Fin n → ℂ) : Prop :=
  FormalRG.IsGammaLimit norm.Z
    (fun UV scale => FormalRG.bareCoupling (Z1 UV scale) (Z3 UV scale)) mu gamma


/-- Bind the exact/EOM operator in the decomposition to the actual anomaly
boundary problem of these L insertions. Z1/Z3 must additionally be authorized
by the actual Ward-restored action; that distinct source theorem is not
replaced by this local composite normalization relation. -/
def SameTheoryCompositeNormalization {B : InvariantForm G} (e : ColorFrame B) {n : ℕ}
    (labels : Fin n → InvariantInsertionLabel G) (D : ℕ)
    (L : ℝ → ℝ → InsertedFlowFamily G) (lift : ℝ → QuantumObservableLift G)
    (transport : (mu : ℝ) → SameTheoryWardTransportData e (L mu))
    (Q : ℝ → QuantumWardLimit G) (Z1 Z3 : ℝ → ℝ → FormalRG.Series)
    (norm : CompositeBareNormalization G n) : Prop :=
  (∀ mu, 0 < mu → (lift mu).Compatible e (transport mu).coefficient (Q mu) ∧
    (Q mu).Nilpotent) ∧
  (norm.ExactClosure e labels D L lift (fun mu => (transport mu).coefficient 1) Z1 Z3 ∨
    norm.AsymptoticClosure e labels D L lift (fun mu => (transport mu).coefficient 1) Z1 Z3)

end YangMills.CompositeRG
