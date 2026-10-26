import Problems.YangMills.GradedAmplitude

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Fixed graded momentum-space flow

This is the coefficient form of the Polchinski flow, with the convention
Δ=(1/2) Σ C_MN d_N d_M for left derivatives. Therefore Δ(φ_A φ_B)=C_AB
also for odd fields. The bilinear term is ordered (d_N L)(d_M F).
External odd permutation signs are the explicit Koszul unshuffle.

`linearFlowRHS` and `quadraticFlowRHS` do not include a factor 1/2.
The background equation is (linear-quadratic)/2; the homogeneous
single-insertion equation is linear/2-quadratic(L,F).
-/
noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative MeasureTheory
open scoped ContDiff

variable {G : CompactSimpleGaugeGroup}

/-- The exact Λ derivative of the fixed covariance matrix. -/
def basicDerivativeCovariance (scale : ℝ) (K L : BasicField G) (p : Spacetime) : ℝ :=
  match K, L with
  | .gauge μ a, .gauge ν b => if a = b ∧ μ = ν then flowDerivativeKernel scale p else 0
  | .antighost a, .ghost b => if a = b then -flowDerivativeKernel scale p else 0
  | .ghost a, .antighost b => if a = b then flowDerivativeKernel scale p else 0
  | .auxiliary a, .auxiliary b =>
      if a = b then euclideanSquare p * flowDerivativeKernel scale p else 0
  | _, _ => 0

def linearFlowIntegrand (F : FlowFamily G) (loop : ℕ) (Λ Λ0 : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) (p : Spacetime) : ℂ :=
  if loop = 0 then 0 else
    (∑ M : BasicField G, ∑ N : BasicField G,
      (basicDerivativeCovariance Λ M N (-p) : ℂ) *
        F (loop - 1) Λ Λ0 (.inl M :: .inl N :: legs)
          (prependMomenta (.inl M) p (prependMomenta (.inl N) (-p) q))) /
      (2 * Real.pi : ℂ) ^ 4

/-- Integral of the combined one-loop contraction. A flow prescription
below must establish its actual integrability. -/
def linearFlowRHS (F : FlowFamily G) (loop : ℕ) (Λ Λ0 : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) : ℂ :=
  ∫ p : Spacetime, linearFlowIntegrand F loop Λ Λ0 legs q p

/-- One ordered external partition and loop split in (d_N L)(d_M F).
L is the momentum-conserving background, fixing its internal momentum.
F may have local insertions and need not conserve external momentum. -/
def quadraticSplit (L F : FlowFamily G) (loop leftLoop : ℕ) (Λ Λ0 : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime)
    (s : Finset (Fin legs.length)) : ℂ :=
  let t := complementIndices legs s
  let k := selectedMomentum legs s q
  splitSign legs s * ∑ M : BasicField G, ∑ N : BasicField G,
    (basicDerivativeCovariance Λ M N k : ℂ) *
      L leftLoop Λ Λ0 (.inl N :: selectedLegs legs s)
        (prependMomenta (.inl N) (-k) (selectedMomenta legs s q)) *
      F (loop - leftLoop) Λ Λ0 (.inl M :: selectedLegs legs t)
        (prependMomenta (.inl M) k (selectedMomenta legs t q))

def quadraticFlowRHS (L F : FlowFamily G) (loop : ℕ) (Λ Λ0 : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) : ℂ :=
  ∑ l : Fin (loop + 1), ∑ s ∈ (Finset.univ : Finset (Fin legs.length)).powerset,
    quadraticSplit L F loop l.val Λ Λ0 legs q s

def backgroundFlowRHS (L : FlowFamily G) (loop : ℕ) (Λ Λ0 : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) : ℂ :=
  (1 / 2 : ℂ) * (linearFlowRHS L loop Λ Λ0 legs q -
    quadraticFlowRHS L L loop Λ Λ0 legs q)

def insertionHomogeneousRHS (L F : FlowFamily G) (loop : ℕ) (Λ Λ0 : ℝ)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) : ℂ :=
  (1 / 2 : ℂ) * linearFlowRHS F loop Λ Λ0 legs q -
    quadraticFlowRHS L F loop Λ Λ0 legs q

/-- The extra intrinsic-parity sign in Δ(AB)-Δ(A)B-AΔ(B).
It is absent for the even background L and present for odd insertions. -/
def intrinsicContractionSign (leftParity : Bool) (M : BasicField G) : ℂ :=
  if leftParity && M.fermionic then -1 else 1

/-- Independent insertion functionals do not carry momentum-conservation
deltas. Their connecting momentum must be integrated, rather than fixed
to the sum of external momenta on one side. All terms are combined first. -/
def independentContractionIntegrand (leftParity : Bool) (A B : FlowFamily G)
    (loop : ℕ) (Λ Λ0 : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (p : Spacetime) : ℂ :=
  (∑ l : Fin (loop + 1), ∑ s ∈ (Finset.univ : Finset (Fin legs.length)).powerset,
    splitSign legs s * ∑ M : BasicField G, ∑ N : BasicField G,
      intrinsicContractionSign leftParity M * (basicDerivativeCovariance Λ M N p : ℂ) *
        A l.val Λ Λ0 (.inl N :: selectedLegs legs s)
          (prependMomenta (.inl N) (-p) (selectedMomenta legs s q)) *
        B (loop - l.val) Λ Λ0 (.inl M :: selectedLegs legs (complementIndices legs s))
          (prependMomenta (.inl M) p (selectedMomenta legs (complementIndices legs s) q))) /
    (2 * Real.pi : ℂ) ^ 4

def independentContractionRHS (leftParity : Bool) (A B : FlowFamily G)
    (loop : ℕ) (Λ Λ0 : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) : ℂ :=
  ∫ p : Spacetime, independentContractionIntegrand leftParity A B loop Λ Λ0 legs q p

abbrev ScaleCouplingFamily (G : CompactSimpleGaugeGroup) := ℝ → ℝ → FlowFamily G

/-- Ordered genuine Frechet partial derivatives in external momenta. -/
def momentumJet {legs : List (ExternalLeg G)}
    (directions : List (Fin legs.length × Fin 4))
    (F : (Fin legs.length → Spacetime) → ℂ) (q : Fin legs.length → Spacetime) : ℂ :=
  iteratedFDeriv ℝ directions.length F q (fun i =>
    Pi.single (directions.get i).1 (Pi.single (directions.get i).2 1))

def marginalJet (L : FlowFamily G) (loop : ℕ) (μ Λ0 : ℝ)
    (legs : List (ExternalLeg G)) (directions : List (Fin legs.length × Fin 4)) : ℂ :=
  momentumJet directions (L loop μ Λ0 legs) 0

def uvLocalJet (L : FlowFamily G) (loop : ℕ) (Λ0 : ℝ)
    (legs : List (ExternalLeg G)) (directions : List (Fin legs.length × Fin 4)) : ℂ :=
  momentumJet directions (L loop Λ0 Λ0 legs) 0

structure LocalVertexLeg (G : CompactSimpleGaugeGroup) where
  field : ExternalLeg G
  derivatives : List (Fin 4)

structure LocalVertex (G : CompactSimpleGaugeGroup) where
  coefficient : ℂ
  couplingOrder : ℕ
  legs : List (LocalVertexLeg G)

def LocalVertex.degree (v : LocalVertex G) : ℕ :=
  (v.legs.map (fun k => k.field.dimension + k.derivatives.length)).sum

def LocalVertex.ghostNumber (v : LocalVertex G) : ℤ :=
  (v.legs.map (fun k => k.field.ghostNumber)).sum

def LocalVertex.parity (v : LocalVertex G) : Bool :=
  decide ((v.legs.filter (fun k => k.field.parity)).length % 2 = 1)

/-- Ordered left coefficient extraction on a local graded jet monomial.
Even multiplicities give their actual factorial factors; odd derivatives
carry the fixed sign from passing the preceding odd generators. The source
Fourier convention is φ(x)=∫exp(-ipx)φ(p), hence each jet contributes -ip;
the +i momentum extraction in source equation (4.1) then recovers its label. -/
def localMonomialDerivative : List (LocalVertexLeg G) → List (ExternalLeg G × Spacetime) → ℂ
  | [], [] => 1
  | _ :: _, [] => 0
  | source, (K, p) :: rest => ∑ j : Fin source.length,
      if (source.get j).field = K then
        ((-1 : ℂ) ^ (if K.parity then
          ((source.take j.val).filter (fun k => k.field.parity)).length else 0)) *
        (((source.get j).derivatives.map (fun μ => -Complex.I * (p μ : ℂ))).prod) *
        localMonomialDerivative (source.take j.val ++ source.drop (j.val + 1)) rest
      else 0
termination_by _ external => external.length

def localVertexAmplitude (v : LocalVertex G) (g : ℝ) : OrderedAmplitude G :=
  fun legs q => v.coefficient * (g : ℂ) ^ v.couplingOrder *
    localMonomialDerivative v.legs (List.ofFn (fun i => (legs.get i, q i)))

def localPolynomialAmplitude (terms : List (LocalVertex G)) (g : ℝ) : OrderedAmplitude G :=
  fun legs q => (terms.map (fun v => localVertexAmplitude v g legs q)).sum

def physicalActionVertices {B : InvariantForm G} (e : ColorFrame B) : List (LocalVertex G) :=
  (actionMonomials e).map (fun m =>
    { coefficient := (m.coefficient : ℂ), couplingOrder := m.couplingOrder,
      legs := m.legs.map (fun k => ⟨.inl k.field, k.derivatives⟩) })

/-- The nonlinear parts of -Σ(sφ)φ‡, with source-compatible real ghost
convention sA=Dc, sc=-g[c,c]/2, s(cbar)=div A+iB, sB=i div Dc.
The last vertex is integrated by parts onto B‡. All bilinear free-BRST
terms belong to S0 and are removed from the amputated interaction. -/
def antifieldActionVertices {B : InvariantForm G} (e : ColorFrame B) : List (LocalVertex G) := do
  let a ← List.finRange G.dimension
  let b ← List.finRange G.dimension
  let c ← List.finRange G.dimension
  let f : ℂ := (structureConstant e a b c : ℝ)
  ({ coefficient := (1 / 2 : ℂ) * f, couplingOrder := 1,
      legs := [⟨.inl (.ghost b), []⟩, ⟨.inl (.ghost c), []⟩,
        ⟨.inr (.ghost a), []⟩] } ::
    (List.finRange 4).flatMap (fun μ =>
      [ { coefficient := -f, couplingOrder := 1,
          legs := [⟨.inl (.gauge μ b), []⟩, ⟨.inl (.ghost c), []⟩,
            ⟨.inr (.gauge μ a), []⟩] },
        { coefficient := Complex.I * f, couplingOrder := 1,
          legs := [⟨.inl (.gauge μ b), []⟩, ⟨.inl (.ghost c), []⟩,
            ⟨.inr (.auxiliary a), [μ]⟩] } ]))

def treeActionVertices {B : InvariantForm G} (e : ColorFrame B) : List (LocalVertex G) :=
  physicalActionVertices e ++ antifieldActionVertices e

def treeVertexAmplitude {B : InvariantForm G} (e : ColorFrame B) (g : ℝ) : OrderedAmplitude G :=
  localPolynomialAmplitude (treeActionVertices e) g

/-- Fixed Feynman-gauge quadratic action S0, including the free antifield
couplings removed from the connected amputated interaction. The gauge
kinetic density is written modulo a total divergence as Σ(∂A)^2/2.
All coefficients use the same ghost/B phases as the nonlinear BV vertices. -/
def freeActionVertices (G : CompactSimpleGaugeGroup) : List (LocalVertex G) :=
  ((List.finRange G.dimension).flatMap (fun a =>
    [ { coefficient := (1 / 2 : ℂ), couplingOrder := 0,
        legs := [⟨.inl (.auxiliary a), []⟩, ⟨.inl (.auxiliary a), []⟩] },
      { coefficient := -Complex.I, couplingOrder := 0,
        legs := [⟨.inl (.auxiliary a), []⟩, ⟨.inr (.antighost a), []⟩] } ] ++
      (List.finRange 4).flatMap (fun μ =>
        [ { coefficient := 1, couplingOrder := 0,
            legs := [⟨.inl (.antighost a), [μ]⟩, ⟨.inl (.ghost a), [μ]⟩] },
          { coefficient := -1, couplingOrder := 0,
            legs := [⟨.inl (.ghost a), [μ]⟩, ⟨.inr (.gauge μ a), []⟩] },
          { coefficient := -1, couplingOrder := 0,
            legs := [⟨.inl (.gauge μ a), [μ]⟩, ⟨.inr (.antighost a), []⟩] },
          { coefficient := -Complex.I, couplingOrder := 0,
            legs := [⟨.inl (.ghost a), [μ, μ]⟩, ⟨.inr (.auxiliary a), []⟩] } ] ++
        (List.finRange 4).map (fun ν =>
          { coefficient := (1 / 2 : ℂ), couplingOrder := 0,
            legs := [⟨.inl (.gauge ν a), [μ]⟩, ⟨.inl (.gauge ν a), [μ]⟩] }))))

def freeVertexAmplitude (G : CompactSimpleGaugeGroup) : OrderedAmplitude G :=
  localPolynomialAmplitude (freeActionVertices G) 0

/-- Finite marginal coefficients specify a local normalization scheme.
They are not arbitrary momentum-dependent amplitude data. The classical
boundary is always the fixed action above. Restored continuum Ward identities
must additionally constrain these finite choices; finite cutoff terms need
not themselves be BRST invariant. -/
structure LocalMarginalData (G : CompactSimpleGaugeGroup) where
  terms : ℕ → List (LocalVertex G)
  marginal : ∀ loop v, v ∈ terms loop → v.degree = 4
  ghost_zero : ∀ loop v, v ∈ terms loop → v.ghostNumber = 0
  even : ∀ loop v, v ∈ terms loop → v.parity = false
  perturbative_order : ∀ loop v, v ∈ terms loop →
    v.couplingOrder + 2 = v.legs.length + 2 * loop

def marginalNormalization {B : InvariantForm G} (e : ColorFrame B)
    (scheme : LocalMarginalData G) (loop : ℕ) (g : ℝ) : OrderedAmplitude G :=
  if loop = 0 then treeVertexAmplitude e g else localPolynomialAmplitude (scheme.terms loop) g

/-- Full Euclidean O(4), including reflections, defined by the actual
Euclidean quadratic form rather than the unrelated sup norm on coordinate tuples. -/
structure EuclideanRotation where
  linear : Spacetime ≃ₗ[ℝ] Spacetime
  orthogonal : ∀ p, euclideanSquare (linear p) = euclideanSquare p

def covectorEntry (T : EuclideanRotation) (μ ν : Fin 4) : ℝ :=
  T.linear.symm (Pi.single μ 1) ν

def vectorEntry (T : EuclideanRotation) (μ ν : Fin 4) : ℝ :=
  T.linear (Pi.single ν 1) μ

def covectorAction (T : EuclideanRotation) (p : Spacetime) : Spacetime :=
  fun μ => ∑ ν : Fin 4, covectorEntry T μ ν * p ν

/-- External BV variables transform dually: gauge potentials are covectors,
their antifields are dual vector densities. Scalar antifields are scalar
densities; |det T|=1 for these O(4) transformations. -/
def rotationEntry (T : EuclideanRotation) : ExternalLeg G → ExternalLeg G → ℂ
  | .inl (.gauge μ a), .inl (.gauge ν b) => if a = b then covectorEntry T μ ν else 0
  | .inr (.gauge μ a), .inr (.gauge ν b) => if a = b then vectorEntry T μ ν else 0
  | .inl (.gauge _ _), _ => 0
  | .inr (.gauge _ _), _ => 0
  | K, L => if K = L then 1 else 0

/-- Exact adjoint/dual-adjoint entries of the actual chosen gauge group. -/
def colorEntry {B : InvariantForm G} (e : ColorFrame B) (u : G.Carrier) :
    ExternalLeg G → ExternalLeg G → ℂ
  | .inl (.gauge μ a), .inl (.gauge ν b) =>
      if μ = ν then e.basis.repr (G.adjoint u (e.basis b)) a else 0
  | .inl (.ghost a), .inl (.ghost b) => e.basis.repr (G.adjoint u (e.basis b)) a
  | .inl (.antighost a), .inl (.antighost b) => e.basis.repr (G.adjoint u (e.basis b)) a
  | .inl (.auxiliary a), .inl (.auxiliary b) => e.basis.repr (G.adjoint u (e.basis b)) a
  | .inr (.gauge μ a), .inr (.gauge ν b) =>
      if μ = ν then e.basis.repr (G.adjoint u⁻¹ (e.basis a)) b else 0
  | .inr (.ghost a), .inr (.ghost b) => e.basis.repr (G.adjoint u⁻¹ (e.basis a)) b
  | .inr (.antighost a), .inr (.antighost b) => e.basis.repr (G.adjoint u⁻¹ (e.basis a)) b
  | .inr (.auxiliary a), .inr (.auxiliary b) => e.basis.repr (G.adjoint u⁻¹ (e.basis a)) b
  | _, _ => 0

def ofFnMomenta {n : ℕ} (labels : Fin n → ExternalLeg G) (q : Fin n → Spacetime) :
    Fin (List.ofFn labels).length → Spacetime :=
  fun i => q ⟨i.val, by simpa using i.isLt⟩

/-- Pull back a coefficient tensor by a fixed field-variable change.
Ordered left derivatives retain the exterior (ghost) coefficients; no
evaluation on commuting ghost numbers is substituted for graded equality. -/
def transformedLocalAmplitude (terms : List (LocalVertex G)) (g : ℝ)
    (entries : ExternalLeg G → ExternalLeg G → ℂ) (momentumAction : Spacetime → Spacetime)
    (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) : ℂ :=
  ∑ labels : Fin legs.length → ExternalLeg G,
    (∏ i : Fin legs.length, entries (labels i) (legs.get i)) *
      localPolynomialAmplitude terms g (List.ofFn labels)
        (ofFnMomenta labels (fun i => momentumAction (q i)))

def LocalColorInvariant {B : InvariantForm G} (e : ColorFrame B)
    (terms : List (LocalVertex G)) : Prop :=
  ∀ u g legs q, transformedLocalAmplitude terms g (colorEntry e u) id legs q =
    localPolynomialAmplitude terms g legs q

def LocalEuclideanInvariant (terms : List (LocalVertex G)) : Prop :=
  ∀ T g legs q, transformedLocalAmplitude terms g (rotationEntry T) (covectorAction T) legs q =
    localPolynomialAmplitude terms g legs q

structure LocalMarginalSymmetries {B : InvariantForm G} (e : ColorFrame B)
    (scheme : LocalMarginalData G) : Prop where
  color : ∀ loop, LocalColorInvariant e (scheme.terms loop)
  euclidean : ∀ loop, LocalEuclideanInvariant (scheme.terms loop)

/-- Last external momentum is the dependent momentum in reduced background
amplitudes. Inserted amplitudes instead use all their momenta independently. -/
def conservingMomenta (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    Fin legs.length → Spacetime :=
  fun i => if i.val + 1 = legs.length then
    -(∑ j ∈ (Finset.univ : Finset (Fin legs.length)).filter
      (fun j => j.val + 1 < legs.length), q j) else q i

def ReducedDirections (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4)) : Prop :=
  ∀ d ∈ directions, d.1.val + 1 < legs.length

def BalancedMomenta (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) : Prop :=
  (∑ i : Fin legs.length, q i) = 0

/-- Concrete fixed flow and local coefficient-boundary equations. This
defines admissibility of a proposed family; no arbitrary amplitude predicate
or arbitrary momentum-dependent "counterterm" is accepted.

Unbroken local E(4)/actual-G invariance is enforced through ordered graded
coefficients above. Restored quantum Ward identities, ultraviolet limits and
the equivalence to the coefficientwise bare construction still remain
required before this defines the full renormalized Yang--Mills prescription.
-/
structure CoefficientFlowConditions {B : InvariantForm G} (e : ColorFrame B)
    (scheme : LocalMarginalData G) (A : ScaleCouplingFamily G) : Prop where
  local_symmetries : LocalMarginalSymmetries e scheme
  momentum_smooth : ∀ μ g loop Λ Λ0 legs,
    0 < μ → μ ≤ Λ0 → 0 < Λ → Λ ≤ Λ0 →
      ContDiff ℝ ∞ (A μ g loop Λ Λ0 legs)
  coupling_smooth : ∀ μ loop Λ Λ0 legs q,
    0 < μ → μ ≤ Λ0 → 0 < Λ → Λ ≤ Λ0 →
      ContDiff ℝ ∞ (fun g : ℝ => A μ g loop Λ Λ0 legs q)
  joint_coupling_momentum_smooth : ∀ μ loop Λ Λ0 legs,
    0 < μ → μ ≤ Λ0 → 0 < Λ → Λ ≤ Λ0 →
      ContDiff ℝ ∞ (fun z : ℝ × (Fin legs.length → Spacetime) =>
        A μ z.1 loop Λ Λ0 legs z.2)
  positive_scale_jet_continuity : ∀ μ g loop Λ0 legs
      (directions : List (Fin legs.length × Fin 4)) q,
    0 < μ → μ ≤ Λ0 →
      ContinuousOn (fun Λ : ℝ => momentumJet directions (A μ g loop Λ Λ0 legs) q)
        (Set.Ioc 0 Λ0)
  reduced_extension : ∀ μ g loop Λ Λ0 legs q,
    A μ g loop Λ Λ0 legs q = A μ g loop Λ Λ0 legs (conservingMomenta legs q)
  statistics : ∀ μ g loop Λ Λ0 legs q,
    (totalGhostNumber legs ≠ 0 ∨ oddCount legs % 2 ≠ 0) → A μ g loop Λ Λ0 legs q = 0
  graded_symmetry : ∀ μ g loop Λ Λ0 legs q (π : Equiv.Perm (Fin legs.length)),
    BalancedMomenta legs q →
    A μ g loop Λ Λ0 (permutedLegs legs π) (permutedMomenta legs π q) =
      permutationSign legs π * A μ g loop Λ Λ0 legs q
  vacuum_subtraction : ∀ μ g loop Λ Λ0 q, A μ g loop Λ Λ0 [] q = 0
  no_free_interaction : ∀ μ g Λ Λ0 legs q,
    legs.length ≤ 2 → A μ g 0 Λ Λ0 legs q = 0
  loop_integrable : ∀ μ g loop Λ Λ0 legs q,
    0 < μ → μ ≤ Λ0 → 0 < Λ → Λ < Λ0 → BalancedMomenta legs q →
      Integrable (linearFlowIntegrand (A μ g) loop Λ Λ0 legs q)
  flow : ∀ μ g loop Λ Λ0 legs q,
    0 < μ → μ ≤ Λ0 → 0 < Λ → Λ < Λ0 → legs ≠ [] → BalancedMomenta legs q →
      HasDerivAt (fun scale : ℝ => A μ g loop scale Λ0 legs q)
        (backgroundFlowRHS (A μ g) loop Λ Λ0 legs q) Λ
  irrelevant_uv : ∀ μ g loop Λ0 legs (directions : List (Fin legs.length × Fin 4)) q,
    0 < μ → μ ≤ Λ0 → ReducedDirections legs directions →
      4 < totalDimension legs + directions.length →
      momentumJet directions (A μ g loop Λ0 Λ0 legs) q = 0
  relevant_ir_regularity : ∀ μ g loop Λ0 legs (directions : List (Fin legs.length × Fin 4)),
    0 < μ → μ ≤ Λ0 → ReducedDirections legs directions →
      totalDimension legs + directions.length < 4 →
      ContDiffAt ℝ directions.length (A μ g loop 0 Λ0 legs) 0
  relevant_ir : ∀ μ g loop Λ0 legs (directions : List (Fin legs.length × Fin 4)),
    0 < μ → μ ≤ Λ0 → ReducedDirections legs directions →
      totalDimension legs + directions.length < 4 →
      momentumJet directions (A μ g loop 0 Λ0 legs) 0 = 0
  relevant_ir_limit : ∀ μ g loop Λ0 legs (directions : List (Fin legs.length × Fin 4)),
    0 < μ → μ ≤ Λ0 → ReducedDirections legs directions →
      totalDimension legs + directions.length < 4 →
      Filter.Tendsto (fun Λ : ℝ => momentumJet directions (A μ g loop Λ Λ0 legs) 0)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
  marginal : ∀ μ g loop Λ0 legs (directions : List (Fin legs.length × Fin 4)),
    0 < μ → μ ≤ Λ0 → ReducedDirections legs directions →
      totalDimension legs + directions.length = 4 →
      marginalJet (A μ g) loop μ Λ0 legs directions =
        momentumJet directions
          (fun q => marginalNormalization e scheme loop g legs (conservingMomenta legs q)) 0

/-- Actual all-order coupling coefficients are derivatives of the same
flow family, rather than an independent list named beta/gamma/predictions. -/
def couplingCoefficient (A : ScaleCouplingFamily G) (μ : ℝ) (loop order : ℕ)
    (Λ Λ0 : ℝ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) : ℂ :=
  (Nat.factorial order : ℂ)⁻¹ * iteratedDeriv order (fun g : ℝ => A μ g loop Λ Λ0 legs q) 0

def uvJetCouplingCoefficient (A : ScaleCouplingFamily G) (μ : ℝ) (loop order : ℕ)
    (Λ0 : ℝ) (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4)) : ℂ :=
  (Nat.factorial order : ℂ)⁻¹ * iteratedDeriv order
    (fun g : ℝ => uvLocalJet (A μ g) loop Λ0 legs directions) 0

def backgroundCouplingPower (legs : List (ExternalLeg G)) (loop : ℕ) : ℕ :=
  legs.length + 2 * loop - 2

/-- The graph-counting identity expected of the fixed action/flow. This
is an explicit equation, not a freely supplied coefficient sequence.
Deriving it from the flow and fixed local boundary data is still a
supporting equivalence theorem, not silently assumed here. -/
def GraphHomogeneous (A : ScaleCouplingFamily G) : Prop :=
  ∀ μ loop Λ Λ0 legs q g,
    A μ g loop Λ Λ0 legs q =
      (g : ℂ) ^ backgroundCouplingPower legs loop * A μ 1 loop Λ Λ0 legs q

theorem backgroundCouplingPower_gt (legs : List (ExternalLeg G))
    (order loop : ℕ) (h : order + 2 < loop) :
    order < backgroundCouplingPower legs loop := by
  unfold backgroundCouplingPower
  omega

/-- Fixed finite assembly in the coupling variable. The safe bound is
loop≤order+2. Proving all excluded loop jets vanish from graph homogeneity
and proving that homogeneity from the fixed generator remain explicit work. -/
def finiteLoopCoefficient (A : ScaleCouplingFamily G) (μ : ℝ) (order : ℕ)
    (Λ Λ0 : ℝ) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) : ℂ :=
  ∑ loop ∈ Finset.range (order + 3), couplingCoefficient A μ loop order Λ Λ0 legs q

def finiteLoopUVJetCoefficient (A : ScaleCouplingFamily G) (μ : ℝ) (order : ℕ)
    (Λ0 : ℝ) (legs : List (ExternalLeg G))
    (directions : List (Fin legs.length × Fin 4)) : ℂ :=
  ∑ loop ∈ Finset.range (order + 3), uvJetCouplingCoefficient A μ loop order Λ0 legs directions

end YangMills.PerturbativeFlow
