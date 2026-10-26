import Problems.YangMills.PerturbativeFlow
import Mathlib.RingTheory.PowerSeries.Basic

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Fixed local tensor coordinates of the physical Yang--Mills action

The five IZ (12-124)--(12-126) directions are actual action tensors.
Coordinates below are computed from UV jets, including S0, and never supplied
as a second independent list Z. A raw finite-cutoff action need not lie in
their span: its residual is defined explicitly, not assumed BRST closed.
Ward restoration and admissible finite scheme transport remain separate.
-/
noncomputable section
open scoped BigOperators
namespace YangMills.WardAction
open YangMills.Perturbative YangMills.PerturbativeFlow

variable {G : CompactSimpleGaugeGroup}

inductive Sector where
  | gluonKinetic | cubic | quartic | ghostKinetic | ghostVertex
  deriving DecidableEq, Fintype

def couplingOffset : Sector → ℕ
  | .cubic | .ghostVertex => 1
  | .quartic => 2
  | _ => 0

def ProbeIndex (G : CompactSimpleGaugeGroup) : Sector → Type
  | .gluonKinetic | .ghostKinetic => Fin G.dimension
  | .cubic | .ghostVertex => Fin G.dimension × Fin G.dimension × Fin G.dimension
  | .quartic => Fin G.dimension × Fin G.dimension

instance (sector : Sector) : Fintype (ProbeIndex G sector) := by
  cases sector <;> dsimp [ProbeIndex] <;> infer_instance

/-- Gluon/ghost kinetic probes are transverse p_0² coefficients. Cubic
and ghost-vertex probes use a first momentum derivative. Quartic probes
use alternating Lorentz components and repeated color pairs. -/
def probeLegs : (s : Sector) → ProbeIndex G s → List (ExternalLeg G)
  | .gluonKinetic, a => [.inl (.gauge 1 a), .inl (.gauge 1 a)]
  | .ghostKinetic, a => [.inl (.antighost a), .inl (.ghost a)]
  | .cubic, (a, b, c) => [.inl (.gauge 0 a), .inl (.gauge 1 b), .inl (.gauge 1 c)]
  | .ghostVertex, (a, b, c) => [.inl (.antighost a), .inl (.gauge 0 b), .inl (.ghost c)]
  | .quartic, (a, b) =>
      [.inl (.gauge 0 a), .inl (.gauge 1 b), .inl (.gauge 0 a), .inl (.gauge 1 b)]

def probeDirections (s : Sector) (i : ProbeIndex G s) :
    List (Fin (probeLegs s i).length × Fin 4) := by
  have hp : 0 < (probeLegs s i).length := by
    cases s with
    | gluonKinetic => simp [probeLegs]
    | ghostKinetic => simp [probeLegs]
    | cubic => rcases i with ⟨a, b, c⟩; simp [probeLegs]
    | ghostVertex => rcases i with ⟨a, b, c⟩; simp [probeLegs]
    | quartic => rcases i with ⟨a, b⟩; simp [probeLegs]
  let z : Fin (probeLegs s i).length := ⟨0, hp⟩
  exact if s = .quartic then [] else
    if s = .gluonKinetic ∨ s = .ghostKinetic then [(z, 0), (z, 0)] else [(z, 0)]

def probeTensor (s : Sector) (F : OrderedAmplitude G) (i : ProbeIndex G s) : ℂ :=
  momentumJet (probeDirections s i)
    (fun q => F (probeLegs s i) (conservingMomenta (probeLegs s i) q)) 0

def liftPhysical (terms : List (InteractionMonomial G)) : List (LocalVertex G) :=
  terms.map (fun m =>
    { coefficient := (m.coefficient : ℂ), couplingOrder := m.couplingOrder,
      legs := m.legs.map (fun k => ⟨.inl k.field, k.derivatives⟩) })

/-- Transverse kinetic term Σ B(dA,dA)/4 before gauge fixing. -/
def gluonKineticVertices (G : CompactSimpleGaugeGroup) : List (LocalVertex G) := do
  let μ ← List.finRange 4
  let ν ← List.finRange 4
  let a ← List.finRange G.dimension
  [ { coefficient := (1 / 2 : ℂ), couplingOrder := 0,
      legs := [⟨.inl (.gauge ν a), [μ]⟩, ⟨.inl (.gauge ν a), [μ]⟩] },
    { coefficient := -(1 / 2 : ℂ), couplingOrder := 0,
      legs := [⟨.inl (.gauge ν a), [μ]⟩, ⟨.inl (.gauge μ a), [ν]⟩] } ]

def ghostKineticVertices (G : CompactSimpleGaugeGroup) : List (LocalVertex G) := do
  let μ ← List.finRange 4
  let a ← List.finRange G.dimension
  [ { coefficient := 1, couplingOrder := 0,
      legs := [⟨.inl (.antighost a), [μ]⟩, ⟨.inl (.ghost a), [μ]⟩] } ]

def gaugeFixingVertices (G : CompactSimpleGaugeGroup) : List (LocalVertex G) := do
  let μ ← List.finRange 4
  let ν ← List.finRange 4
  let a ← List.finRange G.dimension
  [ { coefficient := (1 / 2 : ℂ), couplingOrder := 0,
      legs := [⟨.inl (.gauge μ a), [μ]⟩, ⟨.inl (.gauge ν a), [ν]⟩] } ]

def basisVertices {B : InvariantForm G} (e : ColorFrame B) : Sector → List (LocalVertex G)
  | .gluonKinetic => gluonKineticVertices G
  | .cubic => liftPhysical (cubicMonomials e)
  | .quartic => liftPhysical (quarticMonomials e)
  | .ghostKinetic => ghostKineticVertices G
  | .ghostVertex => liftPhysical (ghostMonomials e)

/-- Coupling is set to one only in the fixed tensor basis. The powers g/g²
are removed explicitly by couplingOffset when forming normalization series. -/
def basisAmplitude {B : InvariantForm G} (e : ColorFrame B) (s : Sector) : OrderedAmplitude G :=
  localPolynomialAmplitude (basisVertices e s) 1

def referenceTensor {B : InvariantForm G} (e : ColorFrame B) (s : Sector) : ProbeIndex G s → ℂ :=
  probeTensor s (basisAmplitude e s)

def tensorNorm {ι : Type*} [Fintype ι] (T : ι → ℂ) : ℝ := ∑ i, Complex.normSq (T i)

def tensorCoordinate {ι : Type*} [Fintype ι] (T F : ι → ℂ) : ℝ :=
  (∑ i, star (T i) * F i).re / tensorNorm T

theorem tensorNorm_pos {ι : Type*} [Fintype ι] (T : ι → ℂ) (h : ∃ i, T i ≠ 0) :
    0 < tensorNorm T := by
  obtain ⟨i, hi⟩ := h
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg (T j))
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩

theorem tensorCoordinate_scalar {ι : Type*} [Fintype ι] (T : ι → ℂ)
    (hn : tensorNorm T ≠ 0) (z : ℝ) :
    tensorCoordinate T (fun i => (z : ℂ) * T i) = z := by
  unfold tensorCoordinate tensorNorm at *
  have hpoint (i : ι) : (star (T i) * ((z : ℂ) * T i)).re = z * Complex.normSq (T i) := by
    simp [Complex.mul_re, Complex.normSq_apply]
    ring
  have hsum : (∑ i, star (T i) * ((z : ℂ) * T i)).re =
      z * ∑ i, Complex.normSq (T i) := by
    change Complex.reAddGroupHom (∑ i, star (T i) * ((z : ℂ) * T i)) = _
    rw [map_sum]
    change (∑ i, (star (T i) * ((z : ℂ) * T i)).re) = _
    simp_rw [hpoint]
    rw [Finset.mul_sum]
  rw [hsum]
  exact mul_div_cancel_right₀ z hn

def coordinate {B : InvariantForm G} (e : ColorFrame B) (s : Sector)
    (F : OrderedAmplitude G) : ℝ := tensorCoordinate (referenceTensor e s) (probeTensor s F)

/-- A direct proof that the projector recovers its advertised real
coefficient from actual tensor equality. Nondegeneracy is a concrete
property of the fixed actual-G tensor, not a candidate-selected meaning. -/
theorem coordinate_eq_of_tensor {B : InvariantForm G} (e : ColorFrame B) (s : Sector)
    (F : OrderedAmplitude G) (z : ℝ) (hn : tensorNorm (referenceTensor e s) ≠ 0)
    (h : ∀ i, probeTensor s F i = (z : ℂ) * referenceTensor e s i) :
    coordinate e s F = z := by
  unfold coordinate
  rw [funext h]
  exact tensorCoordinate_scalar _ hn z

/-- The same UV action, including S0. Gauge fixing is subtracted explicitly
to expose IZ's transverse Z3 direction. Auxiliary/BV sectors remain present
in F but are excluded from the physical projector probes. -/
def uvActionCoefficient (A : ScaleCouplingFamily G) (μ Λ0 : ℝ) (order : ℕ) : OrderedAmplitude G :=
  fun legs q =>
    (if order = 0 then freeVertexAmplitude G legs q -
      localPolynomialAmplitude (gaugeFixingVertices G) 0 legs q else 0) +
    finiteLoopCoefficient A μ order Λ0 Λ0 legs q

abbrev Series := PowerSeries ℝ

/-- Z3 and ghostZ3 include the quadratic free action. Cubic and ghost
vertex coordinates strip one power of g; quartic strips two. -/
def normalizationSeries {B : InvariantForm G} (e : ColorFrame B)
    (A : ScaleCouplingFamily G) (μ Λ0 : ℝ) (s : Sector) : Series :=
  PowerSeries.mk (fun k => coordinate e s (uvActionCoefficient A μ Λ0 (k + couplingOffset s)))

def Z3 {B : InvariantForm G} (e : ColorFrame B) (A : ScaleCouplingFamily G) (μ Λ0 : ℝ) : Series :=
  normalizationSeries e A μ Λ0 .gluonKinetic
def Z1 {B : InvariantForm G} (e : ColorFrame B) (A : ScaleCouplingFamily G) (μ Λ0 : ℝ) : Series :=
  normalizationSeries e A μ Λ0 .cubic
def Z4 {B : InvariantForm G} (e : ColorFrame B) (A : ScaleCouplingFamily G) (μ Λ0 : ℝ) : Series :=
  normalizationSeries e A μ Λ0 .quartic
def ghostZ3 {B : InvariantForm G} (e : ColorFrame B) (A : ScaleCouplingFamily G) (μ Λ0 : ℝ) : Series :=
  normalizationSeries e A μ Λ0 .ghostKinetic
def ghostZ1 {B : InvariantForm G} (e : ColorFrame B) (A : ScaleCouplingFamily G) (μ Λ0 : ℝ) : Series :=
  normalizationSeries e A μ Λ0 .ghostVertex

def reconstructedAmplitude {B : InvariantForm G} (e : ColorFrame B)
    (z : Sector → ℝ) : OrderedAmplitude G :=
  fun legs q => ∑ s : Sector, (z s : ℂ) * basisAmplitude e s legs q

/-- The raw residual is a fixed difference. No freely supplied remainder
can hide the longitudinal, mass, auxiliary or BRST-breaking components. -/
def residualAmplitude {B : InvariantForm G} (e : ColorFrame B) (F : OrderedAmplitude G) :
    OrderedAmplitude G :=
  fun legs q => F legs q - reconstructedAmplitude e (fun s => coordinate e s F) legs q

theorem action_reconstruction_identity {B : InvariantForm G} (e : ColorFrame B)
    (F : OrderedAmplitude G) (legs : List (ExternalLeg G)) (q : Fin legs.length → Spacetime) :
    F legs q = reconstructedAmplitude e (fun s => coordinate e s F) legs q +
      residualAmplitude e F legs q := by
  simp [residualAmplitude]

def IsPhysicalLeg : ExternalLeg G → Prop
  | .inl (.gauge _ _) | .inl (.ghost _) | .inl (.antighost _) => True
  | _ => False

/-- Exact equality of ALL physical local jets of dimension at most four.
This is the multiplicative physical-sector decomposition expected AFTER
the actual Ward-restoring scheme transport. It is deliberately not imposed
on the raw finite-cutoff action by definition. Here "physical sector" means
the propagating gauge/ghost terms of the textbook action, not the positive
physical Hilbert space: ghosts remain auxiliary gauge-fixed variables. -/
def PhysicalActionDecomposition {B : InvariantForm G} (e : ColorFrame B)
    (F : OrderedAmplitude G) (z : Sector → ℝ) : Prop :=
  ∀ (legs : List (ExternalLeg G)) (directions : List (Fin legs.length × Fin 4)),
    (∀ K ∈ legs, IsPhysicalLeg K) → ReducedDirections legs directions →
    totalDimension legs + directions.length ≤ 4 →
      momentumJet directions (fun q => F legs (conservingMomenta legs q)) 0 =
        ∑ s : Sector, (z s : ℂ) * momentumJet directions
          (fun q => basisAmplitude e s legs (conservingMomenta legs q)) 0

theorem probe_admissible (s : Sector) (i : ProbeIndex G s) :
    (∀ K ∈ probeLegs s i, IsPhysicalLeg K) ∧
      ReducedDirections (probeLegs s i) (probeDirections s i) ∧
      totalDimension (probeLegs s i) + (probeDirections s i).length ≤ 4 := by
  cases s with
  | gluonKinetic =>
    simp [probeLegs, probeDirections, IsPhysicalLeg, ReducedDirections, totalDimension,
      ExternalLeg.dimension, BasicField.dimension]
  | ghostKinetic =>
    simp [probeLegs, probeDirections, IsPhysicalLeg, ReducedDirections, totalDimension,
      ExternalLeg.dimension, BasicField.dimension]
  | cubic =>
    rcases i with ⟨a, b, c⟩
    simp [probeLegs, probeDirections, IsPhysicalLeg, ReducedDirections, totalDimension,
      ExternalLeg.dimension, BasicField.dimension]
  | ghostVertex =>
    rcases i with ⟨a, b, c⟩
    simp [probeLegs, probeDirections, IsPhysicalLeg, ReducedDirections, totalDimension,
      ExternalLeg.dimension, BasicField.dimension]
  | quartic =>
    rcases i with ⟨a, b⟩
    simp [probeLegs, probeDirections, IsPhysicalLeg, ReducedDirections, totalDimension,
      ExternalLeg.dimension, BasicField.dimension]

/-- Fixed support separation, still to be established for the concrete
listed tensors; it is not a free selection of dual projectors. -/
def CrossSectorSupport {B : InvariantForm G} (e : ColorFrame B) : Prop :=
  ∀ s t, s ≠ t → ∀ i : ProbeIndex G s, probeTensor s (basisAmplitude e t) i = 0

def FixedProbeNondegenerate {B : InvariantForm G} (e : ColorFrame B) : Prop :=
  ∀ s, tensorNorm (referenceTensor e s) ≠ 0

/-- Full local action equality forces the advertised coordinates. The two
remaining assumptions concern only fixed source tensors; neither can be
selected by the proof author to alter the extracted UV coordinates. -/
theorem PhysicalActionDecomposition.coordinates {B : InvariantForm G} (e : ColorFrame B)
    (F : OrderedAmplitude G) (z : Sector → ℝ) (h : PhysicalActionDecomposition e F z)
    (hcross : CrossSectorSupport e) (hn : FixedProbeNondegenerate e) (s : Sector) :
    coordinate e s F = z s := by
  apply coordinate_eq_of_tensor e s F (z s) (hn s)
  intro i
  have hp := probe_admissible s i
  have hh := h (probeLegs s i) (probeDirections s i) hp.1 hp.2.1 hp.2.2
  change probeTensor s F i = _ at hh
  rw [Finset.sum_eq_single s] at hh
  · exact hh
  · intro t _ hts
    have ht := hcross s t (Ne.symm hts) i
    change (z t : ℂ) * probeTensor s (basisAmplitude e t) i = 0
    rw [ht, mul_zero]
  · simp

end YangMills.WardAction
