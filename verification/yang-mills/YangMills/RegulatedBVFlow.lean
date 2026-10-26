import YangMills.FreeWardExtraction

/-!
# Explicit regulated BV defects of the same coefficient family

These are coefficient forms of FHH 1511.09425 (290)--(294), (302).
Right/left derivative conversion is fixed by intrinsic parity; ghosts never
become commuting numerical field values. The background functional carries
its momentum delta; its bracket with an insertion therefore fixes the internal
momentum, whereas the BV Laplacian integrates a basic/antifield pair.
The equivalence to the density/Euler quotient is supporting work.
-/
noncomputable section
open MeasureTheory
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative
variable {G : CompactSimpleGaugeGroup}

/-- D_R,z F=(-1)^(p(z)(p(F)+1)) D_L,z F. -/
def rightDerivativeSign (functionalParity : Bool) (field : ExternalLeg G) : ℂ :=
  if field.parity && !functionalParity then -1 else 1

/-- The kinetic part of S0^UV has R_UV^-1, cancelling the R in the bracket.
Its antifield coupling is unweighted and retains R in its contribution.
This separates the two terms of source (290), rather than multiplying the
whole unregulated free differential by a guessed common regulator. -/
def regulatedFreeBVKernel (ultraviolet : ℝ)
    (source target : ExternalLeg G) (p : Spacetime) : ℂ :=
  (if source.isRight && target.isLeft then 1 else
    (exponentialRegulator ultraviolet p : ℂ)) * freeBVKernel source target p

def regulatedFreeWardAmplitude (ultraviolet : ℝ) (A : OrderedAmplitude G) : OrderedAmplitude G :=
  fun legs q => ∑ i : Fin legs.length, ∑ source : ExternalLeg G,
    (-1 : ℂ) ^ oddCount (legs.take i.val) *
      regulatedFreeBVKernel ultraviolet source (legs.get i) (q i) *
      A (replaceExternal legs i source) (replacedMomenta legs i source q)

/-- One ordered partition in the regulated odd antibracket, with a
momentum-conserving functional in the first slot. Both signs in source
(291) and the right-derivative conversion are explicit. -/
def regulatedBVSplit (leftParity : Bool) (F G' : FlowFamily G)
    (loop leftLoop : ℕ) (Λ Λ0 : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (s : Finset (Fin legs.length)) : ℂ :=
  let t := complementIndices legs s
  let k := selectedMomentum legs s q
  splitSign legs s * (exponentialRegulator Λ0 k : ℂ) *
    ∑ K : BasicField G,
      (rightDerivativeSign leftParity (.inl K) *
        F leftLoop Λ Λ0 (.inl K :: selectedLegs legs s)
          (prependMomenta (.inl K) (-k) (selectedMomenta legs s q)) *
        G' (loop - leftLoop) Λ Λ0 (.inr K :: selectedLegs legs t)
          (prependMomenta (.inr K) k (selectedMomenta legs t q)) -
      rightDerivativeSign leftParity (.inr K) *
        F leftLoop Λ Λ0 (.inr K :: selectedLegs legs s)
          (prependMomenta (.inr K) (-k) (selectedMomenta legs s q)) *
        G' (loop - leftLoop) Λ Λ0 (.inl K :: selectedLegs legs t)
          (prependMomenta (.inl K) k (selectedMomenta legs t q)))

def regulatedBVBracket (leftParity : Bool) (F G' : FlowFamily G)
    (loop : ℕ) (Λ Λ0 : ℝ) : OrderedAmplitude G :=
  fun legs q => ∑ l : Fin (loop + 1),
    ∑ s ∈ (Finset.univ : Finset (Fin legs.length)).powerset,
      regulatedBVSplit leftParity F G' loop l.val Λ Λ0 legs q s

/-- The right antifield derivative acts first in (294); the following
left basic derivative is the second entry of the ordered amplitude. -/
def regulatedBVLaplacianIntegrand (functionalParity : Bool) (ultraviolet : ℝ)
    (A : OrderedAmplitude G) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (p : Spacetime) : ℂ :=
  ((exponentialRegulator ultraviolet p : ℂ) *
    ∑ K : BasicField G, rightDerivativeSign functionalParity (.inr K) *
      A (.inr K :: .inl K :: legs)
        (prependMomenta (.inr K) p (prependMomenta (.inl K) (-p) q))) /
      (2 * Real.pi : ℂ) ^ 4

def regulatedBVLaplacian (functionalParity : Bool) (ultraviolet : ℝ)
    (A : OrderedAmplitude G) : OrderedAmplitude G :=
  fun legs q => ∫ p, regulatedBVLaplacianIntegrand functionalParity ultraviolet A legs q p

/-- The fixed bare action defect W^UV, including the exact loop shift of
hbar Delta. Delta S0^UV=0 is a separate fixed classical identity.
No continuum Ward conclusion is assumed by this definition. -/
def bareActionWardDefect (L : FlowFamily G) (loop : ℕ) (ultraviolet : ℝ) : OrderedAmplitude G :=
  fun legs q =>
    regulatedFreeWardAmplitude ultraviolet (L loop ultraviolet ultraviolet) legs q +
      (1 / 2 : ℂ) * regulatedBVBracket false L L loop ultraviolet ultraviolet legs q +
      if loop = 0 then 0 else regulatedBVLaplacian false ultraviolet
        (L (loop - 1) ultraviolet ultraviolet) legs q

/-- Bare point-pair antibracket kernel at the origin, without Fourier phase
or (2pi)^-4. The two local insertion momenta are +p and -p as in source (338).
Right/left derivative and external unshuffle signs are fixed. -/
def pairBVFourierSplit (leftParity : Bool) (F G' : FlowFamily G)
    (loop leftLoop : ℕ) (Λ Λ0 : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (s : Finset (Fin legs.length)) (p : Spacetime) : ℂ :=
  (exponentialRegulator Λ0 p : ℂ) * splitSign legs s *
    ∑ K : BasicField G,
      (rightDerivativeSign leftParity (.inl K) *
        F leftLoop Λ Λ0 (.inl K :: selectedLegs legs s)
          (prependMomenta (.inl K) p (selectedMomenta legs s q)) *
        G' (loop - leftLoop) Λ Λ0 (.inr K :: selectedLegs legs (complementIndices legs s))
          (prependMomenta (.inr K) (-p) (selectedMomenta legs (complementIndices legs s) q)) -
      rightDerivativeSign leftParity (.inr K) *
        F leftLoop Λ Λ0 (.inr K :: selectedLegs legs s)
          (prependMomenta (.inr K) p (selectedMomenta legs s q)) *
        G' (loop - leftLoop) Λ Λ0 (.inl K :: selectedLegs legs (complementIndices legs s))
          (prependMomenta (.inl K) (-p) (selectedMomenta legs (complementIndices legs s) q)))

def pairBVFourierKernel (leftParity : Bool) (F G' : FlowFamily G)
    (loop : ℕ) (Λ Λ0 : ℝ) (legs : List (ExternalLeg G))
    (q : Fin legs.length → Spacetime) (p : Spacetime) : ℂ :=
  ∑ l : Fin (loop + 1), ∑ s ∈ (Finset.univ : Finset (Fin legs.length)).powerset,
    pairBVFourierSplit leftParity F G' loop l.val Λ Λ0 legs q s p

/-- All BV contraction integrals must be genuine before the defect can be
used as input to Ward-restoration/transport conditions. -/
structure BVContractionIntegrability (L : FlowFamily G) : Prop where
  laplacian : ∀ loop Λ0 legs q, 0 < Λ0 → BalancedMomenta legs q →
    Integrable (regulatedBVLaplacianIntegrand false Λ0 (L loop Λ0 Λ0) legs q)

end YangMills.PerturbativeFlow
