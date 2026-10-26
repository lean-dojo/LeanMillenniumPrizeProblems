import Problems.YangMills.Renormalization
import Mathlib.Tactic.DeriveFintype

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Ordered graded coefficient conventions

External coefficients use ordered left functional derivatives. Basic fields
and antifields have the parity, dimension and ghost number in Table I of
Fröb--Holland--Hollands arXiv:1511.09425, printed p.14. Odd reordering signs
are fixed combinatorially; they are never amplitude-family parameters.
-/
noncomputable section
namespace YangMills.PerturbativeFlow
open YangMills.Perturbative

variable {G : CompactSimpleGaugeGroup}

deriving instance Fintype for BasicField

abbrev ExternalLeg (G : CompactSimpleGaugeGroup) := BasicField G ⊕ BasicField G

def ExternalLeg.parity : ExternalLeg G → Bool
  | .inl k => k.fermionic
  | .inr k => !k.fermionic

def ExternalLeg.dimension : ExternalLeg G → ℕ
  | .inl k => k.dimension
  | .inr k => 3 - k.dimension

def basicGhostNumber : BasicField G → ℤ
  | .ghost _ => 1
  | .antighost _ => -1
  | _ => 0

def ExternalLeg.ghostNumber : ExternalLeg G → ℤ
  | .inl k => basicGhostNumber k
  | .inr k => -1 - basicGhostNumber k

abbrev OrderedAmplitude (G : CompactSimpleGaugeGroup) :=
  (legs : List (ExternalLeg G)) → (Fin legs.length → Spacetime) → ℂ

/-- Loop order, IR scale, UV scale, ordered external legs and their momenta. -/
abbrev FlowFamily (G : CompactSimpleGaugeGroup) := ℕ → ℝ → ℝ → OrderedAmplitude G

def totalDimension (legs : List (ExternalLeg G)) : ℕ := (legs.map ExternalLeg.dimension).sum
def totalGhostNumber (legs : List (ExternalLeg G)) : ℤ := (legs.map ExternalLeg.ghostNumber).sum
def oddCount (legs : List (ExternalLeg G)) : ℕ := (legs.filter ExternalLeg.parity).length

/-- External indices retain their original relative order in each factor. -/
def selectedIndices {n : ℕ} (s : Finset (Fin n)) : List (Fin n) := s.sort (· ≤ ·)

def selectedLegs (legs : List (ExternalLeg G)) (s : Finset (Fin legs.length)) :
    List (ExternalLeg G) := (selectedIndices s).map legs.get

def selectedMomenta (legs : List (ExternalLeg G)) (s : Finset (Fin legs.length))
    (q : Fin legs.length → Spacetime) : Fin (selectedLegs legs s).length → Spacetime :=
  fun i => q ((selectedIndices s).get ⟨i.val, by simpa [selectedLegs] using i.isLt⟩)

def complementIndices (legs : List (ExternalLeg G)) (s : Finset (Fin legs.length)) :
    Finset (Fin legs.length) := Finset.univ \ s

/-- Koszul inversions of the unshuffle (selected indices, remaining indices).
This counts only crossings of odd generators. -/
def splitSignExponent (legs : List (ExternalLeg G)) (s : Finset (Fin legs.length)) : ℕ :=
  ∑ i ∈ s, ∑ j ∈ complementIndices legs s,
    if j < i ∧ (legs.get i).parity = true ∧ (legs.get j).parity = true then 1 else 0

def splitSign (legs : List (ExternalLeg G)) (s : Finset (Fin legs.length)) : ℂ :=
  (-1 : ℂ) ^ splitSignExponent legs s

def prependMomenta {legs : List (ExternalLeg G)} (leg : ExternalLeg G) (p : Spacetime)
    (q : Fin legs.length → Spacetime) : Fin (leg :: legs).length → Spacetime := Fin.cases p q

def selectedMomentum (legs : List (ExternalLeg G)) (s : Finset (Fin legs.length))
    (q : Fin legs.length → Spacetime) : Spacetime := ∑ i ∈ s, q i

/-- The sign of an arbitrary external permutation. -/
def permutationSign (legs : List (ExternalLeg G)) (π : Equiv.Perm (Fin legs.length)) : ℂ :=
  (-1 : ℂ) ^ (∑ i : Fin legs.length, ∑ j : Fin legs.length,
    if i < j ∧ π j < π i ∧ (legs.get (π i)).parity = true ∧ (legs.get (π j)).parity = true
      then 1 else 0)

def permutedLegs (legs : List (ExternalLeg G)) (π : Equiv.Perm (Fin legs.length)) :
    List (ExternalLeg G) := List.ofFn (fun i => legs.get (π i))

def permutedMomenta (legs : List (ExternalLeg G)) (π : Equiv.Perm (Fin legs.length))
    (q : Fin legs.length → Spacetime) : Fin (permutedLegs legs π).length → Spacetime :=
  fun i => q (π ⟨i.val, by simpa [permutedLegs] using i.isLt⟩)

end YangMills.PerturbativeFlow
