import Problems.YangMills.GaugeGroup
import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic.Group

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Genuine gauge-group dependence of finite holonomy data

This module defines link variables valued in the actual compact simple group
`G.Carrier`, and their action under vertex-dependent gauge transformations.
Path holonomy is computed by multiplication in *that group*; loop holonomy
transforms by conjugation and hence its conjugacy class is gauge-invariant.

This does NOT define the continuum quantum theory, supply renormalized
observables or prove the mass gap. The invariants are non-local lattice
observables, whereas the Jaffe–Witten statement also demands renormalized
local curvature observables. These definitions provide a canonical
group-specific algebraic testbed, not a Clay certification shortcut.

These definitions may be replaced by the official Physlib lattice-QFT APIs
when its roadmap implements link variables, holonomy and Wilson loops, after
checking that the gauge action and generality agree.
-/

noncomputable section

namespace YangMills

universe u v

/-- A composable oriented walk with specified initial and terminal vertices. -/
inductive GaugeWalk (V : Type u) : V → V → Type u where
  | stop (a : V) : GaugeWalk V a a
  | cons (a b : V) {c : V} :
      GaugeWalk V b c → GaugeWalk V a c

/-- On a finite or infinite set of vertices, a directed link assigns an
element of the *actual gauge group* to each oriented pair. -/
abbrev GaugeLinks (V : Type u) (G : CompactSimpleGaugeGroup.{v}) :=
  V → V → G.Carrier

/-- Local gauge transformations are vertex-dependent group elements. -/
def gaugeTransform {V : Type u} (G : CompactSimpleGaugeGroup.{v})
    (h : V → G.Carrier) (links : GaugeLinks V G) :
    GaugeLinks V G :=
  fun a b => h a * links a b * (h b)⁻¹

/-- The ordered product of link variables along a composable walk. -/
def gaugeHolonomy {V : Type u} {G : CompactSimpleGaugeGroup.{v}}
    (links : GaugeLinks V G) : {a b : V} → GaugeWalk V a b → G.Carrier
  | _, _, .stop _ => 1
  | _, _, .cons a b rest =>
      links a b * gaugeHolonomy links rest

@[simp] theorem gaugeTransform_one {V : Type u}
    (G : CompactSimpleGaugeGroup.{v}) (links : GaugeLinks V G) :
    gaugeTransform G (fun _ => 1) links = links := by
  funext a b
  simp [gaugeTransform]

theorem gaugeTransform_comp {V : Type u}
    (G : CompactSimpleGaugeGroup.{v})
    (h k : V → G.Carrier) (links : GaugeLinks V G) :
    gaugeTransform G h (gaugeTransform G k links) =
      gaugeTransform G (fun a => h a * k a) links := by
  funext a b
  simp only [gaugeTransform]
  group

/-- The precise endpoint-covariance law: for a closed path it is conjugation. -/
theorem gaugeHolonomy_transform {V : Type u}
    (G : CompactSimpleGaugeGroup.{v})
    (h : V → G.Carrier) (links : GaugeLinks V G)
    {a b : V} (walk : GaugeWalk V a b) :
    gaugeHolonomy (gaugeTransform G h links) walk =
      h a * gaugeHolonomy links walk * (h b)⁻¹ := by
  induction walk with
  | stop a =>
      simp [gaugeHolonomy]
  | @cons a b c tail ih =>
      simp only [gaugeHolonomy, gaugeTransform, ih]
      group

/-- A closed-loop observable in the *canonical conjugacy-class space of G*.
No choice of faithful representation, arbitrary character or placeholder
predicate is needed. -/
def wilsonConjugacyClass {V : Type u}
    (G : CompactSimpleGaugeGroup.{v}) (links : GaugeLinks V G)
    {a : V} (loop : GaugeWalk V a a) : ConjClasses G.Carrier :=
  ConjClasses.mk (gaugeHolonomy links loop)

/-- Gauge invariance of the conjugacy class (not of untraced holonomy). -/
theorem wilsonConjugacyClass_gauge_invariant {V : Type u}
    (G : CompactSimpleGaugeGroup.{v})
    (h : V → G.Carrier) (links : GaugeLinks V G)
    {a : V} (loop : GaugeWalk V a a) :
    wilsonConjugacyClass G (gaugeTransform G h links) loop =
      wilsonConjugacyClass G links loop := by
  rw [wilsonConjugacyClass, wilsonConjugacyClass,
      ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
  refine ⟨(h a)⁻¹, ?_⟩
  rw [gaugeHolonomy_transform]
  group

/-- A rectangular four-link loop with a fixed basepoint. -/
def squareGaugeLoop {V : Type u} (a b c d : V) : GaugeWalk V a a :=
  .cons a b (.cons b c (.cons c d (.cons d a (.stop a))))

/-- Explicit noncommutative order of a square's four directed links. -/
theorem squareGaugeLoop_holonomy {V : Type u}
    {G : CompactSimpleGaugeGroup.{v}}
    (links : GaugeLinks V G) (a b c d : V) :
    gaugeHolonomy links (squareGaugeLoop a b c d) =
      links a b * links b c * links c d * links d a := by
  simp [squareGaugeLoop, gaugeHolonomy]
  group

end YangMills
