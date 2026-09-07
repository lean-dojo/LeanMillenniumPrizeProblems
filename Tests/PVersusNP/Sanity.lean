import Problems.PVersusNP.Millennium

/-!
# Sanity tests for the P versus NP statement

Positive facts that must keep holding under the corrected definition of `NP`
(`Millennium.InNondeterministicPolynomialTime`: certificates are finite strings over a finite
alphabet, and the checking relation must be decided on *every* pair `w#y`):

* a concrete language is in `P` via Mathlib's identity machine (`trueLanguage_in_P`);
* the empty language over `Bool`-strings is in `P` and in `NP`, witnessed by an explicit two-stack
  machine that drains its input and outputs `false` (`emptyLanguage_in_P`, `emptyLanguage_in_NP`);
  so the corrected `NP` is satisfiable with string certificates and a real checking machine;
* `P ⊆ NP` still follows from the composition-closure hypothesis (`P_subset_NP`);
* the main equivalence theorems use only the standard axioms (checked with `#guard_msgs`).

Everything here is `sorry`-free and is built by `lake build` (library `Tests`).
-/

namespace Tests.PVersusNP

open Millennium Turing Computability StateTransition

/-! ### A language in `P` from Mathlib's identity machine -/

/-- `{true} ⊆ Bool` is decided by the identity machine in one step. -/
theorem trueLanguage_in_P : InPolynomialTime finEncodingBoolBool (fun b : Bool => b = true) :=
  ⟨id, idComputableInPolyTime finEncodingBoolBool.encode, fun _ => Iff.rfl⟩

/-! ### An explicit linear-time machine deciding the empty language -/

/-- Stack alphabets: the input stack (`true`) carries `Γ₀`, the output stack (`false`) carries
`Bool`.  Reducible so that `simp` can see `StkΓ Γ₀ true = Γ₀` in the step lemmas. -/
abbrev StkΓ (Γ₀ : Type) : Bool → Type
  | true => Γ₀
  | false => Bool

/-- Pop the input stack until it is empty, then push `false` on the output stack, reset the state
and halt. -/
def constFalseMachine (Γ₀ : Type) [Fintype Γ₀] : FinTM2 where
  K := Bool
  k₀ := true
  k₁ := false
  Γ := StkΓ Γ₀
  Λ := Unit
  main := ()
  σ := Bool
  initialState := true
  Γk₀Fin := inferInstanceAs (Fintype Γ₀)
  m _ :=
    TM2.Stmt.pop true (fun _ x => x.isSome)
      (TM2.Stmt.branch (fun v => v) (TM2.Stmt.goto fun _ => ())
        (TM2.Stmt.push false (fun _ => false) (TM2.Stmt.load (fun _ => true) TM2.Stmt.halt)))

variable (Γ₀ : Type) [Fintype Γ₀]

/-- Explicit configurations of `constFalseMachine`. -/
def cfg (l : Option Unit) (v : Bool) (inp : List Γ₀) (out : List Bool) :
    (constFalseMachine Γ₀).Cfg where
  l := l
  var := v
  stk
    | true => inp
    | false => out

/-- Unfold the machine and compare configurations componentwise. -/
macro "step_tac" : tactic =>
  `(tactic| (simp [FinTM2.step, TM2.step, TM2.stepAux, constFalseMachine, cfg]
             try (congr <;> first | rfl | (funext k; cases k <;> rfl) | (simp; done))))

theorem step_cons (v : Bool) (a : Γ₀) (inp : List Γ₀) (out : List Bool) :
    (constFalseMachine Γ₀).step (cfg Γ₀ (some ()) v (a :: inp) out) =
      some (cfg Γ₀ (some ()) true inp out) := by
  step_tac

theorem step_nil (v : Bool) (out : List Bool) :
    (constFalseMachine Γ₀).step (cfg Γ₀ (some ()) v [] out) =
      some (cfg Γ₀ none true [] (false :: out)) := by
  step_tac

/-- Weaken a time bound. -/
def EvalsToInTime.mono {σ : Type} {f : σ → Option σ} {a : σ} {b : Option σ} {m m' : ℕ}
    (h : EvalsToInTime f a b m) (hm : m ≤ m') : EvalsToInTime f a b m' :=
  ⟨h.toEvalsTo, le_trans h.steps_le_m hm⟩

/-- One step. -/
def oneStep {a b : (constFalseMachine Γ₀).Cfg} (h : (constFalseMachine Γ₀).step a = some b) :
    EvalsToInTime (constFalseMachine Γ₀).step a (some b) 1 :=
  { steps := 1
    evals_in_steps := by simpa [flip, Option.bind] using h
    steps_le_m := le_rfl }

/-- Draining the input takes one step per symbol; the final step writes the output. -/
def run (inp : List Γ₀) (v : Bool) (out : List Bool) :
    EvalsToInTime (constFalseMachine Γ₀).step (cfg Γ₀ (some ()) v inp out)
      (some (cfg Γ₀ none true [] (false :: out))) (inp.length + 1) := by
  induction inp generalizing v with
  | nil => simpa using oneStep Γ₀ (step_nil Γ₀ v out)
  | cons a t ih =>
      have h₁ := oneStep Γ₀ (step_cons Γ₀ v a t out)
      have h₂ := ih true
      have h := EvalsToInTime.trans (constFalseMachine Γ₀).step 1 (t.length + 1) _ _ _ h₁ h₂
      exact EvalsToInTime.mono h (by simp)

theorem initList_eq (inp : List Γ₀) :
    initList (constFalseMachine Γ₀) inp = cfg Γ₀ (some ()) true inp [] := by
  unfold initList cfg
  congr
  funext k
  cases k <;> rfl

theorem haltList_eq (out : List Bool) :
    haltList (constFalseMachine Γ₀) out = cfg Γ₀ none true [] out := by
  unfold haltList cfg
  congr
  funext k
  cases k <;> rfl

/-- The constant-`false` machine, packaged as a polynomial-time computation of `fun _ => false`
for any input encoding. -/
noncomputable def constFalseDecider {α : Type} (ea : FinEncoding α) :
    TM2ComputableInPolyTime ea.encode finEncodingBoolBool.encode (fun _ : α => false) where
  tm := constFalseMachine ea.Γ
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + 1
  outputsFun a := by
    show EvalsToInTime (constFalseMachine ea.Γ).step
      (initList (constFalseMachine ea.Γ) (List.map id (ea.encode a)))
      (some (haltList (constFalseMachine ea.Γ) (List.map id [false])))
      ((Polynomial.X + 1 : Polynomial ℕ).eval (ea.encode a).length)
    rw [List.map_id, List.map_id, initList_eq, haltList_eq]
    exact EvalsToInTime.mono (run ea.Γ (ea.encode a) true []) (by simp)

/-- The empty language over `Bool`-strings is in `P`. -/
theorem emptyLanguage_in_P :
    InPolynomialTime (fin_encoding_string Bool) (fun _ : List Bool => False) :=
  ⟨fun _ => false, constFalseDecider _, fun _ => by simp⟩

/-- The empty language over `Bool`-strings is in `NP`: certificates are `Bool`-strings and the
constant-`False` checking relation is decided by the constant-`false` machine on every `w#y`. -/
theorem emptyLanguage_in_NP :
    InNondeterministicPolynomialTime (fin_encoding_string Bool) (fun _ : List Bool => False) :=
  ⟨Bool, inferInstance, fun _ _ => False, 0,
    ⟨fun _ => false, constFalseDecider _, fun _ => by simp⟩, fun _ => by simp⟩

/-! ### Structural facts that must survive -/

/-- `P ⊆ NP` still follows from composition closure of the machine model. -/
theorem P_subset_NP (hComp : ClayPVersusNP.Support.PolynomialTimeComputableComposition)
    (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet] (L : Language (List alphabet))
    (hP : InPolynomialTime (fin_encoding_string alphabet) L) :
    InNondeterministicPolynomialTime (fin_encoding_string alphabet) L :=
  PolynomialTimeContainedInNondeterministicPolynomialTime.of_turing_machine_composition hComp
    alphabet L hP

/-- The Clay verifier wording still coincides with `NP`. -/
example (alphabet : Type) [Fintype alphabet] (L : Language (List alphabet)) :
    ClayVerifiableLanguage alphabet L ↔
      InNondeterministicPolynomialTime (fin_encoding_string alphabet) L :=
  ClayVerifiableLanguage.iff_in_nondeterministic_polynomial_time alphabet L

/-- `NegativeBranch` is literally the negation of the positive target. -/
example : ClayPVersusNP.Formulations.NegativeBranch ↔ ¬ ClayPVersusNP := Iff.rfl

/-! ### Axiom checks

These fail the build if any of the listed theorems ever picks up `sorryAx`. -/

/-- info: 'Millennium.ClayVerifiableLanguage.iff_in_nondeterministic_polynomial_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClayVerifiableLanguage.iff_in_nondeterministic_polynomial_time

/-- info: 'Millennium.ClayPVersusNP.Formulations.ClassEquality.iff_hard_direction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClayPVersusNP.Formulations.ClassEquality.iff_hard_direction

/-- info: 'Millennium.ClayPVersusNP.iff_checkable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClayPVersusNP.iff_checkable

/-- info: 'Millennium.ClayPVersusNP.Consequences.NondeterministicPolynomialTimeCompleteInPolynomialTime.of_turing_machine_composition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClayPVersusNP.Consequences.NondeterministicPolynomialTimeCompleteInPolynomialTime.of_turing_machine_composition

/-- info: 'Tests.PVersusNP.emptyLanguage_in_NP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms emptyLanguage_in_NP

/-- info: 'Tests.PVersusNP.emptyLanguage_in_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms emptyLanguage_in_P

end Tests.PVersusNP
