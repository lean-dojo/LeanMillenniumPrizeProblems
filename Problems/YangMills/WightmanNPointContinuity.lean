import Problems.YangMills.QuantumCorrelations
import Mathlib.LinearAlgebra.Multilinear.Basic

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Actual vacuum n-point multilinearity and separate continuity

All values are the existing vacuum matrix elements of Q's same-domain
ordered field products. Reverse adjoint action moves every fixed preceding
field across the inner product, leaving a single varied field acting on a
fixed domain vector. The existing field_continuous axiom then proves actual
separate continuity at every slot; no continuity predicate is added to a
candidate. Ordered endomorphism products supply the exact multilinear map.

Promotion to joint continuity and the Schwartz nuclear kernel theorem are
not asserted here. They require additional supporting topological theorems,
not additional physical candidate axioms or freely selected distributions.
-/
noncomputable section
namespace YangMills
namespace WightmanData
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def wordAction (Q : WightmanData H) :
    List (Q.FieldIndex × TestFunction) → Q.domain →ₗ[ℂ] Q.domain
  | [] => LinearMap.id
  | (i,f) :: rest => (Q.field i f).comp (Q.wordAction rest)

lemma word_append_action (Q : WightmanData H)
    (before suffix : List (Q.FieldIndex × TestFunction)) :
    Q.word (before ++ suffix) = Q.wordAction before (Q.word suffix) := by
  induction before with
  | nil => rfl
  | cons head tail ih => cases head; simp only [List.cons_append, word, wordAction, LinearMap.comp_apply, ih]

/-- Reverse-order adjoint action on the same invariant domain. -/
def adjointWordAction (Q : WightmanData H) :
    List (Q.FieldIndex × TestFunction) → Q.domain → Q.domain
  | [] => id
  | (i,f) :: rest => fun v => Q.adjointWordAction rest
      (Q.field (Q.adjointIndex i) (Q.conjugateTest f) v)

lemma inner_field_right (Q : WightmanData H) (h : WightmanAxioms H Q)
    (i : Q.FieldIndex) (f : TestFunction) (v w : Q.domain) :
    inner ℂ (v : H) (Q.field i f w : H) =
      inner ℂ (Q.field (Q.adjointIndex i) (Q.conjugateTest f) v : H) (w : H) := by
  have hh := congrArg (starRingEnd ℂ) (h.adjoint_relation i f w v)
  simpa only [inner_conj_symm] using hh

lemma inner_wordAction_right (Q : WightmanData H) (h : WightmanAxioms H Q)
    (before : List (Q.FieldIndex × TestFunction)) (v w : Q.domain) :
    inner ℂ (v : H) (Q.wordAction before w : H) =
      inner ℂ (Q.adjointWordAction before v : H) (w : H) := by
  induction before generalizing v with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk i f =>
        change inner ℂ (v : H) (Q.field i f (Q.wordAction tail w) : H) = _
        rw [Q.inner_field_right h, ih]
        rfl

/-- One arbitrary slot of the actual vacuum word, as a linear map. -/
def vacuumSlot (Q : WightmanData H) (before : List (Q.FieldIndex × TestFunction))
    (i : Q.FieldIndex) (suffix : List (Q.FieldIndex × TestFunction)) : TestFunction →ₗ[ℂ] ℂ where
  toFun f := Q.vacuumNPoint (before ++ (i,f) :: suffix)
  map_add' f g := by
    simp only [vacuumNPoint, Q.word_append_action, word, map_add, LinearMap.add_apply, Submodule.coe_add, inner_add_right]
  map_smul' c f := by
    simp only [vacuumNPoint, Q.word_append_action, word, map_smul, LinearMap.smul_apply, Submodule.coe_smul,
      inner_smul_right, RingHom.id_apply, smul_eq_mul]

lemma vacuumSlot_adjoint (Q : WightmanData H) (h : WightmanAxioms H Q)
    (before : List (Q.FieldIndex × TestFunction)) (i : Q.FieldIndex)
    (suffix : List (Q.FieldIndex × TestFunction)) (f : TestFunction) :
    Q.vacuumSlot before i suffix f =
      inner ℂ (Q.adjointWordAction before Q.vacuum : H) (Q.field i f (Q.word suffix) : H) := by
  change inner ℂ (Q.vacuum : H) (Q.word (before ++ (i,f) :: suffix) : H) = _
  rw [Q.word_append_action]
  exact Q.inner_wordAction_right h before Q.vacuum (Q.field i f (Q.word suffix))

/-- Separate continuity at any ordered slot, including every interior slot. -/
theorem vacuumNPoint_slot_continuous (Q : WightmanData H) (h : WightmanAxioms H Q)
    (before : List (Q.FieldIndex × TestFunction)) (i : Q.FieldIndex)
    (suffix : List (Q.FieldIndex × TestFunction)) :
    Continuous (fun f : TestFunction => Q.vacuumNPoint (before ++ (i,f) :: suffix)) := by
  change Continuous (Q.vacuumSlot before i suffix)
  have eq : (Q.vacuumSlot before i suffix : TestFunction → ℂ) =
      fun f => inner ℂ (Q.adjointWordAction before Q.vacuum : H) (Q.field i f (Q.word suffix) : H) :=
    funext (Q.vacuumSlot_adjoint h before i suffix)
  rw [eq]
  exact continuous_const.inner (h.field_continuous i (Q.word suffix))

def vacuumSlotCLM (Q : WightmanData H) (h : WightmanAxioms H Q)
    (before : List (Q.FieldIndex × TestFunction)) (i : Q.FieldIndex)
    (suffix : List (Q.FieldIndex × TestFunction)) : TestFunction →L[ℂ] ℂ :=
  ⟨Q.vacuumSlot before i suffix, Q.vacuumNPoint_slot_continuous h before i suffix⟩

/-- The actual ordered product of field operators, without commutativity. -/
def fieldWordMultilinear (Q : WightmanData H) {n : ℕ} (indices : Fin n → Q.FieldIndex) :
    MultilinearMap ℂ (fun _ : Fin n => TestFunction) (Module.End ℂ Q.domain) :=
  (MultilinearMap.mkPiAlgebraFin ℂ n (Module.End ℂ Q.domain)).compLinearMap
    (fun i => Q.field (indices i))

def vacuumEndFunctional (Q : WightmanData H) : (Module.End ℂ Q.domain) →ₗ[ℂ] ℂ where
  toFun A := inner ℂ (Q.vacuum : H) (A Q.vacuum : H)
  map_add' A B := by simp [inner_add_right]
  map_smul' c A := by simp [inner_smul_right]

/-- Multilinearity is derived from the actual field algebra, not added as
an independent candidate n-point datum. -/
def vacuumMultilinear (Q : WightmanData H) {n : ℕ} (indices : Fin n → Q.FieldIndex) :
    MultilinearMap ℂ (fun _ : Fin n => TestFunction) ℂ :=
  Q.vacuumEndFunctional.compMultilinearMap (Q.fieldWordMultilinear indices)

lemma wordAction_eq_prod (Q : WightmanData H) (word : List (Q.FieldIndex × TestFunction)) :
    Q.wordAction word = (word.map fun p => Q.field p.1 p.2).prod := by
  induction word with
  | nil => rfl
  | cons head tail ih => cases head; simp only [wordAction, List.map_cons, List.prod_cons, ih]; rfl

lemma vacuumMultilinear_apply (Q : WightmanData H) {n : ℕ}
    (indices : Fin n → Q.FieldIndex) (tests : Fin n → TestFunction) :
    Q.vacuumMultilinear indices tests =
      Q.vacuumNPoint (List.ofFn fun i => (indices i, tests i)) := by
  change inner ℂ (Q.vacuum : H)
    (((List.ofFn fun i => Q.field (indices i) (tests i)).prod) Q.vacuum : H) = _
  rw [vacuumNPoint, show Q.word (List.ofFn fun i => (indices i, tests i)) =
    Q.wordAction (List.ofFn fun i => (indices i, tests i)) Q.vacuum by
      simpa only [List.append_nil, word] using
        Q.word_append_action (List.ofFn fun i => (indices i, tests i)) []]
  rw [Q.wordAction_eq_prod, List.map_ofFn]
  rfl

/-- The array-indexed form of the same interior-slot continuity theorem. -/
theorem vacuumMultilinear_separately_continuous (Q : WightmanData H)
    (h : WightmanAxioms H Q) {n : ℕ} (indices : Fin n → Q.FieldIndex)
    (tests : Fin n → TestFunction) (i : Fin n) :
    Continuous (fun f : TestFunction => Q.vacuumMultilinear indices (Function.update tests i f)) := by
  classical
  let word := List.ofFn fun j => (indices j, tests j)
  have word_eq (f : TestFunction) :
      (List.ofFn fun j => (indices j, Function.update tests i f j)) =
        word.take i.val ++ (indices i, f) :: word.drop (i.val+1) := by
    have pair_update : (fun j => (indices j, Function.update tests i f j)) =
        Function.update (fun j => (indices j, tests j)) i (indices i, f) := by
      funext j
      by_cases hj : j = i
      · subst j; simp
      · simp [Function.update_of_ne hj]
    rw [pair_update, List.ofFn_eq_map, (List.nodup_finRange n).map_update]
    simp only [List.mem_finRange, ↓reduceIte, List.idxOf_finRange]
    rw [← List.ofFn_eq_map]
    change word.set i.val (indices i, f) = _
    rw [List.set_eq_take_append_cons_drop, if_pos]
    simpa only [word, List.length_ofFn] using i.isLt
  have observation_eq :
      (fun f => Q.vacuumMultilinear indices (Function.update tests i f)) =
        fun f => Q.vacuumNPoint (word.take i.val ++ (indices i, f) :: word.drop (i.val+1)) := by
    funext f
    rw [Q.vacuumMultilinear_apply, word_eq]
  rw [observation_eq]
  exact Q.vacuumNPoint_slot_continuous h _ _ _

end WightmanData
end YangMills
