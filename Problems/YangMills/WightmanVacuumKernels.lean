import Problems.YangMills.QuantumCorrelations

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Tempered kernels of all actual Wightman vacuum words

A direct full-distribution presentation of the cited Wightman standard.
The kernel acts continuously on the actual full Schwartz test space.
Tensor tests are fixed pointwise, and every tensor value is the existing
vacuum expectation of Q's same-domain field product. Dense tensor span makes
these distributions unique; witnesses cannot select different correlations.
Existence/density of the standard Schwartz tensor realization and its kernel
correspondence are supporting mathematical theorems, not free predicates.
-/
noncomputable section
namespace YangMills
abbrev VacuumNPointTest (n : ℕ) := SchwartzMap (Fin n → Spacetime) ℂ

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

structure WightmanVacuumKernels (Q : WightmanData H) where
  tensor : (n : ℕ) → (Fin n → TestFunction) → VacuumNPointTest n
  tensor_eq : ∀ n tests x, tensor n tests x = ∏ i : Fin n, tests i (x i)
  tensor_dense : ∀ n, Dense ((Submodule.span ℂ (Set.range (tensor n))) : Set (VacuumNPointTest n))
  kernel : (n : ℕ) → (Fin n → Q.FieldIndex) → VacuumNPointTest n →L[ℂ] ℂ
  actual_words : ∀ n indices tests,
    kernel n indices (tensor n tests) =
      Q.vacuumNPoint (List.ofFn fun i => (indices i, tests i))

namespace WightmanVacuumKernels
variable {Q : WightmanData H}

/-- Tensor tests cannot be chosen differently by two kernel witnesses. -/
theorem tensor_unique (K L : WightmanVacuumKernels Q) (n : ℕ) (tests : Fin n → TestFunction) :
    K.tensor n tests = L.tensor n tests := by
  ext x
  rw [K.tensor_eq, L.tensor_eq]

/-- The full Schwartz distribution is uniquely fixed by its actual field
word values and tensor density. In particular there is no unrelated kernel. -/
theorem kernel_unique (K L : WightmanVacuumKernels Q) (n : ℕ) (indices : Fin n → Q.FieldIndex) :
    K.kernel n indices = L.kernel n indices := by
  have on_tensors : Set.EqOn (K.kernel n indices) (L.kernel n indices)
      (Set.range (K.tensor n)) := by
    rintro f ⟨tests, rfl⟩
    rw [K.actual_words, K.tensor_unique L n tests, L.actual_words]
  have on_span : Set.EqOn (K.kernel n indices) (L.kernel n indices)
      (Submodule.span ℂ (Set.range (K.tensor n))) :=
    LinearMap.eqOn_span' on_tensors
  apply DFunLike.ext
  intro f
  exact (K.kernel n indices).continuous.ext_on (K.tensor_dense n)
    (L.kernel n indices).continuous on_span ▸ rfl

/-- Every actual finite component word occurs, with no restriction on the
chosen field-index sequence or its test functions. -/
theorem actual_word_on_list (K : WightmanVacuumKernels Q)
    (word : List (Q.FieldIndex × TestFunction)) :
    K.kernel word.length (fun i => (word.get i).1)
      (K.tensor word.length (fun i => (word.get i).2)) = Q.vacuumNPoint word := by
  rw [K.actual_words]
  change Q.vacuumNPoint (List.ofFn fun i => word.get i) = _
  rw [List.ofFn_get]

/-- Any other continuous kernel with these same tensor observations is
already the same distribution; no independent compatibility meaning occurs. -/
theorem eq_of_actual_words (K : WightmanVacuumKernels Q) (n : ℕ)
    (indices : Fin n → Q.FieldIndex) (candidate : VacuumNPointTest n →L[ℂ] ℂ)
    (actual : ∀ tests, candidate (K.tensor n tests) =
      Q.vacuumNPoint (List.ofFn fun i => (indices i, tests i))) :
    candidate = K.kernel n indices := by
  have on_tensors : Set.EqOn candidate (K.kernel n indices) (Set.range (K.tensor n)) := by
    rintro f ⟨tests, rfl⟩
    rw [actual, K.actual_words]
  have on_span : Set.EqOn candidate (K.kernel n indices)
      (Submodule.span ℂ (Set.range (K.tensor n))) := LinearMap.eqOn_span' on_tensors
  apply DFunLike.ext
  intro f
  exact candidate.continuous.ext_on (K.tensor_dense n) (K.kernel n indices).continuous on_span ▸ rfl

end WightmanVacuumKernels
end YangMills
