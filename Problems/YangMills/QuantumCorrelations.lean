import Problems.YangMills.QFT.Wightman

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true

/-!
# Genuine (smeared) vacuum correlation functions

Jaffe–Witten §4 requires the *short-distance correlations* of the same
Yang–Mills quantum operators to agree with asymptotic-freedom predictions.
This file defines their actual n-point functions from Wightman field products
and the vacuum. A candidate does not choose an arbitrary "correlation"
predicate or freely supplied set of n-point numbers.

Neither a UV limit nor a specific OPE follows from these definitions; those
remain open parts of the proposed specification.
-/

noncomputable section

namespace YangMills

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

namespace WightmanData

/-- The vacuum n-point function for an ordered word of smeared fields,
computed in the *same* Hilbert space as the Hamiltonian. -/
def vacuumNPoint (Q : WightmanData H)
    (word : List (Q.FieldIndex × TestFunction)) : ℂ :=
  inner ℂ (Q.vacuum : H) (Q.word word : H)

/-- One-point expectation of the operator-valued distribution. -/
def vacuumOnePoint (Q : WightmanData H)
    (i : Q.FieldIndex) (f : TestFunction) : ℂ :=
  Q.vacuumNPoint [(i, f)]

/-- Ordered two-point expectation, with the same observable indices and
test functions as the full Wightman field structure. -/
def vacuumTwoPoint (Q : WightmanData H)
    (i j : Q.FieldIndex) (f g : TestFunction) : ℂ :=
  Q.vacuumNPoint [(i, f), (j, g)]

@[simp] theorem vacuumNPoint_nil (Q : WightmanData H) :
    Q.vacuumNPoint [] =
      inner ℂ (Q.vacuum : H) (Q.vacuum : H) := rfl

@[simp] theorem vacuumNPoint_cons (Q : WightmanData H)
    (i : Q.FieldIndex) (f : TestFunction)
    (rest : List (Q.FieldIndex × TestFunction)) :
    Q.vacuumNPoint ((i, f) :: rest) =
      inner ℂ (Q.vacuum : H) (Q.field i f (Q.word rest) : H) := rfl

/-- The empty field word has vacuum expectation one as an actual
consequence of normalization, not an assumed correlation datum. -/
theorem vacuumNPoint_nil_eq_one (Q : WightmanData H)
    (h : WightmanAxioms H Q) :
    Q.vacuumNPoint [] = 1 := by
  simp [vacuumNPoint, word, inner_self_eq_norm_sq_to_K, h.vacuum_norm]

end WightmanData

end YangMills
