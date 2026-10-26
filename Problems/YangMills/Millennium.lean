import Problems.YangMills.YangMillsSpecification

/-!
# Yang–Mills existence and mass gap

The entry point for the proposed Yang–Mills specification.
For every compact connected simple Lie gauge group it requires a
`YangMills.FilteredGeneratedCandidate`, tying the physical QFT and its positive
finite Hamiltonian mass gap to the same generated Yang–Mills data.

It is a proposed formalization, not an independently validated equivalence to
Jaffe–Witten or an existence proof.
-/

namespace MillenniumYangMills
universe u

/-- The proposed all-group Yang–Mills target, preserving its universe parameter. -/
abbrev ClayYangMills : Prop := YangMills.YangMillsExistenceAndMassGap.{u}

/-- The public entry point is definitionally the proposed specification. -/
theorem clayYangMills_iff_specification :
    ClayYangMills.{u} ↔ YangMills.YangMillsExistenceAndMassGap.{u} := Iff.rfl

end MillenniumYangMills
