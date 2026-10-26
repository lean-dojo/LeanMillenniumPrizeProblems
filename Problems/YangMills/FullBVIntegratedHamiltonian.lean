import Problems.YangMills.FullBVLocalIntegration

set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option linter.unusedSimpArgs false
namespace YangMills.FullBV
variable {G : CompactSimpleGaugeGroup}

theorem jetSummands_finite (F : Jet G → JetAlgebra G) (P : JetAlgebra G) :
    (Function.support (fun j => F j * leftPartialJet j P)).Finite := by
  apply (jetPartialsSupport_finite P).subset
  intro j hj
  contrapose! hj
  have hz : leftPartialJet j P = 0 := not_not.mp hj
  simp [hz]

theorem jetConditionalSummands_finite (F : Jet G → JetAlgebra G) (P : JetAlgebra G)
    (p : Jet G → Prop) [DecidablePred p] :
    (Function.support (fun j => if p j then F j * leftPartialJet j P else 0)).Finite := by
  apply (jetPartialsSupport_finite P).subset
  intro j hj
  contrapose! hj
  have hz : leftPartialJet j P = 0 := not_not.mp hj
  simp [hz]

/-- The pointwise operator uses every actual nonzero jet partial, with its
Euler-derived Hamiltonian characteristic; even/odd indexing adds no data. -/
theorem localST_finsum_jet (S P : JetAlgebra G) :
    localST S P = ∑ᶠ j : Jet G, prolongedST S j * leftPartialJet j P := by
  classical
  have he : (∑ᶠ j : EvenJet G, prolongedST S j.val * evenPartial j P) =
      ∑ᶠ j : Jet G, if j.field.parity = false then prolongedST S j * leftPartialJet j P else 0 := by
    calc
      _ = ∑ᶠ j : EvenJet G, prolongedST S j.val * leftPartialJet j.val P := by
        apply finsum_congr
        intro j
        simp [leftPartialJet, j.property]
      _ = _ := by
        simpa only [finsum_eq_if] using
          (finsum_subtype_eq_finsum_cond
            (f := fun j : Jet G => prolongedST S j * leftPartialJet j P)
            (fun j => j.field.parity = false))
  have ho : (∑ᶠ j : OddJet G, prolongedST S j.val * oddPartial j P) =
      ∑ᶠ j : Jet G, if j.field.parity = true then prolongedST S j * leftPartialJet j P else 0 := by
    calc
      _ = ∑ᶠ j : OddJet G, prolongedST S j.val * leftPartialJet j.val P := by
        apply finsum_congr
        intro j
        simp [leftPartialJet, j.property]
      _ = _ := by
        simpa only [finsum_eq_if] using
          (finsum_subtype_eq_finsum_cond
            (f := fun j : Jet G => prolongedST S j * leftPartialJet j P)
            (fun j => j.field.parity = true))
  change (∑ᶠ j : EvenJet G, prolongedST S j.val * evenPartial j P) +
    (∑ᶠ j : OddJet G, prolongedST S j.val * oddPartial j P) = _
  rw [he,ho, ← finsum_add_distrib
    (jetConditionalSummands_finite (prolongedST S) P (fun j => j.field.parity = false))
    (jetConditionalSummands_finite (prolongedST S) P (fun j => j.field.parity = true))]
  apply finsum_congr
  intro j
  cases j.field.parity <;> simp

/-- Left Euler differentiation is exactly the integration-by-parts adjoint
of prolonging the actual Hamiltonian characteristic. -/
theorem localClass_characteristicEuler (C P : JetAlgebra G)
    (field : YangMills.PerturbativeFlow.ExternalLeg G) :
    localClass (C * leftEuler field P) =
      ∑ᶠ alpha : Multiindex,
        localClass (totalDerivatives alpha C * leftPartialJet ⟨field,alpha⟩ P) := by
  let L : JetAlgebra G →ₗ[ℂ] LocalFunctional G :=
    (divergences G).mkQ.comp (LinearMap.mulLeft ℂ C)
  change L (leftEuler field P) = _
  unfold leftEuler
  trans ∑ᶠ alpha : Multiindex, L (((-1 : ℂ) ^ derivativeOrder alpha) •
    totalDerivatives alpha (leftPartialJet ⟨field,alpha⟩ P))
  · exact L.toAddMonoidHom.map_finsum (leftEulerSummands_finite field P)
  apply finsum_congr
  intro alpha
  change localClass (C * (((-1 : ℂ) ^ derivativeOrder alpha) •
    totalDerivatives alpha (leftPartialJet ⟨field,alpha⟩ P))) = _
  rw [localClass_integrateByParts_multi]
  change (divergences G).mkQ _ = _
  rw [mul_smul_comm, map_smul]
  rfl

def jetCoordinatesEquiv : Jet G ≃ YangMills.PerturbativeFlow.ExternalLeg G × Multiindex where
  toFun j := (j.field,j.derivative)
  invFun p := ⟨p.1,p.2⟩
  left_inv j := by cases j; rfl
  right_inv p := by cases p; rfl

/-- The induced evolutionary operation is the actual integrated Euler
Hamiltonian expression, before the elementary species sum is expanded. -/
theorem localClass_prolongation_euler
    (C : YangMills.PerturbativeFlow.ExternalLeg G → JetAlgebra G) (P : JetAlgebra G) :
    localClass (∑ᶠ j : Jet G, totalDerivatives j.derivative (C j.field) * leftPartialJet j P) =
      ∑ field : YangMills.PerturbativeFlow.ExternalLeg G,
        localClass (C field * leftEuler field P) := by
  let F : Jet G → JetAlgebra G := fun j => totalDerivatives j.derivative (C j.field) * leftPartialJet j P
  have hf : (Function.support F).Finite := jetSummands_finite (fun j => totalDerivatives j.derivative (C j.field)) P
  have hfp : (Function.support (fun p => F (jetCoordinatesEquiv.symm p))).Finite :=
    hf.preimage jetCoordinatesEquiv.symm.injective.injOn
  have hfc : (Function.support (fun p => localClass (F (jetCoordinatesEquiv.symm p)))).Finite := by
    apply hfp.subset
    intro p hp
    contrapose! hp
    have hz : F (jetCoordinatesEquiv.symm p) = 0 := not_not.mp hp
    simp [hz, localClass, Function.mem_support]
  change (divergences G).mkQ (∑ᶠ j, F j) = _
  trans ∑ᶠ j, localClass (F j)
  · exact (divergences G).mkQ.toAddMonoidHom.map_finsum hf
  rw [← finsum_comp_equiv jetCoordinatesEquiv.symm
    (f := fun j => localClass (F j)), finsum_curry _ hfc,
    finsum_eq_sum_of_fintype]
  apply Finset.sum_congr rfl
  intro field _
  exact (localClass_characteristicEuler (C field) P field).symm

theorem localClass_localST_euler (S P : JetAlgebra G) :
    localClass (localST S P) =
      ∑ field : YangMills.PerturbativeFlow.ExternalLeg G,
        localClass (stCharacteristic S field * leftEuler field P) := by
  rw [localST_finsum_jet]
  exact localClass_prolongation_euler (stCharacteristic S) P

/-- The same fixed evolutionary map agrees with the fixed BV antibracket
on integrated local functionals. No master-equation hypothesis is used. -/
theorem localClass_localST_eq_densityBracket (S P : JetAlgebra G) :
    localClass (localST S P) = localClass (densityBracket S P) := by
  have hn (A B : JetAlgebra G) :
      (divergences G).mkQ ((-A)*B) = -(divergences G).mkQ (A*B) := by
    calc
      _ = (divergences G).mkQ (-(A*B)) := congrArg (divergences G).mkQ (neg_mul A B)
      _ = _ := map_neg _ _
  rw [localClass_localST_euler, Fintype.sum_sum_type]
  change (∑ K, (divergences G).mkQ ((-(rightEuler (.inr K) S)) * leftEuler (.inl K) P)) +
    (∑ K, (divergences G).mkQ (rightEuler (.inl K) S * leftEuler (.inr K) P)) =
    (divergences G).mkQ (∑ K, (rightEuler (.inl K) S * leftEuler (.inr K) P -
      rightEuler (.inr K) S * leftEuler (.inl K) P))
  simp only [hn, map_sum, map_sub, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  abel

/-- Consequently the integrated Euler bracket with this fixed left argument
is independent of the right representative modulo actual divergences. -/
theorem densityBracket_right_representative (S P Q : JetAlgebra G)
    (same : localClass P = localClass Q) :
    localClass (densityBracket S P) = localClass (densityBracket S Q) := by
  rw [← localClass_localST_eq_densityBracket, ← localClass_localST_eq_densityBracket]
  exact localST_localClass_eq S P Q same

end YangMills.FullBV
