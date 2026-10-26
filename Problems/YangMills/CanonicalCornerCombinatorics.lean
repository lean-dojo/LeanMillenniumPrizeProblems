import Problems.YangMills.CompositeExtraction

-- Compatibility settings for the Lean 4.31 port of the reviewed source.
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
set_option maxHeartbeats 1800000
namespace YangMills.CanonicalUV
open scoped BigOperators

/-- Finite greedy selection. Every active index receives a candidate distinct
from every other assigned value; inactive values are kept literally fixed. -/
theorem fresh_assignment {n : ℕ} {B : Type*} [DecidableEq B]
    (S : Finset (Fin n)) (a : Fin n → B) (candidate : Fin n → Fin (n+1) → B)
    (injective : ∀ i, Function.Injective (candidate i)) :
    ∃ b : Fin n → B,
      (∀ i, i ∉ S → b i = a i) ∧
      (∀ i ∈ S, ∃ t, b i = candidate i t) ∧
      (∀ i ∈ S, ∀ j, j ≠ i → b i ≠ b j) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨a,by simp,by simp,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨b,hfixed,hcandidate,hdistinct⟩ := ih
    have hcard : (Finset.univ.image b).card <
        (Finset.univ.image (candidate i)).card := by
      rw [Finset.card_image_of_injective _ (injective i)]
      have hb := Finset.card_image_le (s := Finset.univ) (f := b)
      simp only [Finset.card_univ,Fintype.card_fin] at hb ⊢
      omega
    have hex : ∃ z, z ∈ Finset.univ.image (candidate i) ∧ z ∉ Finset.univ.image b := by
      by_contra! hh
      have hle := Finset.card_le_card hh
      omega
    obtain ⟨z,hz,hfresh⟩ := hex
    obtain ⟨t,_ht,rfl⟩ := Finset.mem_image.mp hz
    have hnew (j : Fin n) : candidate i t ≠ b j := by
      intro hj
      apply hfresh
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj.symm⟩
    refine ⟨Function.update b i (candidate i t),?_,?_,?_⟩
    · intro j hj
      have hji : j ≠ i := by intro h; subst j; exact hj (Finset.mem_insert_self _ _)
      rw [Function.update_of_ne hji]
      exact hfixed j (fun h => hj (Finset.mem_insert_of_mem h))
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ⟨t,Function.update_self _ _ _⟩
      · have hji : j ≠ i := by intro h; subst j; exact hi hj
        rw [Function.update_of_ne hji]
        exact hcandidate j hj
    · intro j hj k hkj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa only [Function.update_self,Function.update_of_ne hkj] using hnew k
      · have hji : j ≠ i := by intro h; subst j; exact hi hj
        rw [Function.update_of_ne hji]
        by_cases hki : k = i
        · subst k
          simpa only [Function.update_self] using (hnew j).symm
        · rw [Function.update_of_ne hki]
          exact hdistinct j hj k hkj

/-- Which full momentum slots have at least one remainder coordinate. -/
def activeLegs {n : ℕ} (S : Finset (Fin n × Fin 4)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∃ mu : Fin 4, (i,mu) ∈ S)

@[simp] theorem mem_activeLegs {n : ℕ} (S : Finset (Fin n × Fin 4)) (i : Fin n) :
    i ∈ activeLegs S ↔ ∃ mu : Fin 4, (i,mu) ∈ S := by
  simp [activeLegs]

/-- Corner derivative in an anchored rectangular Taylor term. -/
def corner {n : ℕ} (S : Finset (Fin n × Fin 4)) (L : ℕ)
    (a : Fin n → Fin 4 → ℕ) (i : Fin n) (mu : Fin 4) : ℕ :=
  if (i,mu) ∈ S then L else a i mu

/-- An anchored remainder either has a swap-fixed repeated odd jet, or its
corner differential is divisible by an admissible differential above N.
R is the actual same-odd-species relation when this lemma is applied. -/
theorem corner_dichotomy {n : ℕ} (N : ℕ) (S : Finset (Fin n × Fin 4))
    (nonempty : S.Nonempty) (a : Fin n → Fin 4 → ℕ)
    (R : Fin n → Fin n → Prop) :
    (∃ i j, i ≠ j ∧ R i j ∧ i ∉ activeLegs S ∧ j ∉ activeLegs S ∧ a i = a j) ∨
    ∃ b : Fin n → Fin 4 → ℕ,
      (∀ i mu, b i mu ≤ corner S (N+n+1) a i mu) ∧
      N < ∑ i : Fin n, ∑ mu : Fin 4, b i mu ∧
      (∀ i j, i ≠ j → R i j → b i ≠ b j) := by
  classical
  by_cases collision : ∃ i j, i ≠ j ∧ R i j ∧ i ∉ activeLegs S ∧ j ∉ activeLegs S ∧ a i = a j
  · exact Or.inl collision
  · right
    let pivot (i : Fin n) : Fin 4 :=
      if hi : i ∈ activeLegs S then Classical.choose ((mem_activeLegs S i).mp hi) else 0
    have hp (i : Fin n) (hi : i ∈ activeLegs S) : (i,pivot i) ∈ S := by
      simp only [pivot,dif_pos hi]
      exact Classical.choose_spec ((mem_activeLegs S i).mp hi)
    let candidate (i : Fin n) (t : Fin (n+1)) (mu : Fin 4) : ℕ :=
      if mu = pivot i then N+1+t.val else if (i,mu) ∈ S then 0 else a i mu
    have hc (i : Fin n) : Function.Injective (candidate i) := by
      intro t r htr
      have hh := congrFun htr (pivot i)
      simp only [candidate,if_pos rfl] at hh
      apply Fin.ext
      omega
    obtain ⟨b,hfixed,hcandidate,hdistinct⟩ := fresh_assignment (activeLegs S) a candidate hc
    refine ⟨b,?_,?_,?_⟩
    · intro i mu
      by_cases hi : i ∈ activeLegs S
      · obtain ⟨t,ht⟩ := hcandidate i hi
        rw [ht]
        by_cases heq : mu = pivot i
        · subst mu
          simp only [candidate,if_pos rfl,corner,if_pos (hp i hi)]
          have := t.isLt
          omega
        · simp only [candidate,if_neg heq,corner]
          split_ifs <;> omega
      · rw [hfixed i hi]
        have hmu : (i,mu) ∉ S := by
          intro hm
          exact hi ((mem_activeLegs S i).mpr ⟨mu,hm⟩)
        simp only [corner,if_neg hmu]
        exact le_rfl
    · obtain ⟨⟨i,mu⟩,hm⟩ := nonempty
      have hi : i ∈ activeLegs S := (mem_activeLegs S i).mpr ⟨mu,hm⟩
      obtain ⟨t,ht⟩ := hcandidate i hi
      have hb : b i (pivot i) = N+1+t.val := by simp only [ht,candidate,if_pos rfl]
      have h1 : b i (pivot i) ≤ ∑ mu : Fin 4, b i mu :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      have h2 : (∑ mu : Fin 4, b i mu) ≤ ∑ j : Fin n, ∑ mu : Fin 4, b j mu :=
        Finset.single_le_sum (f := fun j : Fin n => ∑ mu : Fin 4, b j mu)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    · intro i j hij hr heq
      by_cases hi : i ∈ activeLegs S
      · exact hdistinct i hi j hij.symm heq
      · by_cases hj : j ∈ activeLegs S
        · exact hdistinct j hj i hij heq.symm
        · apply collision
          exact ⟨i,j,hij,hr,hi,hj,(hfixed i hi).symm.trans (heq.trans (hfixed j hj))⟩

end YangMills.CanonicalUV
