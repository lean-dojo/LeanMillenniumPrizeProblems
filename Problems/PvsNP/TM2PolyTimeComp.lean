import Mathlib.Computability.TMComputable
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Max

namespace Millennium

open Computability
open Turing

namespace Turing

open TM2

/-!
This file provides an axiom-free proof of closure of `TM2ComputableInPolyTime` under composition.

Mathlib currently ships `Turing.TM2ComputableInPolyTime.comp` as a `proof_wanted` (axiom).  We do
not use it; instead we construct an explicit composed machine and prove its correctness/time.
-/

private instance (tm : FinTM2) : Fintype tm.K :=
  tm.kFin

private instance (tm : FinTM2) : Fintype tm.Λ :=
  tm.ΛFin

private instance (tm : FinTM2) : Fintype tm.σ :=
  tm.σFin

private instance (tm : FinTM2) : Fintype (tm.Γ tm.k₀) :=
  tm.Γk₀Fin

private abbrev CompK (tm₁ tm₂ : FinTM2) : Type :=
  Sum (Sum tm₁.K tm₂.K) Unit

private abbrev CompLabel (tm₁ tm₂ : FinTM2) : Type :=
  Sum (Sum tm₁.Λ tm₂.Λ) Bool

private abbrev Compσ (tm₁ tm₂ : FinTM2) (Γβ : Type) : Type :=
  tm₁.σ × tm₂.σ × Option Γβ

private def compΓ (tm₁ tm₂ : FinTM2) (Γβ : Type) : CompK tm₁ tm₂ → Type
  | Sum.inl (Sum.inl k) => tm₁.Γ k
  | Sum.inl (Sum.inr k) => tm₂.Γ k
  | Sum.inr () => Γβ

private abbrev inlK {tm₁ tm₂ : FinTM2} : tm₁.K → CompK tm₁ tm₂ :=
  fun k => Sum.inl (Sum.inl k)

private abbrev inrK {tm₁ tm₂ : FinTM2} : tm₂.K → CompK tm₁ tm₂ :=
  fun k => Sum.inl (Sum.inr k)

private abbrev bufK {tm₁ tm₂ : FinTM2} : CompK tm₁ tm₂ :=
  Sum.inr ()

private abbrev inlL {tm₁ tm₂ : FinTM2} : tm₁.Λ → CompLabel tm₁ tm₂ :=
  fun l => Sum.inl (Sum.inl l)

private abbrev inrL {tm₁ tm₂ : FinTM2} : tm₂.Λ → CompLabel tm₁ tm₂ :=
  fun l => Sum.inl (Sum.inr l)

private abbrev copy1L {tm₁ tm₂ : FinTM2} : CompLabel tm₁ tm₂ :=
  Sum.inr false

private abbrev copy2L {tm₁ tm₂ : FinTM2} : CompLabel tm₁ tm₂ :=
  Sum.inr true

private def liftStmtLeft {tm₁ tm₂ : FinTM2} {Γβ : Type} (haltTarget : CompLabel tm₁ tm₂) :
    TM2.Stmt tm₁.Γ tm₁.Λ tm₁.σ → TM2.Stmt (compΓ tm₁ tm₂ Γβ) (CompLabel tm₁ tm₂) (Compσ tm₁ tm₂ Γβ)
  | TM2.Stmt.push k f q =>
      TM2.Stmt.push (inlK (tm₁ := tm₁) (tm₂ := tm₂) k) (fun s => f s.1)
        (liftStmtLeft (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) haltTarget q)
  | TM2.Stmt.peek k f q =>
      TM2.Stmt.peek (inlK (tm₁ := tm₁) (tm₂ := tm₂) k)
        (fun s a => (f s.1 a, s.2.1, s.2.2))
        (liftStmtLeft (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) haltTarget q)
  | TM2.Stmt.pop k f q =>
      TM2.Stmt.pop (inlK (tm₁ := tm₁) (tm₂ := tm₂) k)
        (fun s a => (f s.1 a, s.2.1, s.2.2))
        (liftStmtLeft (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) haltTarget q)
  | TM2.Stmt.load a q =>
      TM2.Stmt.load (fun s => (a s.1, s.2.1, s.2.2))
        (liftStmtLeft (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) haltTarget q)
  | TM2.Stmt.branch p q₁ q₂ =>
      TM2.Stmt.branch (fun s => p s.1)
        (liftStmtLeft (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) haltTarget q₁)
        (liftStmtLeft (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) haltTarget q₂)
  | TM2.Stmt.goto j =>
      TM2.Stmt.goto (fun s => inlL (tm₁ := tm₁) (tm₂ := tm₂) (j s.1))
  | TM2.Stmt.halt =>
      TM2.Stmt.goto (fun _ => haltTarget)

private def liftStmtRight {tm₁ tm₂ : FinTM2} {Γβ : Type} :
    TM2.Stmt tm₂.Γ tm₂.Λ tm₂.σ → TM2.Stmt (compΓ tm₁ tm₂ Γβ) (CompLabel tm₁ tm₂) (Compσ tm₁ tm₂ Γβ)
  | TM2.Stmt.push k f q =>
      TM2.Stmt.push (inrK (tm₁ := tm₁) (tm₂ := tm₂) k) (fun s => f s.2.1)
        (liftStmtRight (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) q)
  | TM2.Stmt.peek k f q =>
      TM2.Stmt.peek (inrK (tm₁ := tm₁) (tm₂ := tm₂) k)
        (fun s a => (s.1, f s.2.1 a, s.2.2))
        (liftStmtRight (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) q)
  | TM2.Stmt.pop k f q =>
      TM2.Stmt.pop (inrK (tm₁ := tm₁) (tm₂ := tm₂) k)
        (fun s a => (s.1, f s.2.1 a, s.2.2))
        (liftStmtRight (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) q)
  | TM2.Stmt.load a q =>
      TM2.Stmt.load (fun s => (s.1, a s.2.1, s.2.2))
        (liftStmtRight (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) q)
  | TM2.Stmt.branch p q₁ q₂ =>
      TM2.Stmt.branch (fun s => p s.2.1)
        (liftStmtRight (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) q₁)
        (liftStmtRight (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) q₂)
  | TM2.Stmt.goto j =>
      TM2.Stmt.goto (fun s => inrL (tm₁ := tm₁) (tm₂ := tm₂) (j s.2.1))
  | TM2.Stmt.halt =>
      TM2.Stmt.halt

private def copy1Stmt {α β γ : Type} {eα : FinEncoding α} {eβ : FinEncoding β} {eγ : FinEncoding γ}
    {f : α → β} {g : β → γ} (h₁ : TM2ComputableInPolyTime eα eβ f) (h₂ : TM2ComputableInPolyTime eβ eγ g)
    (β0 : eβ.Γ) :
    TM2.Stmt (compΓ h₁.tm h₂.tm eβ.Γ) (CompLabel h₁.tm h₂.tm) (Compσ h₁.tm h₂.tm eβ.Γ) :=
  TM2.Stmt.pop (inlK (tm₁ := h₁.tm) (tm₂ := h₂.tm) h₁.tm.k₁)
    (fun s a => (s.1, s.2.1, a.map h₁.outputAlphabet))
    (TM2.Stmt.branch (fun s => (s.2.2).isSome)
      (TM2.Stmt.push (bufK (tm₁ := h₁.tm) (tm₂ := h₂.tm)) (fun s => (s.2.2).getD β0)
        (TM2.Stmt.goto (fun _ => copy1L (tm₁ := h₁.tm) (tm₂ := h₂.tm))))
      (TM2.Stmt.goto (fun _ => copy2L (tm₁ := h₁.tm) (tm₂ := h₂.tm))))

private def copy2Stmt {α β γ : Type} {eα : FinEncoding α} {eβ : FinEncoding β} {eγ : FinEncoding γ}
    {f : α → β} {g : β → γ} (h₁ : TM2ComputableInPolyTime eα eβ f) (h₂ : TM2ComputableInPolyTime eβ eγ g)
    (β0 : eβ.Γ) :
    TM2.Stmt (compΓ h₁.tm h₂.tm eβ.Γ) (CompLabel h₁.tm h₂.tm) (Compσ h₁.tm h₂.tm eβ.Γ) :=
  TM2.Stmt.pop (bufK (tm₁ := h₁.tm) (tm₂ := h₂.tm))
    (fun s a => (s.1, s.2.1, a))
    (TM2.Stmt.branch (fun s => (s.2.2).isSome)
      (TM2.Stmt.push (inrK (tm₁ := h₁.tm) (tm₂ := h₂.tm) h₂.tm.k₀)
        (fun s => h₂.inputAlphabet.invFun ((s.2.2).getD β0))
        (TM2.Stmt.goto (fun _ => copy2L (tm₁ := h₁.tm) (tm₂ := h₂.tm))))
      (TM2.Stmt.goto (fun _ => inrL (tm₁ := h₁.tm) (tm₂ := h₂.tm) h₂.tm.main)))

private noncomputable def compFinTM2Core {α β γ : Type} {eα : FinEncoding α} {eβ : FinEncoding β}
    {eγ : FinEncoding γ} {f : α → β} {g : β → γ} (h₁ : TM2ComputableInPolyTime eα eβ f)
    (h₂ : TM2ComputableInPolyTime eβ eγ g) (haltTarget : CompLabel h₁.tm h₂.tm)
    (mCopy :
      Bool →
        TM2.Stmt (compΓ h₁.tm h₂.tm eβ.Γ) (CompLabel h₁.tm h₂.tm) (Compσ h₁.tm h₂.tm eβ.Γ)) :
    FinTM2 := by
  classical
  refine
    { K := CompK h₁.tm h₂.tm
      k₀ := inlK (tm₁ := h₁.tm) (tm₂ := h₂.tm) h₁.tm.k₀
      k₁ := inrK (tm₁ := h₁.tm) (tm₂ := h₂.tm) h₂.tm.k₁
      Γ := compΓ h₁.tm h₂.tm eβ.Γ
      Λ := CompLabel h₁.tm h₂.tm
      main := inlL (tm₁ := h₁.tm) (tm₂ := h₂.tm) h₁.tm.main
      σ := Compσ h₁.tm h₂.tm eβ.Γ
      initialState := (h₁.tm.initialState, h₂.tm.initialState, none)
      Γk₀Fin := by
        simpa [compΓ, inlK] using (h₁.tm.Γk₀Fin)
      m := fun
        | Sum.inl (Sum.inl l) =>
            liftStmtLeft (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) haltTarget (h₁.tm.m l)
        | Sum.inl (Sum.inr l) =>
            liftStmtRight (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) (h₂.tm.m l)
        | Sum.inr b => mCopy b }

private noncomputable def compFinTM2_nonempty {α β γ : Type} {eα : FinEncoding α} {eβ : FinEncoding β}
    {eγ : FinEncoding γ} {f : α → β} {g : β → γ} (h₁ : TM2ComputableInPolyTime eα eβ f)
    (h₂ : TM2ComputableInPolyTime eβ eγ g) (β0 : eβ.Γ) : FinTM2 :=
  compFinTM2Core h₁ h₂ (haltTarget := copy1L (tm₁ := h₁.tm) (tm₂ := h₂.tm))
    (mCopy := fun
      | false => copy1Stmt h₁ h₂ β0
      | true => copy2Stmt h₁ h₂ β0)

private noncomputable def compFinTM2_empty {α β γ : Type} {eα : FinEncoding α} {eβ : FinEncoding β}
    {eγ : FinEncoding γ} {f : α → β} {g : β → γ} (h₁ : TM2ComputableInPolyTime eα eβ f)
    (h₂ : TM2ComputableInPolyTime eβ eγ g) : FinTM2 :=
  compFinTM2Core h₁ h₂ (haltTarget := inrL (tm₁ := h₁.tm) (tm₂ := h₂.tm) h₂.tm.main)
    (mCopy := fun _ => TM2.Stmt.goto (fun _ => inrL (tm₁ := h₁.tm) (tm₂ := h₂.tm) h₂.tm.main))

private noncomputable def compFinTM2 {α β γ : Type} {eα : FinEncoding α} {eβ : FinEncoding β}
    {eγ : FinEncoding γ} {f : α → β} {g : β → γ} (h₁ : TM2ComputableInPolyTime eα eβ f)
    (h₂ : TM2ComputableInPolyTime eβ eγ g) : FinTM2 := by
  classical
  by_cases hβ : Nonempty eβ.Γ
  · exact compFinTM2_nonempty h₁ h₂ (Classical.choice hβ)
  · exact compFinTM2_empty h₁ h₂

private def compStk {tm₁ tm₂ : FinTM2} {Γβ : Type}
    (S₁ : ∀ k : tm₁.K, List (tm₁.Γ k)) (S₂ : ∀ k : tm₂.K, List (tm₂.Γ k)) (B : List Γβ) :
    ∀ k : CompK tm₁ tm₂, List (compΓ tm₁ tm₂ Γβ k)
  | Sum.inl (Sum.inl k) => S₁ k
  | Sum.inl (Sum.inr k) => S₂ k
  | Sum.inr () => B

private theorem compStk_update_inl {tm₁ tm₂ : FinTM2} {Γβ : Type}
    (S₁ : ∀ k : tm₁.K, List (tm₁.Γ k)) (S₂ : ∀ k : tm₂.K, List (tm₂.Γ k)) (B : List Γβ)
    (k : tm₁.K) (v : List (tm₁.Γ k)) :
    Function.update (compStk (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) S₁ S₂ B)
        (inlK (tm₁ := tm₁) (tm₂ := tm₂) k) v
      =
      compStk (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) (Function.update S₁ k v) S₂ B := by
  classical
  funext x
  cases x with
  | inl x =>
      cases x with
      | inl x =>
          by_cases hx : x = k <;>
            simp [compStk, inlK, Function.update_apply, hx]
      | inr x =>
          simp [compStk, inlK, Function.update_apply]
  | inr u =>
      cases u
      simp [compStk, inlK, Function.update_apply]

private theorem compStk_update_inr {tm₁ tm₂ : FinTM2} {Γβ : Type}
    (S₁ : ∀ k : tm₁.K, List (tm₁.Γ k)) (S₂ : ∀ k : tm₂.K, List (tm₂.Γ k)) (B : List Γβ)
    (k : tm₂.K) (v : List (tm₂.Γ k)) :
    Function.update (compStk (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) S₁ S₂ B)
        (inrK (tm₁ := tm₁) (tm₂ := tm₂) k) v
      =
      compStk (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) S₁ (Function.update S₂ k v) B := by
  classical
  funext x
  cases x with
  | inl x =>
      cases x with
      | inl x =>
          simp [compStk, inrK, Function.update_apply]
      | inr x =>
          by_cases hx : x = k <;>
            simp [compStk, inrK, Function.update_apply, hx]
  | inr u =>
      cases u
      simp [compStk, inrK, Function.update_apply]

private theorem compStk_update_buf {tm₁ tm₂ : FinTM2} {Γβ : Type}
    (S₁ : ∀ k : tm₁.K, List (tm₁.Γ k)) (S₂ : ∀ k : tm₂.K, List (tm₂.Γ k)) (B : List Γβ)
    (v : List Γβ) :
    Function.update (compStk (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) S₁ S₂ B) (bufK (tm₁ := tm₁) (tm₂ := tm₂))
        v
      =
      compStk (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) S₁ S₂ v := by
  classical
  funext x
  cases x with
  | inl x =>
      cases x with
      | inl x =>
          simp [compStk, bufK, Function.update_apply]
      | inr x =>
          simp [compStk, bufK, Function.update_apply]
  | inr u =>
      cases u
      simp [compStk, bufK, Function.update_apply]

private theorem stepAux_liftStmtLeft {tm₁ tm₂ : FinTM2} {Γβ : Type} (haltTarget : CompLabel tm₁ tm₂)
    (q : TM2.Stmt tm₁.Γ tm₁.Λ tm₁.σ) (s₁ : tm₁.σ) (s₂ : tm₂.σ) (tmp : Option Γβ)
    (S₁ : ∀ k : tm₁.K, List (tm₁.Γ k)) (S₂ : ∀ k : tm₂.K, List (tm₂.Γ k)) (B : List Γβ) :
    stepAux (liftStmtLeft (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) haltTarget q) (s₁, s₂, tmp)
        (compStk (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) S₁ S₂ B)
      =
      let cfg₁ := stepAux q s₁ S₁
      { l :=
          match cfg₁.l with
          | some l => some (inlL (tm₁ := tm₁) (tm₂ := tm₂) l)
          | none => some haltTarget
        var := (cfg₁.var, s₂, tmp)
        stk := compStk (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) cfg₁.stk S₂ B } := by
  classical
  induction q generalizing s₁ S₁ S₂ B with
  | push k f q ih =>
      simp [liftStmtLeft, stepAux, ih, compStk_update_inl, compStk, Function.update_apply]
  | peek k f q ih =>
      simp [liftStmtLeft, stepAux, ih, compStk, Function.update_apply]
  | pop k f q ih =>
      simp [liftStmtLeft, stepAux, ih, compStk_update_inl, compStk, Function.update_apply]
  | load a q ih =>
      simp [liftStmtLeft, stepAux, ih, compStk]
  | branch p q₁ q₂ ih₁ ih₂ =>
      by_cases h : p s₁ <;> simp [liftStmtLeft, stepAux, h, ih₁, ih₂, compStk]
  | goto j =>
      simp [liftStmtLeft, stepAux, compStk]
  | halt =>
      simp [liftStmtLeft, stepAux, compStk]

private theorem stepAux_liftStmtRight {tm₁ tm₂ : FinTM2} {Γβ : Type}
    (q : TM2.Stmt tm₂.Γ tm₂.Λ tm₂.σ) (s₁ : tm₁.σ) (s₂ : tm₂.σ) (tmp : Option Γβ)
    (S₁ : ∀ k : tm₁.K, List (tm₁.Γ k)) (S₂ : ∀ k : tm₂.K, List (tm₂.Γ k)) (B : List Γβ) :
    stepAux (liftStmtRight (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) q) (s₁, s₂, tmp)
        (compStk (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) S₁ S₂ B)
      =
      let cfg₂ := stepAux q s₂ S₂
      { l :=
          match cfg₂.l with
          | some l => some (inrL (tm₁ := tm₁) (tm₂ := tm₂) l)
          | none => none
        var := (s₁, cfg₂.var, tmp)
        stk := compStk (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) S₁ cfg₂.stk B } := by
  classical
  induction q generalizing s₂ S₁ S₂ B with
  | push k f q ih =>
      simp [liftStmtRight, stepAux, ih, compStk_update_inr, compStk, Function.update_apply]
  | peek k f q ih =>
      simp [liftStmtRight, stepAux, ih, compStk, Function.update_apply]
  | pop k f q ih =>
      simp [liftStmtRight, stepAux, ih, compStk_update_inr, compStk, Function.update_apply]
  | load a q ih =>
      simp [liftStmtRight, stepAux, ih, compStk]
  | branch p q₁ q₂ ih₁ ih₂ =>
      by_cases h : p s₂ <;> simp [liftStmtRight, stepAux, h, ih₁, ih₂, compStk]
  | goto j =>
      simp [liftStmtRight, stepAux, compStk]
  | halt =>
      simp [liftStmtRight, stepAux, compStk]

private def embedLeftCfg {tm₁ tm₂ : FinTM2} {Γβ : Type} (haltTarget : CompLabel tm₁ tm₂)
    (s₂ : tm₂.σ) (tmp : Option Γβ) (S₂ : ∀ k : tm₂.K, List (tm₂.Γ k)) (B : List Γβ) (cfg₁ : tm₁.Cfg) :
    TM2.Cfg (compΓ tm₁ tm₂ Γβ) (CompLabel tm₁ tm₂) (Compσ tm₁ tm₂ Γβ) where
  l :=
    match cfg₁.l with
    | some l => some (inlL (tm₁ := tm₁) (tm₂ := tm₂) l)
    | none => some haltTarget
  var := (cfg₁.var, s₂, tmp)
  stk := compStk (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) cfg₁.stk S₂ B

private def embedRightCfg {tm₁ tm₂ : FinTM2} {Γβ : Type} (s₁ : tm₁.σ) (tmp : Option Γβ)
    (S₁ : ∀ k : tm₁.K, List (tm₁.Γ k)) (B : List Γβ) (cfg₂ : tm₂.Cfg) :
    TM2.Cfg (compΓ tm₁ tm₂ Γβ) (CompLabel tm₁ tm₂) (Compσ tm₁ tm₂ Γβ) where
  l :=
    match cfg₂.l with
    | some l => some (inrL (tm₁ := tm₁) (tm₂ := tm₂) l)
    | none => none
  var := (s₁, cfg₂.var, tmp)
  stk := compStk (tm₁ := tm₁) (tm₂ := tm₂) (Γβ := Γβ) S₁ cfg₂.stk B

private theorem Polynomial.eval_monotone_nat (p : Polynomial ℕ) : Monotone (fun n => p.eval n) := by
  intro m n hmn
  revert m n hmn
  refine Polynomial.induction_on' (p := p)
    (motive := fun p => ∀ m n : ℕ, m ≤ n → p.eval m ≤ p.eval n) ?_ ?_
  · intro p q hp hq m n hmn
    simpa [Polynomial.eval_add] using add_le_add (hp m n hmn) (hq m n hmn)
  · intro d a m n hmn
    simpa [Polynomial.eval_monomial] using Nat.mul_le_mul_left a (Nat.pow_le_pow_left hmn d)

private def Stmt.pushBound {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} (k : K) :
    TM2.Stmt Γ Λ σ → ℕ
  | TM2.Stmt.push k' _ q => (if k' = k then 1 else 0) + pushBound k q
  | TM2.Stmt.peek _ _ q => pushBound k q
  | TM2.Stmt.pop _ _ q => pushBound k q
  | TM2.Stmt.load _ q => pushBound k q
  | TM2.Stmt.branch _ q₁ q₂ => max (pushBound k q₁) (pushBound k q₂)
  | TM2.Stmt.goto _ => 0
  | TM2.Stmt.halt => 0

private theorem stepAux_stk_length_le_add_pushBound {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (k : K) (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k : K, List (Γ k)) :
    ((stepAux q v S).stk k).length ≤ (S k).length + Stmt.pushBound (Γ := Γ) k q := by
  classical
  induction q generalizing v S with
  | push k' f q ih =>
      by_cases hk : k' = k
      · subst k'
        have ih' := ih (v := v) (S := Function.update S k (f v :: S k))
        simpa [Stmt.pushBound, stepAux, Function.update_apply, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using ih'
      ·
        have hk' : k ≠ k' := by
          intro h; exact hk h.symm
        have hupdate : (Function.update S k' (f v :: S k')) k = S k := by
          simp [Function.update_apply, hk']
        have ih' := ih (v := v) (S := Function.update S k' (f v :: S k'))
        -- pushing on a different stack leaves `k` unchanged
        simpa [Stmt.pushBound, stepAux, Function.update_apply, hk, hupdate] using ih'
  | peek k' f q ih =>
      simpa [Stmt.pushBound, stepAux, ih, Function.update_apply]
  | pop k' f q ih =>
      by_cases hk : k' = k
      · subst k'
        -- popping on `k` can only decrease its length
        have htail : ((S k).tail).length ≤ (S k).length := by
          simpa using List.length_tail_le (S k)
        have ih' := ih (v := f v (S k).head?) (S := Function.update S k (S k).tail)
        have hstep : ((stepAux (TM2.Stmt.pop k f q) v S).stk k).length ≤
            ((S k).tail).length + Stmt.pushBound (Γ := Γ) k q := by
          simpa [Stmt.pushBound, stepAux, Function.update_apply] using ih'
        have htail' :
            ((S k).tail).length + Stmt.pushBound (Γ := Γ) k q ≤ (S k).length + Stmt.pushBound (Γ := Γ) k q :=
          Nat.add_le_add_right htail _
        exact le_trans hstep (by simpa [Stmt.pushBound] using htail')
      ·
        have hk' : k ≠ k' := by
          intro h; exact hk h.symm
        have hupdate : (Function.update S k' (S k').tail) k = S k := by
          simp [Function.update_apply, hk']
        have ih' := ih (v := f v (S k').head?) (S := Function.update S k' (S k').tail)
        simpa [Stmt.pushBound, stepAux, Function.update_apply, hk, hupdate] using ih'
  | load a q ih =>
      simpa [Stmt.pushBound, stepAux, ih]
  | branch p q₁ q₂ ih₁ ih₂ =>
      by_cases h : p v
      ·
        have h₁ : ((stepAux q₁ v S).stk k).length ≤ (S k).length + Stmt.pushBound (Γ := Γ) k q₁ :=
          ih₁ (v := v) (S := S)
        have hpush : Stmt.pushBound (Γ := Γ) k q₁ ≤ max (Stmt.pushBound (Γ := Γ) k q₁) (Stmt.pushBound (Γ := Γ) k q₂) :=
          le_max_left _ _
        have : ((stepAux (TM2.Stmt.branch p q₁ q₂) v S).stk k).length ≤
            (S k).length + Stmt.pushBound (Γ := Γ) k q₁ := by
          simpa [Stmt.pushBound, stepAux, h] using h₁
        exact le_trans this (by simpa [Stmt.pushBound] using add_le_add_left hpush _)
      ·
        have h₂ : ((stepAux q₂ v S).stk k).length ≤ (S k).length + Stmt.pushBound (Γ := Γ) k q₂ :=
          ih₂ (v := v) (S := S)
        have hpush : Stmt.pushBound (Γ := Γ) k q₂ ≤ max (Stmt.pushBound (Γ := Γ) k q₁) (Stmt.pushBound (Γ := Γ) k q₂) :=
          le_max_right _ _
        have : ((stepAux (TM2.Stmt.branch p q₁ q₂) v S).stk k).length ≤
            (S k).length + Stmt.pushBound (Γ := Γ) k q₂ := by
          simpa [Stmt.pushBound, stepAux, h] using h₂
        exact le_trans this (by simpa [Stmt.pushBound] using add_le_add_left hpush _)
  | goto j =>
      simp [Stmt.pushBound, stepAux]
  | halt =>
      simp [Stmt.pushBound, stepAux]

private def maxPushBound (tm : FinTM2) (k : tm.K) : ℕ := by
  classical
  let s : Finset ℕ := (Finset.univ : Finset tm.Λ).image (fun l => Stmt.pushBound (Γ := tm.Γ) k (tm.m l))
  exact s.max' (by
    refine ⟨Stmt.pushBound (Γ := tm.Γ) k (tm.m tm.main), ?_⟩
    refine (Finset.mem_image).2 ?_
    exact ⟨tm.main, by simp, rfl⟩)

private theorem pushBound_le_maxPushBound (tm : FinTM2) (k : tm.K) (l : tm.Λ) :
    Stmt.pushBound (Γ := tm.Γ) k (tm.m l) ≤ maxPushBound tm k := by
  classical
  -- unfold `maxPushBound` enough to use `Finset.le_max'`
  unfold maxPushBound
  -- `simp` turns the `let` into an `image`
  simp only
  have hl : Stmt.pushBound (Γ := tm.Γ) k (tm.m l) ∈
      (Finset.univ : Finset tm.Λ).image (fun l => Stmt.pushBound (Γ := tm.Γ) k (tm.m l)) := by
    refine (Finset.mem_image).2 ?_
    exact ⟨l, by simp, rfl⟩
  exact Finset.le_max' _ _ hl

private theorem step_stk_length_le_add_maxPushBound (tm : FinTM2) (k : tm.K) {cfg cfg' : tm.Cfg} :
    tm.step cfg = some cfg' → (cfg'.stk k).length ≤ (cfg.stk k).length + maxPushBound tm k := by
  classical
  intro hStep
  rcases cfg with ⟨lbl, v, S⟩
  cases lbl with
  | none =>
      -- `step` can't return `some` from a halting label
      simp [FinTM2.step, TM2.step] at hStep
  | some l =>
      have hcfg' : cfg' = stepAux (tm.m l) v S := by
        simpa [FinTM2.step, TM2.step] using hStep.symm
      subst hcfg'
      have hlen :
          ((stepAux (tm.m l) v S).stk k).length ≤ (S k).length + Stmt.pushBound (Γ := tm.Γ) k (tm.m l) :=
        stepAux_stk_length_le_add_pushBound (Γ := tm.Γ) k (tm.m l) v S
      have hbound : Stmt.pushBound (Γ := tm.Γ) k (tm.m l) ≤ maxPushBound tm k :=
        pushBound_le_maxPushBound tm k l
      exact le_trans hlen (by simpa using Nat.add_le_add_left hbound (S k).length)

private theorem stk_length_le_of_iterate (tm : FinTM2) (k : tm.K) :
    ∀ (t : ℕ) {cfg₀ cfg : tm.Cfg},
      (flip bind tm.step)^[t] (some cfg₀) = some cfg →
        (cfg.stk k).length ≤ (cfg₀.stk k).length + t * maxPushBound tm k := by
  classical
  intro t
  induction t with
  | zero =>
      intro cfg₀ cfg h
      simp at h
      cases h
      simp
  | succ t ih =>
      intro cfg₀ cfg h
      -- unfold one iteration step: `x_{t+1} = x_t >>= tm.step`
      have hSucc : (flip bind tm.step) ((flip bind tm.step)^[t] (some cfg₀)) = some cfg := by
        simpa [Function.iterate_succ_apply'] using h
      cases hMid : ((flip bind tm.step)^[t] (some cfg₀)) with
      | none =>
          -- `none >>= tm.step = none`, contradiction
          rw [hMid] at hSucc
          simp [flip, Option.bind] at hSucc
      | some cfgMid =>
          rw [hMid] at hSucc
          have hStepMid : tm.step cfgMid = some cfg := by
            simpa [flip, Option.bind] using hSucc
          have hMidLen :
              (cfgMid.stk k).length ≤ (cfg₀.stk k).length + t * maxPushBound tm k :=
            ih (cfg₀ := cfg₀) (cfg := cfgMid) hMid
          have hStepLen :
              (cfg.stk k).length ≤ (cfgMid.stk k).length + maxPushBound tm k :=
            step_stk_length_le_add_maxPushBound tm k hStepMid
          have hMidLen' :
              (cfgMid.stk k).length + maxPushBound tm k ≤ (cfg₀.stk k).length + t * maxPushBound tm k + maxPushBound tm k :=
            Nat.add_le_add_right hMidLen _
          have hTotal :
              (cfg.stk k).length ≤ (cfg₀.stk k).length + t * maxPushBound tm k + maxPushBound tm k :=
            le_trans hStepLen hMidLen'
          -- rewrite `t * C + C` as `(t+1) * C`
          simpa [Nat.add_assoc, Nat.succ_mul] using hTotal

private def evalsToInTime_mono {σ : Type*} {f : σ → Option σ} {a : σ} {b : Option σ} {m₁ m₂ : ℕ}
    (h : EvalsToInTime f a b m₁) (hm : m₁ ≤ m₂) : EvalsToInTime f a b m₂ :=
  { toEvalsTo := h.toEvalsTo
    steps_le_m := le_trans h.steps_le_m hm }

private def evalsToInTime_ofStep {σ : Type*} (f : σ → Option σ) (a b : σ) (h : f a = some b) :
    EvalsToInTime f a (some b) 1 := by
  refine { steps := 1, evals_in_steps := ?_, steps_le_m := by simp }
  simpa [Function.iterate_succ_apply', flip, Option.bind, h]

private theorem List.map_equiv_apply_inv {α β : Type} (e : α ≃ β) (l : List β) :
    List.map e (List.map e.invFun l) = l := by
  induction l with
  | nil => simp
  | cons a t ih => simpa [ih]

private theorem initList_stk_eq_update (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    (initList tm s).stk = Function.update (fun k => ([] : List (tm.Γ k))) tm.k₀ s := by
  classical
  funext k
  by_cases hk : k = tm.k₀
  · subst hk
    simp [initList, Function.update]
  · simp [initList, Function.update, hk]

private theorem initList_l (tm : FinTM2) (s : List (tm.Γ tm.k₀)) : (initList tm s).l = some tm.main := rfl

private theorem initList_var (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    (initList tm s).var = tm.initialState := rfl

private theorem haltList_stk_eq_update (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    (haltList tm s).stk = Function.update (fun k => ([] : List (tm.Γ k))) tm.k₁ s := by
  classical
  funext k
  by_cases hk : k = tm.k₁
  · subst hk
    simp [haltList, Function.update]
  · simp [haltList, Function.update, hk]

private theorem haltList_l (tm : FinTM2) (s : List (tm.Γ tm.k₁)) : (haltList tm s).l = none := rfl

private theorem haltList_var (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    (haltList tm s).var = tm.initialState := rfl

private theorem cfg_eq_of_fields {K : Type} {Γ : K → Type} {Λ σ : Type} {c₁ c₂ : TM2.Cfg Γ Λ σ}
    (hl : c₁.l = c₂.l) (hv : c₁.var = c₂.var) (hs : c₁.stk = c₂.stk) : c₁ = c₂ := by
  cases c₁ <;> cases c₂ <;> cases hl <;> cases hv <;> cases hs <;> rfl

private theorem stkIf_eq_update {K : Type} [DecidableEq K] (Γ : K → Type) (k0 : K) (s : List (Γ k0)) :
    (fun k => if h : k = k0 then cast (by cases h; rfl) s else ([] : List (Γ k))) =
      Function.update (fun k => ([] : List (Γ k))) k0 s := by
  classical
  funext k
  by_cases hk : k = k0
  · subst hk
    simp [Function.update]
  · simp [Function.update, hk]

section Simulation

variable {α β γ : Type} {eα : FinEncoding α} {eβ : FinEncoding β} {eγ : FinEncoding γ}
variable {f : α → β} {g : β → γ}

private theorem compFinTM2Core_step_left (h₁ : TM2ComputableInPolyTime eα eβ f)
    (h₂ : TM2ComputableInPolyTime eβ eγ g) (haltTarget : CompLabel h₁.tm h₂.tm)
    (mCopy :
      Bool →
        TM2.Stmt (compΓ h₁.tm h₂.tm eβ.Γ) (CompLabel h₁.tm h₂.tm) (Compσ h₁.tm h₂.tm eβ.Γ))
    (s₂ : h₂.tm.σ) (tmp : Option eβ.Γ) (S₂ : ∀ k : h₂.tm.K, List (h₂.tm.Γ k)) (B : List eβ.Γ)
    {cfg₁ cfg₁' : h₁.tm.Cfg} :
    h₁.tm.step cfg₁ = some cfg₁' →
      (compFinTM2Core h₁ h₂ haltTarget mCopy).step
          (embedLeftCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) haltTarget s₂ tmp S₂ B cfg₁) =
        some
          (embedLeftCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) haltTarget s₂ tmp S₂ B cfg₁') := by
  classical
  intro hStep
  rcases cfg₁ with ⟨lbl, v, S⟩
  cases lbl with
  | none =>
      simp [FinTM2.step, TM2.step] at hStep
  | some l =>
      have hCfg1' : cfg₁' = stepAux (h₁.tm.m l) v S := by
        simpa [FinTM2.step, TM2.step] using hStep.symm
      subst hCfg1'
      -- unfold the composed machine `step` on a left-embedded configuration
      simp [compFinTM2Core, FinTM2.step, TM2.step, embedLeftCfg, stepAux_liftStmtLeft]

private theorem compFinTM2Core_step_right (h₁ : TM2ComputableInPolyTime eα eβ f)
    (h₂ : TM2ComputableInPolyTime eβ eγ g)
    (haltTarget : CompLabel h₁.tm h₂.tm)
    (mCopy :
      Bool →
        TM2.Stmt (compΓ h₁.tm h₂.tm eβ.Γ) (CompLabel h₁.tm h₂.tm) (Compσ h₁.tm h₂.tm eβ.Γ))
    (s₁ : h₁.tm.σ) (tmp : Option eβ.Γ) (S₁ : ∀ k : h₁.tm.K, List (h₁.tm.Γ k)) (B : List eβ.Γ)
    {cfg₂ cfg₂' : h₂.tm.Cfg} :
    h₂.tm.step cfg₂ = some cfg₂' →
      (compFinTM2Core h₁ h₂ haltTarget mCopy).step
          (embedRightCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) s₁ tmp S₁ B cfg₂) =
        some
          (embedRightCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) s₁ tmp S₁ B cfg₂') := by
  classical
  intro hStep
  rcases cfg₂ with ⟨lbl, v, S⟩
  cases lbl with
  | none =>
      simp [FinTM2.step, TM2.step] at hStep
  | some l =>
      have hCfg2' : cfg₂' = stepAux (h₂.tm.m l) v S := by
        simpa [FinTM2.step, TM2.step] using hStep.symm
      subst hCfg2'
      simp [compFinTM2Core, FinTM2.step, TM2.step, embedRightCfg, stepAux_liftStmtRight]

private theorem compFinTM2Core_iterate_left (h₁ : TM2ComputableInPolyTime eα eβ f)
    (h₂ : TM2ComputableInPolyTime eβ eγ g) (haltTarget : CompLabel h₁.tm h₂.tm)
    (mCopy :
      Bool →
        TM2.Stmt (compΓ h₁.tm h₂.tm eβ.Γ) (CompLabel h₁.tm h₂.tm) (Compσ h₁.tm h₂.tm eβ.Γ))
    (s₂ : h₂.tm.σ) (tmp : Option eβ.Γ) (S₂ : ∀ k : h₂.tm.K, List (h₂.tm.Γ k)) (B : List eβ.Γ) :
    ∀ (t : ℕ) {cfg₀ cfg : h₁.tm.Cfg},
      (flip bind h₁.tm.step)^[t] (some cfg₀) = some cfg →
        (flip bind (compFinTM2Core h₁ h₂ haltTarget mCopy).step)^[t]
              (some
                (embedLeftCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) haltTarget s₂ tmp S₂ B cfg₀)) =
            some
              (embedLeftCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) haltTarget s₂ tmp S₂ B cfg) := by
  classical
  intro t
  induction t with
  | zero =>
      intro cfg₀ cfg h
      simp at h
      cases h
      simp
  | succ t ih =>
      intro cfg₀ cfg h
      have hSucc : (flip bind h₁.tm.step) ((flip bind h₁.tm.step)^[t] (some cfg₀)) = some cfg := by
        simpa [Function.iterate_succ_apply'] using h
      cases hMid : ((flip bind h₁.tm.step)^[t] (some cfg₀)) with
      | none =>
          rw [hMid] at hSucc
          simp [flip, Option.bind] at hSucc
      | some cfgMid =>
          rw [hMid] at hSucc
          have hStepMid : h₁.tm.step cfgMid = some cfg := by
            simpa [flip, Option.bind] using hSucc
          have ih' := ih (cfg₀ := cfg₀) (cfg := cfgMid) hMid
          have hStepComp :
              (compFinTM2Core h₁ h₂ haltTarget mCopy).step
                  (embedLeftCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) haltTarget s₂ tmp S₂ B cfgMid) =
                some
                  (embedLeftCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) haltTarget s₂ tmp S₂ B cfg) :=
            compFinTM2Core_step_left (h₁ := h₁) (h₂ := h₂) (haltTarget := haltTarget) (mCopy := mCopy)
              (s₂ := s₂) (tmp := tmp) (S₂ := S₂) (B := B) hStepMid
          -- unfold one step of the iterate on the composed side
          rw [Function.iterate_succ_apply']
          rw [ih']
          simpa [flip, Option.bind] using hStepComp

private theorem compFinTM2Core_iterate_right (h₁ : TM2ComputableInPolyTime eα eβ f)
    (h₂ : TM2ComputableInPolyTime eβ eγ g) (haltTarget : CompLabel h₁.tm h₂.tm)
    (mCopy :
      Bool →
        TM2.Stmt (compΓ h₁.tm h₂.tm eβ.Γ) (CompLabel h₁.tm h₂.tm) (Compσ h₁.tm h₂.tm eβ.Γ))
    (s₁ : h₁.tm.σ) (tmp : Option eβ.Γ) (S₁ : ∀ k : h₁.tm.K, List (h₁.tm.Γ k)) (B : List eβ.Γ) :
    ∀ (t : ℕ) {cfg₀ cfg : h₂.tm.Cfg},
      (flip bind h₂.tm.step)^[t] (some cfg₀) = some cfg →
        (flip bind (compFinTM2Core h₁ h₂ haltTarget mCopy).step)^[t]
              (some
                (embedRightCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) s₁ tmp S₁ B cfg₀)) =
            some
              (embedRightCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) s₁ tmp S₁ B cfg) := by
  classical
  intro t
  induction t with
  | zero =>
      intro cfg₀ cfg h
      simp at h
      cases h
      simp
  | succ t ih =>
      intro cfg₀ cfg h
      have hSucc : (flip bind h₂.tm.step) ((flip bind h₂.tm.step)^[t] (some cfg₀)) = some cfg := by
        simpa [Function.iterate_succ_apply'] using h
      cases hMid : ((flip bind h₂.tm.step)^[t] (some cfg₀)) with
      | none =>
          rw [hMid] at hSucc
          simp [flip, Option.bind] at hSucc
      | some cfgMid =>
          rw [hMid] at hSucc
          have hStepMid : h₂.tm.step cfgMid = some cfg := by
            simpa [flip, Option.bind] using hSucc
          have ih' := ih (cfg₀ := cfg₀) (cfg := cfgMid) hMid
          have hStepComp :
              (compFinTM2Core h₁ h₂ haltTarget mCopy).step
                  (embedRightCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) s₁ tmp S₁ B cfgMid) =
                some
                  (embedRightCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) s₁ tmp S₁ B cfg) :=
            compFinTM2Core_step_right (h₁ := h₁) (h₂ := h₂) (haltTarget := haltTarget) (mCopy := mCopy)
              (s₁ := s₁) (tmp := tmp) (S₁ := S₁) (B := B) hStepMid
          rw [Function.iterate_succ_apply']
          rw [ih']
          simpa [flip, Option.bind] using hStepComp

end Simulation

section CopyStage

variable {α β γ : Type} {eα : FinEncoding α} {eβ : FinEncoding β} {eγ : FinEncoding γ}
variable {f : α → β} {g : β → γ}

variable (h₁ : TM2ComputableInPolyTime eα eβ f) (h₂ : TM2ComputableInPolyTime eβ eγ g) (β0 : eβ.Γ)

private noncomputable abbrev tmComp : FinTM2 :=
  compFinTM2_nonempty h₁ h₂ β0

private def leftStk (out : List (h₁.tm.Γ h₁.tm.k₁)) : ∀ k : h₁.tm.K, List (h₁.tm.Γ k) :=
  Function.update (fun k => ([] : List (h₁.tm.Γ k))) h₁.tm.k₁ out

private def rightStk (inp : List (h₂.tm.Γ h₂.tm.k₀)) : ∀ k : h₂.tm.K, List (h₂.tm.Γ k) :=
  Function.update (fun k => ([] : List (h₂.tm.Γ k))) h₂.tm.k₀ inp

private def cfgCopy1 (tmp : Option eβ.Γ) (lβ : List eβ.Γ) (buf : List eβ.Γ)
    (inp : List (h₂.tm.Γ h₂.tm.k₀)) : (tmComp (h₁ := h₁) (h₂ := h₂) β0).Cfg where
  l := some (copy1L (tm₁ := h₁.tm) (tm₂ := h₂.tm))
  var := (h₁.tm.initialState, h₂.tm.initialState, tmp)
  stk :=
    compStk (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ)
      (leftStk (h₁ := h₁) (List.map h₁.outputAlphabet.invFun lβ)) (rightStk (h₂ := h₂) inp) buf

private def cfgCopy2 (tmp : Option eβ.Γ) (buf : List eβ.Γ)
    (inp : List (h₂.tm.Γ h₂.tm.k₀)) : (tmComp (h₁ := h₁) (h₂ := h₂) β0).Cfg where
  l := some (copy2L (tm₁ := h₁.tm) (tm₂ := h₂.tm))
  var := (h₁.tm.initialState, h₂.tm.initialState, tmp)
  stk :=
    compStk (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ)
      (leftStk (h₁ := h₁) []) (rightStk (h₂ := h₂) inp) buf

private def cfgRightMain (inp : List (h₂.tm.Γ h₂.tm.k₀)) : (tmComp (h₁ := h₁) (h₂ := h₂) β0).Cfg where
  l := some (inrL (tm₁ := h₁.tm) (tm₂ := h₂.tm) h₂.tm.main)
  var := (h₁.tm.initialState, h₂.tm.initialState, none)
  stk :=
    compStk (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ)
      (leftStk (h₁ := h₁) []) (rightStk (h₂ := h₂) inp) []

private theorem copy1_step_nil (tmp : Option eβ.Γ) (buf : List eβ.Γ) (inp : List (h₂.tm.Γ h₂.tm.k₀)) :
    (tmComp (h₁ := h₁) (h₂ := h₂) β0).step (cfgCopy1 (h₁ := h₁) (h₂ := h₂) β0 tmp [] buf inp) =
      some (cfgCopy2 (h₁ := h₁) (h₂ := h₂) β0 none buf inp) := by
  classical
  simp [tmComp, compFinTM2_nonempty, compFinTM2Core, cfgCopy1, cfgCopy2, leftStk, rightStk, copy1Stmt, copy1L,
    copy2L, inlK, bufK, compStk, compStk_update_inl, Function.update_idem]

private theorem copy1_step_cons (b : eβ.Γ) (bs : List eβ.Γ) (tmp : Option eβ.Γ) (buf : List eβ.Γ)
    (inp : List (h₂.tm.Γ h₂.tm.k₀)) :
    (tmComp (h₁ := h₁) (h₂ := h₂) β0).step (cfgCopy1 (h₁ := h₁) (h₂ := h₂) β0 tmp (b :: bs) buf inp) =
      some (cfgCopy1 (h₁ := h₁) (h₂ := h₂) β0 (some b) bs (b :: buf) inp) := by
  classical
  simp [tmComp, compFinTM2_nonempty, compFinTM2Core, cfgCopy1, leftStk, rightStk, copy1Stmt, copy1L, copy2L, inlK,
    bufK, compStk, compStk_update_inl, compStk_update_buf, Function.update_idem]

private theorem copy2_step_nil (tmp : Option eβ.Γ) (inp : List (h₂.tm.Γ h₂.tm.k₀)) :
    (tmComp (h₁ := h₁) (h₂ := h₂) β0).step (cfgCopy2 (h₁ := h₁) (h₂ := h₂) β0 tmp [] inp) =
      some (cfgRightMain (h₁ := h₁) (h₂ := h₂) β0 inp) := by
  classical
  simp [tmComp, compFinTM2_nonempty, compFinTM2Core, cfgCopy2, cfgRightMain, leftStk, rightStk, copy2Stmt, copy2L,
    bufK, compStk, Function.update_idem]

private theorem copy2_step_cons (b : eβ.Γ) (bs : List eβ.Γ) (tmp : Option eβ.Γ) (inp : List (h₂.tm.Γ h₂.tm.k₀)) :
    (tmComp (h₁ := h₁) (h₂ := h₂) β0).step (cfgCopy2 (h₁ := h₁) (h₂ := h₂) β0 tmp (b :: bs) inp) =
      some (cfgCopy2 (h₁ := h₁) (h₂ := h₂) β0 (some b) bs (h₂.inputAlphabet.invFun b :: inp)) := by
  classical
  simp [tmComp, compFinTM2_nonempty, compFinTM2Core, cfgCopy2, leftStk, rightStk, copy2Stmt, copy2L, inrK, bufK,
    compStk, compStk_update_inr, compStk_update_buf, Function.update_idem]

private noncomputable def copy1_run (inp : List (h₂.tm.Γ h₂.tm.k₀)) :
    ∀ (lβ : List eβ.Γ) (buf : List eβ.Γ) (tmp : Option eβ.Γ),
      EvalsToInTime (tmComp (h₁ := h₁) (h₂ := h₂) β0).step
        (cfgCopy1 (h₁ := h₁) (h₂ := h₂) β0 tmp lβ buf inp)
        (some (cfgCopy2 (h₁ := h₁) (h₂ := h₂) β0 none (lβ.reverse ++ buf) inp))
        (lβ.length + 1) := by
  classical
  intro lβ
  induction lβ with
  | nil =>
      intro buf tmp
      -- one step: copy1 -> copy2
      exact
        evalsToInTime_mono
          (h := evalsToInTime_ofStep _ _ _ (copy1_step_nil (h₁ := h₁) (h₂ := h₂) (β0 := β0) tmp buf inp))
          (by simp)
  | cons b bs ih =>
      intro buf tmp
      have hStep :
          EvalsToInTime (tmComp (h₁ := h₁) (h₂ := h₂) β0).step
            (cfgCopy1 (h₁ := h₁) (h₂ := h₂) β0 tmp (b :: bs) buf inp)
            (some (cfgCopy1 (h₁ := h₁) (h₂ := h₂) β0 (some b) bs (b :: buf) inp)) 1 :=
        evalsToInTime_ofStep _ _ _ (copy1_step_cons (h₁ := h₁) (h₂ := h₂) (β0 := β0) b bs tmp buf inp)
      have hRest :=
        ih (buf := b :: buf) (tmp := some b)
      have hTrans :=
        EvalsToInTime.trans (f := (tmComp (h₁ := h₁) (h₂ := h₂) β0).step) 1 (bs.length + 1)
          (cfgCopy1 (h₁ := h₁) (h₂ := h₂) β0 tmp (b :: bs) buf inp)
          (cfgCopy1 (h₁ := h₁) (h₂ := h₂) β0 (some b) bs (b :: buf) inp)
          (some (cfgCopy2 (h₁ := h₁) (h₂ := h₂) β0 none (bs.reverse ++ (b :: buf)) inp)) hStep hRest
      -- normalize the buffer term to `(b :: bs).reverse ++ buf`
      simpa [List.reverse_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hTrans

private noncomputable def copy2_run :
    ∀ (buf : List eβ.Γ) (inp : List (h₂.tm.Γ h₂.tm.k₀)) (tmp : Option eβ.Γ),
      EvalsToInTime (tmComp (h₁ := h₁) (h₂ := h₂) β0).step
        (cfgCopy2 (h₁ := h₁) (h₂ := h₂) β0 tmp buf inp)
        (some (cfgRightMain (h₁ := h₁) (h₂ := h₂) β0 (buf.reverse.map h₂.inputAlphabet.invFun ++ inp)))
        (buf.length + 1) := by
  classical
  intro buf
  induction buf with
  | nil =>
      intro inp tmp
      exact
        evalsToInTime_mono
          (h := evalsToInTime_ofStep _ _ _ (copy2_step_nil (h₁ := h₁) (h₂ := h₂) (β0 := β0) tmp inp))
          (by simp)
  | cons b bs ih =>
      intro inp tmp
      have hStep :
          EvalsToInTime (tmComp (h₁ := h₁) (h₂ := h₂) β0).step
            (cfgCopy2 (h₁ := h₁) (h₂ := h₂) β0 tmp (b :: bs) inp)
            (some (cfgCopy2 (h₁ := h₁) (h₂ := h₂) β0 (some b) bs (h₂.inputAlphabet.invFun b :: inp))) 1 :=
        evalsToInTime_ofStep _ _ _ (copy2_step_cons (h₁ := h₁) (h₂ := h₂) (β0 := β0) b bs tmp inp)
      have hRest :=
        ih (inp := h₂.inputAlphabet.invFun b :: inp) (tmp := some b)
      have hTrans :=
        EvalsToInTime.trans (f := (tmComp (h₁ := h₁) (h₂ := h₂) β0).step) 1 (bs.length + 1)
          (cfgCopy2 (h₁ := h₁) (h₂ := h₂) β0 tmp (b :: bs) inp)
          (cfgCopy2 (h₁ := h₁) (h₂ := h₂) β0 (some b) bs (h₂.inputAlphabet.invFun b :: inp))
          (some (cfgRightMain (h₁ := h₁) (h₂ := h₂) β0 (bs.reverse.map h₂.inputAlphabet.invFun ++ (h₂.inputAlphabet.invFun b :: inp))))
          hStep hRest
      simpa [List.reverse_cons, List.map_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hTrans

private noncomputable def copy_run (lβ : List eβ.Γ) :
    EvalsToInTime (tmComp (h₁ := h₁) (h₂ := h₂) β0).step
      (cfgCopy1 (h₁ := h₁) (h₂ := h₂) β0 none lβ [] [])
      (some (cfgRightMain (h₁ := h₁) (h₂ := h₂) β0 (List.map h₂.inputAlphabet.invFun lβ)))
      (2 * lβ.length + 2) := by
  classical
  have h1 :
      EvalsToInTime (tmComp (h₁ := h₁) (h₂ := h₂) β0).step
        (cfgCopy1 (h₁ := h₁) (h₂ := h₂) β0 none lβ [] [])
        (some (cfgCopy2 (h₁ := h₁) (h₂ := h₂) β0 none lβ.reverse [])) (lβ.length + 1) := by
    simpa using (copy1_run (h₁ := h₁) (h₂ := h₂) (β0 := β0) (inp := []) lβ [] none)
  have h2 :=
    copy2_run (h₁ := h₁) (h₂ := h₂) (β0 := β0) (buf := lβ.reverse) (inp := []) (tmp := none)
  have hTrans :=
    EvalsToInTime.trans (f := (tmComp (h₁ := h₁) (h₂ := h₂) β0).step) (lβ.length + 1) (lβ.reverse.length + 1)
      (cfgCopy1 (h₁ := h₁) (h₂ := h₂) β0 none lβ [] [])
      (cfgCopy2 (h₁ := h₁) (h₂ := h₂) β0 none lβ.reverse [])
      (some (cfgRightMain (h₁ := h₁) (h₂ := h₂) β0 (lβ.reverse.reverse.map h₂.inputAlphabet.invFun ++ [])))
      h1 h2
  -- normalize the final input list and the transitivity time bound.
  simpa [List.reverse_reverse, List.length_reverse, Nat.two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hTrans

end CopyStage

section Composition

variable {α β γ : Type} {eα : FinEncoding α} {eβ : FinEncoding β} {eγ : FinEncoding γ}
variable {f : α → β} {g : β → γ}

/--
An axiom-free composition theorem for `TM2ComputableInPolyTime`, avoiding Mathlib's `proof_wanted`
placeholder.
-/
theorem TM2ComputableInPolyTime.comp (h₁ : TM2ComputableInPolyTime eα eβ f)
    (h₂ : TM2ComputableInPolyTime eβ eγ g) : Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f)) := by
  classical
  -- We split on whether the intermediate alphabet is inhabited; the `Nonempty` case uses the
  -- explicit copy-phase machine, while the `IsEmpty` case can skip copying entirely.
  by_cases hβ : Nonempty eβ.Γ
  ·
    classical
    let β0 : eβ.Γ := Classical.choice hβ
    -- Composed machine: run `h₁`, copy its output to `h₂`'s input, then run `h₂`.
    let tm : FinTM2 := compFinTM2_nonempty (h₁ := h₁) (h₂ := h₂) β0
    -- Bound on the intermediate output length (in symbols of `eβ.Γ`).
    let M : ℕ := maxPushBound h₁.tm h₁.tm.k₁
    let q : Polynomial ℕ := Polynomial.X + Polynomial.C M * h₁.time
    let timeCopy : Polynomial ℕ := Polynomial.C 2 * q + Polynomial.C 2
    let timeH₂ : Polynomial ℕ := h₂.time.comp q
    let time : Polynomial ℕ := h₁.time + timeCopy + timeH₂
    refine
      ⟨{
        tm := tm
        inputAlphabet := by
          -- `tm.k₀` is the left input stack, so we reuse `h₁.inputAlphabet`.
          simpa [tm, compFinTM2_nonempty, compFinTM2Core, compΓ, inlK] using h₁.inputAlphabet
        outputAlphabet := by
          -- `tm.k₁` is the right output stack, so we reuse `h₂.outputAlphabet`.
          simpa [tm, compFinTM2_nonempty, compFinTM2Core, compΓ, inrK] using h₂.outputAlphabet
        time := time
        outputsFun := ?_ }⟩
    ·
      intro a
      -- Abbreviations for the relevant lists.
      let n : ℕ := (eα.encode a).length
      let input₁ : List (h₁.tm.Γ h₁.tm.k₀) := List.map h₁.inputAlphabet.invFun (eα.encode a)
      let lβ : List eβ.Γ := eβ.encode (f a)
      let out₁ : List (h₁.tm.Γ h₁.tm.k₁) := List.map h₁.outputAlphabet.symm lβ
      let input₂ : List (h₂.tm.Γ h₂.tm.k₀) := List.map h₂.inputAlphabet.invFun lβ
      let out₂ : List (h₂.tm.Γ h₂.tm.k₁) := List.map h₂.outputAlphabet.invFun (eγ.encode (g (f a)))

      -- Unpack the correctness/time certificates for `h₁` and `h₂`.
      have h₁out :
          TM2OutputsInTime h₁.tm input₁ (some out₁) (h₁.time.eval n) := by
        simpa [TM2OutputsInTime, TM2Outputs, input₁, out₁, n] using h₁.outputsFun a
      have h₂out :
          TM2OutputsInTime h₂.tm input₂ (some out₂) (h₂.time.eval lβ.length) := by
        simpa [TM2OutputsInTime, TM2Outputs, input₂, out₂, lβ] using h₂.outputsFun (f a)

      -- Length bound: `lβ.length ≤ q.eval n`.
      have hLenInputK₁ :
          ((initList h₁.tm input₁).stk h₁.tm.k₁).length ≤ n := by
        -- Prove the general bound `((initList tm s).stk k).length ≤ s.length` and then specialize.
        have hLenGen :
            ∀ k : h₁.tm.K, ((initList h₁.tm input₁).stk k).length ≤ input₁.length := by
          intro k
          by_cases hk : k = h₁.tm.k₀
          · subst hk
            simp [initList]
          · simp [initList, hk]
        have hLen : ((initList h₁.tm input₁).stk h₁.tm.k₁).length ≤ input₁.length :=
          hLenGen h₁.tm.k₁
        simpa [input₁, n, List.length_map] using hLen
      have hIter₁ :
          (flip bind h₁.tm.step)^[h₁out.steps] (some (initList h₁.tm input₁)) =
            some (haltList h₁.tm out₁) := by
        simpa [TM2OutputsInTime, TM2Outputs, input₁, out₁] using h₁out.evals_in_steps
      have hLenOut :
          out₁.length ≤ n + h₁out.steps * M := by
        have hLen :=
          stk_length_le_of_iterate (tm := h₁.tm) (k := h₁.tm.k₁) h₁out.steps (cfg₀ := initList h₁.tm input₁)
            (cfg := haltList h₁.tm out₁) hIter₁
        -- `haltList` puts `out₁` on stack `k₁`.
        have hLen' :
            out₁.length ≤ ((initList h₁.tm input₁).stk h₁.tm.k₁).length + h₁out.steps * M := by
          simpa [haltList] using hLen
        exact le_trans hLen' (by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            Nat.add_le_add_right hLenInputK₁ (h₁out.steps * M))
      have hLenβ :
          lβ.length ≤ q.eval n := by
        have hLenOut' :
            lβ.length ≤ n + h₁out.steps * M := by
          simpa [out₁, List.length_map] using hLenOut
        have hLenOut'' :
            lβ.length ≤ n + h₁.time.eval n * M := by
          exact le_trans hLenOut' (by
            refine Nat.add_le_add_left ?_ _
            exact Nat.mul_le_mul_right M h₁out.steps_le_m)
        -- rewrite the RHS as `q.eval n`
        simpa [q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Nat.mul_comm, Nat.mul_left_comm,
          Nat.mul_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hLenOut''

      -- Stage 1: simulate `h₁` inside the composed machine.
      have hStage₁ :
          EvalsToInTime tm.step (initList tm input₁)
            (some (cfgCopy1 (h₁ := h₁) (h₂ := h₂) β0 none lβ [] [])) (h₁.time.eval n) := by
        -- Lift the raw iterate from `h₁` to the composed machine using the simulation lemma.
        have hLift :
            (flip bind tm.step)^[h₁out.steps]
                  (some (embedLeftCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ)
                    (copy1L (tm₁ := h₁.tm) (tm₂ := h₂.tm)) h₂.tm.initialState none (fun _ => []) [] (initList h₁.tm input₁))) =
                some
                  (embedLeftCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ)
                    (copy1L (tm₁ := h₁.tm) (tm₂ := h₂.tm)) h₂.tm.initialState none (fun _ => []) [] (haltList h₁.tm out₁)) := by
          -- `tm` is definitional equal to the corresponding `compFinTM2Core` instance.
          simpa [tm, compFinTM2_nonempty, compFinTM2Core] using
            (compFinTM2Core_iterate_left (h₁ := h₁) (h₂ := h₂)
              (haltTarget := copy1L (tm₁ := h₁.tm) (tm₂ := h₂.tm))
              (mCopy := fun
                | false => copy1Stmt h₁ h₂ β0
                | true => copy2Stmt h₁ h₂ β0)
              (s₂ := h₂.tm.initialState) (tmp := none) (S₂ := fun _ => []) (B := [])
              h₁out.steps (cfg₀ := initList h₁.tm input₁) (cfg := haltList h₁.tm out₁) hIter₁)
        -- Package into `EvalsToInTime`, keeping the step bound from `h₁out`.
        refine
          { steps := h₁out.steps
            evals_in_steps := ?_
            steps_le_m := h₁out.steps_le_m }
        -- Normalize start/end configurations.
        -- `hLift` runs from the embedded `h₁`-initial configuration; we rewrite that initial
        -- configuration to `initList tm input₁`.
        have hStart :
            embedLeftCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ)
                (copy1L (tm₁ := h₁.tm) (tm₂ := h₂.tm)) h₂.tm.initialState none (fun _ => []) [] (initList h₁.tm input₁) =
              initList tm input₁ := by
          -- Compare the three fields `l`, `var`, and `stk`.
          -- The `stk` field needs a small case split on the composite key.
          apply (by
            intro c1 c2 hl hv hs
            cases c1 <;> cases c2 <;> cases hl <;> cases hv <;> cases hs <;> rfl :
              ∀ {c1 c2 : TM2.Cfg _ _ _}, c1.l = c2.l → c1.var = c2.var → c1.stk = c2.stk → c1 = c2)
          ·
            simp [embedLeftCfg, initList_l, tm, compFinTM2_nonempty, compFinTM2Core]
          ·
            simp [embedLeftCfg, initList_var, tm, compFinTM2_nonempty, compFinTM2Core]
          ·
            funext k
            cases k with
            | inl k =>
                cases k with
                | inl k =>
                    by_cases hk : k = h₁.tm.k₀
                    · subst hk
                      simp [embedLeftCfg, initList_stk_eq_update, initList, compStk, compΓ, inlK, tm,
                        compFinTM2_nonempty, compFinTM2Core]
                    · simp [embedLeftCfg, initList_stk_eq_update, initList, compStk, compΓ, inlK, tm,
                        compFinTM2_nonempty, compFinTM2Core, hk]
                | inr k =>
                    simp [embedLeftCfg, initList_stk_eq_update, initList, compStk, compΓ, tm, compFinTM2_nonempty,
                      compFinTM2Core]
            | inr u =>
                cases u
                simp [embedLeftCfg, initList_stk_eq_update, initList, compStk, tm, compFinTM2_nonempty, compFinTM2Core]

        have hEnd :
            embedLeftCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ)
                (copy1L (tm₁ := h₁.tm) (tm₂ := h₂.tm)) h₂.tm.initialState none (fun _ => []) [] (haltList h₁.tm out₁) =
              cfgCopy1 (h₁ := h₁) (h₂ := h₂) β0 none lβ [] [] := by
          -- Similar field-by-field comparison, using `haltList_stk_eq_update`.
          apply (by
            intro c1 c2 hl hv hs
            cases c1 <;> cases c2 <;> cases hl <;> cases hv <;> cases hs <;> rfl :
              ∀ {c1 c2 : TM2.Cfg _ _ _}, c1.l = c2.l → c1.var = c2.var → c1.stk = c2.stk → c1 = c2)
          ·
            simp [embedLeftCfg, haltList_l, cfgCopy1, tmComp, tm, compFinTM2_nonempty, compFinTM2Core]
          ·
            simp [embedLeftCfg, haltList_var, cfgCopy1, tmComp, tm, compFinTM2_nonempty, compFinTM2Core]
          ·
            funext k
            cases k with
            | inl k =>
                cases k with
                | inl k =>
                    by_cases hk : k = h₁.tm.k₁
                    · subst hk
                      simp [embedLeftCfg, cfgCopy1, leftStk, haltList_stk_eq_update, haltList, compStk, compΓ, inlK,
                        tmComp, tm, compFinTM2_nonempty, compFinTM2Core, out₁]
                    · simp [embedLeftCfg, cfgCopy1, leftStk, haltList_stk_eq_update, haltList, compStk, compΓ, inlK,
                        tmComp, tm, compFinTM2_nonempty, compFinTM2Core, hk]
                | inr k =>
                    simp [embedLeftCfg, cfgCopy1, leftStk, rightStk, haltList_stk_eq_update, haltList, compStk, tmComp,
                      tm, out₁, compFinTM2_nonempty, compFinTM2Core, Function.update_idem]
            | inr u =>
                cases u
                simp [embedLeftCfg, cfgCopy1, leftStk, haltList_stk_eq_update, haltList, compStk, tmComp, tm,
                  compFinTM2_nonempty, compFinTM2Core]

        -- Rewrite both sides of `hLift` using `hStart`/`hEnd`.
        simpa [hStart, hEnd] using hLift

      -- Stage 2: copy `h₁`'s output (in `eβ.Γ`) to `h₂`'s input.
      have hStage₂raw :
          EvalsToInTime tm.step
            (cfgCopy1 (h₁ := h₁) (h₂ := h₂) β0 none lβ [] [])
            (some (cfgRightMain (h₁ := h₁) (h₂ := h₂) β0 input₂)) (2 * lβ.length + 2) := by
        simpa [tm, input₂] using (copy_run (h₁ := h₁) (h₂ := h₂) (β0 := β0) lβ)
      have hStage₂ :
          EvalsToInTime tm.step
            (cfgCopy1 (h₁ := h₁) (h₂ := h₂) β0 none lβ [] [])
            (some (cfgRightMain (h₁ := h₁) (h₂ := h₂) β0 input₂)) (timeCopy.eval n) := by
        refine evalsToInTime_mono (h := hStage₂raw) (hm := ?_)
        -- `2 * lβ.length + 2 ≤ timeCopy.eval n = 2 * q.eval n + 2`.
        have hmul : 2 * lβ.length ≤ 2 * q.eval n := Nat.mul_le_mul_left 2 hLenβ
        have : 2 * lβ.length + 2 ≤ 2 * q.eval n + 2 := Nat.add_le_add_right hmul 2
        simpa [timeCopy, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Nat.mul_assoc, Nat.mul_left_comm,
          Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

      -- Stage 3: simulate `h₂` inside the composed machine, then widen to `timeH₂.eval n`.
      have hIter₂ :
          (flip bind h₂.tm.step)^[h₂out.steps] (some (initList h₂.tm input₂)) =
            some (haltList h₂.tm out₂) := by
        simpa [TM2OutputsInTime, TM2Outputs, input₂, out₂] using h₂out.evals_in_steps
      have hStage₃raw :
          EvalsToInTime tm.step
            (cfgRightMain (h₁ := h₁) (h₂ := h₂) β0 input₂)
            (some (haltList tm out₂)) (h₂.time.eval lβ.length) := by
        -- Lift the iterate from `h₂` to the composed machine.
        have hLift :
            (flip bind tm.step)^[h₂out.steps]
                  (some
                    (embedRightCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) h₁.tm.initialState none
                      (fun _ => []) [] (initList h₂.tm input₂))) =
                some
                  (embedRightCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) h₁.tm.initialState none
                    (fun _ => []) [] (haltList h₂.tm out₂)) := by
          simpa [tm, compFinTM2_nonempty, compFinTM2Core] using
            (compFinTM2Core_iterate_right (h₁ := h₁) (h₂ := h₂)
              (haltTarget := copy1L (tm₁ := h₁.tm) (tm₂ := h₂.tm))
              (mCopy := fun
                | false => copy1Stmt h₁ h₂ β0
                | true => copy2Stmt h₁ h₂ β0)
              (s₁ := h₁.tm.initialState) (tmp := none) (S₁ := fun _ => []) (B := [])
              h₂out.steps (cfg₀ := initList h₂.tm input₂) (cfg := haltList h₂.tm out₂) hIter₂)
        refine
          { steps := h₂out.steps
            evals_in_steps := ?_
            steps_le_m := h₂out.steps_le_m }
        -- Rewrite the embedded start/end configurations to our canonical ones.
        have hStart :
            embedRightCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) h₁.tm.initialState none (fun _ => []) []
                (initList h₂.tm input₂) =
              cfgRightMain (h₁ := h₁) (h₂ := h₂) β0 input₂ := by
          apply cfg_eq_of_fields
          · simp [embedRightCfg, cfgRightMain, initList_l]
          · simp [embedRightCfg, cfgRightMain, initList_var]
          ·
            -- compare stacks pointwise; only the right input stack can be nonempty
            funext k
            cases k with
            | inl k =>
                cases k <;>
                  simp [embedRightCfg, cfgRightMain, compStk, leftStk, rightStk, initList_stk_eq_update]
            | inr u =>
                cases u
                simp [embedRightCfg, cfgRightMain, compStk, leftStk, rightStk, initList_stk_eq_update]
        have hEnd :
            embedRightCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) h₁.tm.initialState none (fun _ => []) []
                (haltList h₂.tm out₂) =
              haltList tm out₂ := by
          apply cfg_eq_of_fields
          · simp [embedRightCfg, haltList_l, haltList_l, tm, compFinTM2_nonempty, compFinTM2Core]
          · simp [embedRightCfg, haltList_var, haltList_var, tm, compFinTM2_nonempty, compFinTM2Core]
          ·
            funext k
            cases k with
            | inl k =>
                cases k <;> simp [embedRightCfg, haltList_stk_eq_update, compStk, tm, compFinTM2_nonempty, compFinTM2Core]
            | inr u =>
                cases u
                simp [embedRightCfg, haltList_stk_eq_update, compStk, haltList_stk_eq_update, tm, compFinTM2_nonempty,
                  compFinTM2Core]
        simpa [hStart, hEnd] using hLift
      have hStage₃ :
          EvalsToInTime tm.step
            (cfgRightMain (h₁ := h₁) (h₂ := h₂) β0 input₂)
            (some (haltList tm out₂)) (timeH₂.eval n) := by
        refine evalsToInTime_mono (h := hStage₃raw) (hm := ?_)
        -- Use monotonicity of polynomial evaluation together with `hLenβ`.
        have hmono : h₂.time.eval lβ.length ≤ h₂.time.eval (q.eval n) :=
          (Polynomial.eval_monotone_nat (p := h₂.time)) hLenβ
        -- `timeH₂.eval n = h₂.time.eval (q.eval n)`.
        simpa [timeH₂] using hmono

      -- Combine the three stages, then widen the final step bound to `time.eval n`.
      have h12 :=
        EvalsToInTime.trans (f := tm.step) (h₁.time.eval n) (timeCopy.eval n)
          (initList tm input₁)
          (cfgCopy1 (h₁ := h₁) (h₂ := h₂) β0 none lβ [] [])
          (some (cfgRightMain (h₁ := h₁) (h₂ := h₂) β0 input₂))
          hStage₁ hStage₂
      have h123 :=
        EvalsToInTime.trans (f := tm.step) (timeCopy.eval n + h₁.time.eval n) (timeH₂.eval n)
          (initList tm input₁)
          (cfgRightMain (h₁ := h₁) (h₂ := h₂) β0 input₂)
          (some (haltList tm out₂))
          h12 hStage₃
      refine evalsToInTime_mono (h := h123) (hm := ?_)
      -- Rearrange and compare the numeric bounds.
      -- `h123` has bound `timeH₂.eval n + (timeCopy.eval n + h₁.time.eval n)`.
      -- `time.eval n` is `h₁.time.eval n + timeCopy.eval n + timeH₂.eval n`.
      have : timeH₂.eval n + (timeCopy.eval n + h₁.time.eval n) ≤ time.eval n := by
        simp [time, Polynomial.eval_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      simpa using this
  ·
    classical
    -- The intermediate alphabet is empty, so we can skip copying and run `h₂` directly.
    haveI : IsEmpty eβ.Γ := ⟨fun x => hβ ⟨x⟩⟩
    let tm : FinTM2 := compFinTM2_empty (h₁ := h₁) (h₂ := h₂)
    let M : ℕ := maxPushBound h₁.tm h₁.tm.k₁
    let q : Polynomial ℕ := Polynomial.X + Polynomial.C M * h₁.time
    let timeCopy : Polynomial ℕ := Polynomial.C 2 * q + Polynomial.C 2
    let timeH₂ : Polynomial ℕ := h₂.time.comp q
    let time : Polynomial ℕ := h₁.time + timeCopy + timeH₂
    refine
      ⟨{
        tm := tm
        inputAlphabet := by
          simpa [tm, compFinTM2_empty, compFinTM2Core, compΓ, inlK] using h₁.inputAlphabet
        outputAlphabet := by
          simpa [tm, compFinTM2_empty, compFinTM2Core, compΓ, inrK] using h₂.outputAlphabet
        time := time
        outputsFun := ?_ }⟩
    ·
      intro a
      let n : ℕ := (eα.encode a).length
      let input₁ : List (h₁.tm.Γ h₁.tm.k₀) := List.map h₁.inputAlphabet.invFun (eα.encode a)
      let input₂ : List (h₂.tm.Γ h₂.tm.k₀) := []
      let out₂ : List (h₂.tm.Γ h₂.tm.k₁) := List.map h₂.outputAlphabet.invFun (eγ.encode (g (f a)))

      have h₁out :
          TM2OutputsInTime h₁.tm input₁
            (some (List.map h₁.outputAlphabet.invFun (eβ.encode (f a)))) (h₁.time.eval n) := by
        simpa [TM2OutputsInTime, TM2Outputs, input₁, n] using h₁.outputsFun a

      have hEncβ : eβ.encode (f a) = [] := by
        cases h : eβ.encode (f a) with
        | nil => simpa using h
        | cons x xs => cases (IsEmpty.false x)

      -- The intermediate encoding is always `[]`, so both the right input and left output are `[]`.
      have hInput₂ : List.map h₂.inputAlphabet.invFun (eβ.encode (f a)) = input₂ := by
        simp [input₂, hEncβ]
      have hOutput₁ : List.map h₁.outputAlphabet.invFun (eβ.encode (f a)) = [] := by
        simp [hEncβ]

      have h₂out :
          TM2OutputsInTime h₂.tm input₂ (some out₂) (h₂.time.eval 0) := by
        -- rewrite `h₂.outputsFun (f a)` using `hEncβ : eβ.encode (f a) = []`
        simpa [input₂, out₂, hEncβ] using h₂.outputsFun (f a)

      -- Stage 1: simulate `h₁` inside the composed machine (which jumps directly to `h₂.main`).
      have hIter₁ :
          (flip bind h₁.tm.step)^[h₁out.steps] (some (initList h₁.tm input₁)) =
            some (haltList h₁.tm (List.map h₁.outputAlphabet.invFun (eβ.encode (f a)))) := by
        simpa [TM2OutputsInTime, TM2Outputs, input₁] using h₁out.evals_in_steps
      have hStage₁ :
          EvalsToInTime tm.step (initList tm input₁)
            (some
              (embedLeftCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ)
                (inrL (tm₁ := h₁.tm) (tm₂ := h₂.tm) h₂.tm.main) h₂.tm.initialState none (fun _ => []) []
                (haltList h₁.tm (List.map h₁.outputAlphabet.invFun (eβ.encode (f a)))))) (h₁.time.eval n) := by
        have hLift :
            (flip bind tm.step)^[h₁out.steps]
                  (some
                    (embedLeftCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ)
                      (inrL (tm₁ := h₁.tm) (tm₂ := h₂.tm) h₂.tm.main) h₂.tm.initialState none (fun _ => []) []
                      (initList h₁.tm input₁))) =
                some
                  (embedLeftCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ)
                    (inrL (tm₁ := h₁.tm) (tm₂ := h₂.tm) h₂.tm.main) h₂.tm.initialState none (fun _ => []) []
                    (haltList h₁.tm (List.map h₁.outputAlphabet.invFun (eβ.encode (f a))))) := by
          simpa [tm, compFinTM2_empty, compFinTM2Core] using
            (compFinTM2Core_iterate_left (h₁ := h₁) (h₂ := h₂)
              (haltTarget := inrL (tm₁ := h₁.tm) (tm₂ := h₂.tm) h₂.tm.main)
              (mCopy := fun _ => TM2.Stmt.goto (fun _ => inrL (tm₁ := h₁.tm) (tm₂ := h₂.tm) h₂.tm.main))
              (s₂ := h₂.tm.initialState) (tmp := none) (S₂ := fun _ => []) (B := [])
              h₁out.steps (cfg₀ := initList h₁.tm input₁)
              (cfg := haltList h₁.tm (List.map h₁.outputAlphabet.invFun (eβ.encode (f a)))) hIter₁)
        refine
          { steps := h₁out.steps
            evals_in_steps := ?_
            steps_le_m := h₁out.steps_le_m }
        -- Rewrite the embedded start configuration to `initList tm input₁`.
        have hStart :
            embedLeftCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ)
                (inrL (tm₁ := h₁.tm) (tm₂ := h₂.tm) h₂.tm.main) h₂.tm.initialState none (fun _ => []) []
                (initList h₁.tm input₁) =
              initList tm input₁ := by
          apply cfg_eq_of_fields
          · simp [embedLeftCfg, initList_l, tm, compFinTM2_empty, compFinTM2Core]
          · simp [embedLeftCfg, initList_var, tm, compFinTM2_empty, compFinTM2Core]
          ·
            funext k
            cases k with
            | inl k =>
                cases k with
                | inl k =>
                    by_cases hk : k = h₁.tm.k₀
                    · subst hk
                      simp [embedLeftCfg, initList_stk_eq_update, initList, compStk, compΓ, inlK, tm, compFinTM2_empty,
                        compFinTM2Core]
                    ·
                      simp [embedLeftCfg, initList_stk_eq_update, initList, compStk, compΓ, inlK, tm, compFinTM2_empty,
                        compFinTM2Core, hk]
                | inr k =>
                    simp [embedLeftCfg, initList_stk_eq_update, initList, compStk, compΓ, tm, compFinTM2_empty,
                      compFinTM2Core]
            | inr u =>
                cases u
                simp [embedLeftCfg, initList_stk_eq_update, initList, compStk, tm, compFinTM2_empty, compFinTM2Core]
        simpa [hStart] using hLift

      -- Stage 2: run `h₂` inside the composed machine.
      have hIter₂ :
          (flip bind h₂.tm.step)^[h₂out.steps] (some (initList h₂.tm input₂)) =
            some (haltList h₂.tm out₂) := by
        simpa [TM2OutputsInTime, TM2Outputs, input₂, out₂] using h₂out.evals_in_steps
      have hStage₂raw :
          EvalsToInTime tm.step
            (embedRightCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) h₁.tm.initialState none (fun _ => []) []
              (initList h₂.tm input₂))
            (some (haltList tm out₂)) (h₂.time.eval 0) := by
        have hLift :
            (flip bind tm.step)^[h₂out.steps]
                  (some
                    (embedRightCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) h₁.tm.initialState none (fun _ => []) []
                      (initList h₂.tm input₂))) =
                some
                  (embedRightCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) h₁.tm.initialState none (fun _ => []) []
                    (haltList h₂.tm out₂)) := by
          simpa [tm, compFinTM2_empty, compFinTM2Core] using
            (compFinTM2Core_iterate_right (h₁ := h₁) (h₂ := h₂)
              (haltTarget := inrL (tm₁ := h₁.tm) (tm₂ := h₂.tm) h₂.tm.main)
              (mCopy := fun _ => TM2.Stmt.goto (fun _ => inrL (tm₁ := h₁.tm) (tm₂ := h₂.tm) h₂.tm.main))
              (s₁ := h₁.tm.initialState) (tmp := none) (S₁ := fun _ => []) (B := [])
              h₂out.steps (cfg₀ := initList h₂.tm input₂) (cfg := haltList h₂.tm out₂) hIter₂)
        refine
          { steps := h₂out.steps
            evals_in_steps := ?_
            steps_le_m := h₂out.steps_le_m }
        -- Rewrite the embedded halt configuration to `haltList tm out₂`.
        have hEnd :
            embedRightCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) h₁.tm.initialState none (fun _ => []) []
                (haltList h₂.tm out₂) =
              haltList tm out₂ := by
          apply cfg_eq_of_fields
          · simp [embedRightCfg, haltList_l, tm, compFinTM2_empty, compFinTM2Core]
          · simp [embedRightCfg, haltList_var, tm, compFinTM2_empty, compFinTM2Core]
          ·
            funext k
            cases k with
            | inl k =>
                cases k <;>
                  simp [embedRightCfg, haltList_stk_eq_update, compStk, tm, compFinTM2_empty, compFinTM2Core]
            | inr u =>
                cases u
                simp [embedRightCfg, haltList_stk_eq_update, compStk, tm, compFinTM2_empty, compFinTM2Core]
        simpa [hEnd] using hLift

      -- Stitch stages, rewriting the intermediate configuration to match `embedRightCfg (initList ...)`.
      have hStage₁' :
          EvalsToInTime tm.step (initList tm input₁)
            (some
              (embedRightCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) h₁.tm.initialState none
                (fun _ => []) [] (initList h₂.tm input₂))) (h₁.time.eval n) := by
        -- The intermediate alphabet is empty, so the left output and right input stacks are both `[]`.
        have hMid :
            embedLeftCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ)
                (inrL (tm₁ := h₁.tm) (tm₂ := h₂.tm) h₂.tm.main) h₂.tm.initialState none (fun _ => []) []
                (haltList h₁.tm (List.map h₁.outputAlphabet.invFun (eβ.encode (f a)))) =
              embedRightCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) h₁.tm.initialState none (fun _ => []) []
                (initList h₂.tm input₂) := by
          apply cfg_eq_of_fields
          · simp [embedLeftCfg, embedRightCfg, haltList_l, initList_l]
          · simp [embedLeftCfg, embedRightCfg, haltList_var, initList_var]
          ·
            funext k
            cases k with
            | inl k =>
                cases k with
                | inl k =>
                    -- left stacks are empty since `hOutput₁` forces the output list to be `[]`.
                    by_cases hk : k = h₁.tm.k₁
                    · subst hk
                      simp [embedLeftCfg, embedRightCfg, compStk, haltList_stk_eq_update, initList_stk_eq_update,
                        hOutput₁, hEncβ]
                    ·
                      simp [embedLeftCfg, embedRightCfg, compStk, haltList_stk_eq_update, initList_stk_eq_update,
                        hOutput₁, hk]
                | inr k =>
                    -- right stacks are empty since `input₂ = []`.
                    simp [embedLeftCfg, embedRightCfg, compStk, initList_stk_eq_update, input₂]
            | inr u =>
                cases u
                simp [embedLeftCfg, embedRightCfg, compStk]
        refine
          { steps := hStage₁.steps
            evals_in_steps := ?_
            steps_le_m := hStage₁.steps_le_m }
        -- Rewrite the terminal configuration using `hMid`.
        refine Eq.trans hStage₁.evals_in_steps ?_
        exact congrArg some hMid

      have h12 :=
        EvalsToInTime.trans (f := tm.step) (h₁.time.eval n) (h₂.time.eval 0)
          (initList tm input₁)
          (embedRightCfg (tm₁ := h₁.tm) (tm₂ := h₂.tm) (Γβ := eβ.Γ) h₁.tm.initialState none (fun _ => []) []
            (initList h₂.tm input₂))
          (some (haltList tm out₂))
          hStage₁' hStage₂raw

      -- Widen to the declared polynomial time bound.
      refine evalsToInTime_mono (h := h12) (hm := ?_)
      -- `h12` has bound `h₂.time.eval 0 + h₁.time.eval n`; `time.eval n` is larger.
      have : h₂.time.eval 0 + h₁.time.eval n ≤ time.eval n := by
        -- First, use monotonicity to compare `h₂.time.eval 0` with `h₂.time.eval (q.eval n)`.
        have hbd : h₂.time.eval 0 ≤ h₂.time.eval (q.eval n) :=
          (Polynomial.eval_monotone_nat (p := h₂.time)) (Nat.zero_le (q.eval n))
        -- Expand the declared bound and solve by simple arithmetic.
        -- After rewriting, the goal is of the form `b + a ≤ 2 + (a + (c + d))`.
        simpa [time, timeCopy, timeH₂, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
          (by
            have hbda : h₂.time.eval 0 + h₁.time.eval n ≤ h₂.time.eval (q.eval n) + h₁.time.eval n :=
              Nat.add_le_add_right hbd (h₁.time.eval n)
            have hcomm : h₂.time.eval (q.eval n) + h₁.time.eval n = h₁.time.eval n + h₂.time.eval (q.eval n) := by
              simp [Nat.add_comm]
            have hd : h₂.time.eval (q.eval n) ≤ 2 * q.eval n + h₂.time.eval (q.eval n) :=
              Nat.le_add_left _ _
            have had :
                h₁.time.eval n + h₂.time.eval (q.eval n) ≤ h₁.time.eval n + (2 * q.eval n + h₂.time.eval (q.eval n)) := by
              simpa [Nat.add_assoc] using (Nat.add_le_add_left hd (h₁.time.eval n))
            have h2 :
                h₁.time.eval n + (2 * q.eval n + h₂.time.eval (q.eval n)) ≤
                  2 + (h₁.time.eval n + (2 * q.eval n + h₂.time.eval (q.eval n))) := by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                (Nat.le_add_left (h₁.time.eval n + (2 * q.eval n + h₂.time.eval (q.eval n))) 2)
            have hda :
                h₂.time.eval (q.eval n) + h₁.time.eval n ≤
                  2 + (h₁.time.eval n + (2 * q.eval n + h₂.time.eval (q.eval n))) := by
              have :
                  h₁.time.eval n + h₂.time.eval (q.eval n) ≤
                    2 + (h₁.time.eval n + (2 * q.eval n + h₂.time.eval (q.eval n))) :=
                le_trans (le_trans had h2) (le_rfl)
              simpa [hcomm] using this
            exact le_trans hbda hda)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

end Composition

end Turing

end Millennium
