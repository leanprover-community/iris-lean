module

public import Iris.BI
public import Iris.ProofMode
public import ITree.Definition
public import ITree.Exec

public section

namespace IrisITree

open Iris BI ITree

/--
  An `IHandler` is the user-specified recipe used to define a custom weakest precondition `WPi`.
  It specifies how to interpret an effect logically, given weakest preconditions for
  continuations of the itree.
-/
structure IHandler (PROP : Type u) [BI PROP] (E : Effect.{v}) where
  ihandle :
    (i : E.I) →
    -- Continuation conditions `λ a, ▷ WPi k a @ H; ∅ {{ Φ }}`
    (E.O i → PROP) →
    -- Conditions for spawning threads `λ a, ▷ WPi k a @ H; ⊤ {{ False }}`
    (E.O i → PROP) →
    -- Condition `WPi (Vis i k) @ H; ∅ {{ Φ }}`
    PROP

  ihandle_mono : ∀ (i : E.I) (Φ Φ' s s' : E.O i → PROP),
    (∀ a, Φ a -∗ Φ' a) -∗
    □ (∀ t, s t -∗ s' t) -∗
    ihandle i Φ s -∗ ihandle i Φ' s'

instance {PROP E} [BI PROP] (H : IHandler PROP E) (i : E.I) :
    OFE.NonExpansive₂ (H.ihandle i) := by
  constructor
  intro n Φ₁ Φ₂ HΦ s₁ s₂ Hs
  have Hmon : ∀ Φ s, H.ihandle i Φ s = iprop(∃ Φ' s', (∀ a, Φ' a -∗ Φ a) ∗ □ (∀ a, s' a -∗ s a) ∗ H.ihandle i Φ' s') := by
    iintro %Φ %s; isplit
    · iintro Hwand; iexists Φ, s; isplitr;
      · iintro %a $
      · isplitr; imodintro;
        iintro %a $; iexact Hwand
    · iintro ⟨%Φ', ⟨%s', ⟨HmonΦ, ⟨Hmons, HH⟩⟩⟩⟩
      iapply H.ihandle_mono $$ HmonΦ Hmons HH
  apply (Hmon Φ₁ s₁).dist.trans
  apply ((exists_ne fun Φ' => ?_)).trans (Hmon Φ₂ s₂).dist.symm
  refine exists_ne fun s' => sep_ne.ne ?_ <| sep_ne.ne ?_ .rfl
  · exact forall_ne fun a => wand_ne.ne .rfl (HΦ a)
  · exact intuitionistically_ne.ne <| forall_ne fun a => wand_ne.ne .rfl (Hs a)

section handler_sumH

variable {E₁ E₂} {PROP : Type _} [BI PROP] (H₁ : IHandler PROP E₁) (H₂ : IHandler PROP E₂)

/-- An [IHandler] for sum events [E₁ ⊕ₑ E₂] delegating to respective [IHandler]s. -/
@[expose]
def sumH : IHandler PROP (E₁ ⊕ₑ E₂) where
  ihandle := by
    intro e Φ s
    cases e with
    | inl e1 => exact H₁.ihandle e1 Φ s
    | inr e2 => exact H₂.ihandle e2 Φ s
  ihandle_mono := by
    iintro %e %Φ %Φ' %s %s' HΦwand #Hswand HH
    cases e with
    | inl e1 => iapply H₁.ihandle_mono $$ HΦwand Hswand HH
    | inr e2 => iapply H₂.ihandle_mono $$ HΦwand Hswand HH
infixr:30 " ⊕ₕ " => sumH

@[simp]
theorem sumH_inl (i : E₁.I) (Φ s) : (H₁ ⊕ₕ H₂).ihandle (.inl i) Φ s = H₁.ihandle i Φ s := rfl

@[simp]
theorem sumH_inr (i : E₂.I) (Φ s) : (H₁ ⊕ₕ H₂).ihandle (.inr i) Φ s = H₂.ihandle i Φ s := rfl

end handler_sumH

section handler_InH

variable {PROP : Type _} [BI PROP]

/-- `InH H1 H2` means that `H1` is equivalent to `H2` on events `E1`. -/
class InH {E₁ E₂} [Hsub : E₁ -< E₂]
    (H1 : outParam (IHandler PROP E₁)) (H2 : IHandler PROP E₂) where
  is_inH : ∀ (i₁ : E₁.I) (Φ₁ s₁ : E₁.O i₁ → PROP),
    let ⟨i₂, f⟩ := Hsub.map i₁
    let Φ₂ := fun x => Φ₁ <| f x
    let s₂ := fun x => s₁ <| f x
    H1.ihandle i₁ Φ₁ s₁ ⊣⊢ H2.ihandle i₂ Φ₂ s₂

instance {PROP E} [BI PROP] (H : IHandler PROP E) : InH H H := by
  constructor
  intro i Φ s
  change H.ihandle i Φ s ⊣⊢ H.ihandle i Φ s
  exact .rfl

instance {PROP E₁ E₂ E₃} [BI PROP] [f : E₁ -< E₂]
    (H1 : IHandler PROP E₁) (H2 : IHandler PROP E₂) (H3 : IHandler PROP E₃)
    [Hin : InH H1 H2] : InH H1 (H2 ⊕ₕ H3) := by
  constructor
  intro i Φ s
  exact Hin.is_inH i Φ s

instance {PROP E₁ E₂ E₃} [BI PROP] [f : E₁ -< E₃]
    (H1 : IHandler PROP E₁) (H2 : IHandler PROP E₂) (H3 : IHandler PROP E₃)
    [Hin : InH H1 H3] : InH H1 (H2 ⊕ₕ H3) := by
  constructor
  intro i Φ s
  exact Hin.is_inH i Φ s

end handler_InH

section handler_WandH

/-- `WandH H1 H2` means that `H1` implies `H2` -/
class WandH {PROP E} [BI PROP] (H1 : IHandler PROP E) (H2 : IHandler PROP E) where
  is_wandH : ∀ (i : E.I) (Φ s : E.O i → PROP),
    H1.ihandle i Φ s -∗ H2.ihandle i Φ s

instance {PROP E} [BI PROP] (H : IHandler PROP E) : WandH H H := by
  constructor
  iintro %i %Φ %s H
  iexact H

instance {PROP E₁ E₂} [BI PROP]
    (H1 H1' : IHandler PROP E₁) (H2 H2' : IHandler PROP E₂)
    [Hwand1 : WandH H1 H1'] [Hwand2 : WandH H2 H2'] :
    WandH (H1 ⊕ₕ H2) (H1' ⊕ₕ H2') := by
  constructor
  iintro %e %Φ %s H
  cases e with
  | inl e1 => simp only [sumH_inl]; iapply Hwand1.is_wandH $$ H
  | inr e2 => simp only [sumH_inr]; iapply Hwand2.is_wandH $$ H

end handler_WandH

section handler_Sequential

/-- `Sequential` handlers ignore the spawning continuation and do not model concurrency. -/
class Sequential {PROP} [BI PROP] {E : Effect} (H : IHandler PROP E) where
  is_seq : ∀ (i : E.I) (Φ s : E.O i → PROP),
    H.ihandle i Φ s -∗ H.ihandle i Φ (fun _ => iprop(⌜False⌝))

instance {PROP E₁ E₂} [BI PROP]
    (H1 : IHandler PROP E₁) (H2 : IHandler PROP E₂)
    [Hs1 : Sequential H1] [Hs2 : Sequential H2] : Sequential (H1 ⊕ₕ H2) := by
  constructor
  iintro %e %Φ %s H
  cases e with
  | inl e1 => simp only [sumH_inl]; iapply Hs1.is_seq $$ H
  | inr e2 => simp only [sumH_inr]; iapply Hs2.is_seq $$ H

end handler_Sequential

section adequate
open ITree.Exec

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

/-- Logical adequacy interface for executable handlers, with an invariant over the state and the pending thread pool. -/
class EHandlerAdequate {E GE : Effect.{u}} {R σ : Type _}
    (H : IHandler PROP E) (EH : EHandler E GE R σ) where
  inv : σ → List (((ITree GE R → PROP) → PROP)) → PROP
  adequate :
    ∀ (G : ITree GE R → PROP) (i : E.I) (s : σ)
      (Ms : List (((ITree GE R → PROP) → PROP)))
      (C : ITree GE R → σ → Prop) (k : E.O i → ITree GE R),
      EH.handle i s k C →
      H.ihandle i (fun a => G (k a)) (fun a => G (k a)) -∗
      inv s Ms -∗
      |={∅}=> ∃ t' s' M' Ms' Msn, <affine> ⌜C t' s'⌝ ∗
        <affine> ⌜(M' :: Ms').Perm (Msn ++ Ms)⌝ ∗
        ([∗list] M ∈ Msn, M G) ∗ inv s' Ms' ∗
        (∀ P, M' P ={∅}=∗ P t')

/-- Logical adequacy interface for simple executable handlers. -/
class SEHandlerAdequate {E : Effect.{_}} {σ : Type _}
    (H : IHandler PROP E) (EH : SEHandler E σ) where
  inv : σ → PROP
  adequate :
    ∀ (i : E.I) (s : σ) (C : E.O i → σ → Prop) (Φ1 Φ2 : E.O i → PROP),
      EH.handle i s C →
      H.ihandle i Φ1 Φ2 ⊢
      inv s -∗
      |={∅}=> ∃ a s', <affine> ⌜C a s'⌝ ∗ inv s' ∗ Φ1 a

instance {E GE : Effect.{u}} {R σ : Type _}
    (H : IHandler PROP E) (EH : SEHandler E σ)
    [A : SEHandlerAdequate H EH] :
    EHandlerAdequate H (EH : EHandler E GE R σ) where
  inv s _ := A.inv s
  adequate := by
    intro G i s Ms C k H0; simp at H0
    iintro Hh Hinv
    ihave >⟨%a, %s', %_, _, _⟩ := A.adequate $$ Hh [$]; assumption
    imodintro; iexists (k a), _, (fun P => P (k a)), Ms, [fun P => P (k a)]
    iframe; isplitr; itrivial
    isplitr; itrivial
    simp; iframe; isplitr; itrivial
    iintro %_ $ !> //

end adequate

end IrisITree
