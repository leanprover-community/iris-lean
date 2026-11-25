/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang, Michael Sammler
-/

module

public import Iris.BI
public import Iris.BI.BigOp.BigSepMSet
public import Iris.ProofMode
public import ITree.Definition
public import ITree.Exec
public import IrisITree.Core.LfpTp

public section

local stepindex Nat

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
    -- Main continuation with the postcondition, must be used at most once
    (E.O i → PROP) →
    -- Continuation for without postcondition, can be used multiple times (e.g., for spawning threads)
    (E.O i → PROP) →
    PROP
  ihandle_mono : ∀ (i : E.I) (Φ Φ' s s' : E.O i → PROP),
    (∀ a, Φ a -∗ Φ' a) -∗
    □ (∀ t, s t -∗ s' t) -∗
    ihandle i Φ s -∗ ihandle i Φ' s'

instance {PROP E} [BI PROP] (H : IHandler PROP E) (i : E.I) :
    OFE.NonExpansive₂ (H.ihandle i) := by
  -- TODO automate this
  constructor
  intro n Φ₁ Φ₂ HΦ s₁ s₂ Hs
  have Hmon : ∀ Φ s, H.ihandle i Φ s = iprop(∃ Φ' s', (∀ a, Φ' a -∗ Φ a) ∗ □ (∀ a, s' a -∗ s a) ∗ H.ihandle i Φ' s') := by
    iintro %Φ %s; isplit
    · iintro Hwand; iexists Φ, s; isplitr
      · iintro %a $
      · iframe
        iintro !> %a $
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
  ihandle e Φ s := match e with
    | .inl i₁ => H₁.ihandle i₁ Φ s
    | .inr i₂ => H₂.ihandle i₂ Φ s
  ihandle_mono := by
    iintro %e %Φ %Φ' %s %s' HΦwand #Hswand HH
    cases e
    · iapply H₁.ihandle_mono $$ HΦwand Hswand HH
    · iapply H₂.ihandle_mono $$ HΦwand Hswand HH
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

instance {E} (H : IHandler PROP E) : InH H H := ⟨fun _ _ _ => .rfl⟩

instance {E₁ E₂ E₃} [f : E₁ -< E₂]
    (H1 : IHandler PROP E₁) (H2 : IHandler PROP E₂) (H3 : IHandler PROP E₃)
    [Hin : InH H1 H2] : InH H1 (H2 ⊕ₕ H3) := ⟨fun i Φ s => Hin.is_inH i Φ s⟩

instance {E₁ E₂ E₃} [f : E₁ -< E₃]
    (H1 : IHandler PROP E₁) (H2 : IHandler PROP E₂) (H3 : IHandler PROP E₃)
    [Hin : InH H1 H3] : InH H1 (H2 ⊕ₕ H3) := ⟨fun i Φ s => Hin.is_inH i Φ s⟩

end handler_InH

section handler_WandH
variable {PROP : Type _} [BI PROP]

/-- `WandH H1 H2` means that `H1` implies `H2` -/
class WandH {E} (H1 : IHandler PROP E) (H2 : IHandler PROP E) where
  is_wandH : ∀ (i : E.I) (Φ s : E.O i → PROP),
    H1.ihandle i Φ s -∗ H2.ihandle i Φ s

instance {E} (H : IHandler PROP E) : WandH H H := by
  constructor
  iintro %i %Φ %s $

instance {E₁ E₂} (H1 H1' : IHandler PROP E₁) (H2 H2' : IHandler PROP E₂)
    [Hwand1 : WandH H1 H1'] [Hwand2 : WandH H2 H2'] :
    WandH (H1 ⊕ₕ H2) (H1' ⊕ₕ H2') := by
  constructor
  iintro %e %Φ %s H
  cases e with
  | inl e1 => simp only [sumH_inl]; iapply Hwand1.is_wandH $$ H
  | inr e2 => simp only [sumH_inr]; iapply Hwand2.is_wandH $$ H

end handler_WandH

section handler_Sequential
variable {PROP : Type _} [BI PROP]

/-- `Sequential` handlers ignore the spawning continuation and do not model concurrency. -/
class Sequential {E : Effect} (H : IHandler PROP E) where
  is_seq : ∀ (i : E.I) (Φ s : E.O i → PROP),
    H.ihandle i Φ s -∗ H.ihandle i Φ (fun _ => iprop% False)

instance {E₁ E₂} (H1 : IHandler PROP E₁) (H2 : IHandler PROP E₂)
    [Hs1 : Sequential H1] [Hs2 : Sequential H2] : Sequential (H1 ⊕ₕ H2) := by
  constructor
  iintro %e %Φ %s H
  cases e with
  | inl e1 => simp only [sumH_inl]; iapply Hs1.is_seq $$ H
  | inr e2 => simp only [sumH_inr]; iapply Hs2.is_seq $$ H

end handler_Sequential

section adequate
open ITree.Exec Iris.Std
variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

/-- Logical adequacy interface for executable handlers,
    with an invariant over the state and the pending thread pool. -/
class EHandlerAdequate {E GE : Effect} {R σ : Type _}
    (IH : IHandler PROP E) (EH : EHandler E GE R σ) where
  inv : σ → ListPerm ((ITree GE R → PROP) → PROP) → PROP
  adequate :
    ∀ (G : ITree GE R → PROP) (i : E.I) (s : σ)
      (Ms : ListPerm ((ITree GE R → PROP) → PROP))
      (C : ITree GE R → σ → Prop) (k : E.O i → ITree GE R),
      EH.handle i s k C →
      IH.ihandle i (fun a => G (k a)) (fun a => G (k a)) -∗
      inv s Ms -∗
      |={∅}=> ∃ t s' M' Ms' Msn, <affine> ⌜C t s'⌝ ∗
        <affine> ⌜{M'} ⊎ Ms' = Msn ⊎ Ms⌝ ∗
        ([∗mset] M ∈ Msn, M G) ∗ inv s' Ms' ∗
        (∀ P, M' P ={∅}=∗ P t)

/-- Logical adequacy interface for simple executable handlers. -/
class SEHandlerAdequate {E : Effect} {σ : Type _}
    (IH : IHandler PROP E) (EH : SEHandler E σ) where
  inv : σ → PROP
  adequate :
    ∀ (i : E.I) (s : σ) (C : E.O i → σ → Prop) (Φ1 Φ2 : E.O i → PROP),
      EH.handle i s C →
      IH.ihandle i Φ1 Φ2 -∗
      inv s -∗
      |={∅}=> ∃ a s', <affine> ⌜C a s'⌝ ∗ inv s' ∗ Φ1 a

instance EH_of_SEH_adequate {E GE : Effect} {R σ : Type _}
    (H : IHandler PROP E) (EH : SEHandler E σ)
    [A : SEHandlerAdequate H EH] :
    EHandlerAdequate H (EH : EHandler E GE R σ) where
  inv s Ms := iprop% <affine> ⌜Ms = ∅⌝ ∗ A.inv s
  adequate := by
    intro G i s Ms C k Hhandle
    simp at Hhandle
    iintro Hh ⟨%rfl, Hinv⟩
    imod A.adequate _ _ _ _ _ Hhandle $$ Hh Hinv with ⟨%a, %s', %HC, Hinv, Ha⟩
    imodintro
    iexists k a, s', fun P => P (k a), ∅, {fun P => P (k a)}
    rw [BigSepMS.bigSepMS_singleton.to_eq, disjUnion_empty_right]
    iframe %HC Hinv Ha
    isplit
    · itrivial
    isplit
    · itrivial
    iintro %_ $ !> //

/-- Independent simple handlers preserve the separating conjunction of their invariants. -/
instance sumSEH_adequate {E₁ E₂ : Effect} {S₁ S₂ : Type _}
    (H₁ : IHandler PROP E₁) (H₂ : IHandler PROP E₂)
    (EH₁ : SEHandler E₁ S₁) (EH₂ : SEHandler E₂ S₂)
    [A₁ : SEHandlerAdequate H₁ EH₁] [A₂ : SEHandlerAdequate H₂ EH₂] :
    SEHandlerAdequate (H₁ ⊕ₕ H₂) (EH₁ ⊕ₛₑₕ EH₂) where
  inv s := iprop% A₁.inv s.1 ∗ A₂.inv s.2
  adequate :=by
    iintro %i %⟨s1, s2⟩ %C %Φ1 %Φ2 %Hse
    cases i with
    | inl i =>
      simp only [sumH_inl, sumSEH] at ⊢ Hse
      iintro Hh ⟨Hinv1, Hinv2⟩
      imod A₁.adequate _ _ _ _ _ Hse $$ Hh Hinv1 with ⟨%a, %s', %HC, Hinv1, HΦ1⟩
      imodintro
      iexists a, (s', s2)
      iframe %HC Hinv1 Hinv2 HΦ1
    | inr i =>
      simp only [sumH_inr, sumSEH] at ⊢ Hse
      iintro Hh ⟨Hinv1, Hinv2⟩
      imod A₂.adequate _ _ _ _ _ Hse $$ Hh Hinv2 with ⟨%a, %s', %HC, Hinv2, HΦ2⟩
      imodintro
      iexists a, (s1, s')
      iframe %HC Hinv1 Hinv2 HΦ2

/-- Two thread-pool handlers: the pending threads are split between their invariants. -/
instance sumEEH_adequate {E₁ E₂ GE : Effect} {R S₁ S₂ : Type _}
    (H₁ : IHandler PROP E₁) (H₂ : IHandler PROP E₂)
    (EH₁ : EHandler E₁ GE R S₁) (EH₂ : EHandler E₂ GE R S₂)
    [A₁ : EHandlerAdequate H₁ EH₁] [A₂ : EHandlerAdequate H₂ EH₂] :
    EHandlerAdequate (H₁ ⊕ₕ H₂) (EH₁ ⊕ₑₕ EH₂) where
  inv s Ms := iprop% ∃ Ms1 Ms2, <affine> ⌜Ms = Ms1 ⊎ Ms2⌝ ∗ A₁.inv s.1 Ms1 ∗ A₂.inv s.2 Ms2
  adequate := by
    intro G i ⟨s1, s2⟩ Ms C k Heh
    cases i with
    | inl i =>
      simp only [sumH_inl]; iintro Hh ⟨%Ms1, %Ms2, ⟨%Hsplit, Hinv1, Hinv2⟩⟩
      imod A₁.adequate _ _ _ _ _ _ Heh $$ Hh Hinv1 with
        ⟨%t', %s', %M', %Ms₁', %Msn, HC, %Hperm, Hspawn, Hinv1, Hclose⟩
      imodintro
      iexists t', (s', s2), M', Ms₁' ⊎ Ms2, Msn
      iframe
      ipureintro; grind
    | inr i =>
      simp only [sumH_inr]; iintro Hh ⟨%Ms1, %Ms2, ⟨%Hsplit, Hinv1, Hinv2⟩⟩
      imod A₂.adequate _ _ _ _ _ _ Heh $$ Hh Hinv2 with
        ⟨%t', %s', %M', %Ms₂', %Msn, HC, %Hperm, Hspawn, Hinv2, Hclose⟩
      imodintro
      iexists t', (s1, s'), M', Ms1 ⊎ Ms₂', Msn
      iframe
      ipureintro; grind

/-- Adequacy is preserved by an isomorphism of executable states. -/
instance isoEH_adequate {E GE : Effect} {R S₁ S₂ : Type _}
    (iso : Iso S₁ S₂) (H : IHandler PROP E) (EH : EHandler E GE R S₁)
    [A : EHandlerAdequate H EH] : EHandlerAdequate H (isoEH iso EH) where
  inv s Ms := A.inv (iso.invFun s) Ms
  adequate := by
    intro G i s Ms C k Heh
    iintro Hh Hinv
    imod A.adequate _ _ _ _ _ _ Heh $$ Hh Hinv with
      ⟨%t', %s', %M', %Ms', %Msn, HC, Hperm, HMsn, Hinv', Hpre⟩
    imodintro
    iexists t', iso.toFun s', M', Ms', Msn
    simp only [invFun_toFun]
    iframe HC Hperm HMsn Hinv' Hpre


end adequate

end IrisITree
