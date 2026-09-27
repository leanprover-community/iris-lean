/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import IrisMath.NaturalSum
public import IrisMath.Transfinite
public import Iris

/-! # Ordinal time credits (Transfinite Iris)

This file ports `ord_auth_source` of `theories/program_logic/refinement/ref_source.v` and
`theories/program_logic/refinement/tc_weakestpre.v` of Transfinite Iris: ordinal time credits
`tc α` (Rocq: `$ α`) and the time-credit weakest precondition `tcwp` (Rocq: `WP e [{ Φ }]`), which
is the refinement weakest precondition for the source of ordinals ordered by `>`. Termination
follows from the well-foundedness of the ordinals (`tcwp_adequacy`).

## Universes

The source states are ordinals `Ordinal.{w}`, while the camera carrier `OrdCam SI` lives in the
universe of the step-indices. Adequacy uses the existential property of satisfiability for the
source states, which requires `SIdxLarge.{w + 1} SI`, e.g. `SI = Ordinal.{w + 1}`.
-/

@[expose] public noncomputable section

universe w v u

namespace Iris.Transfinite

open _root_.Std (Associative Commutative LeftIdentity LawfulLeftIdentity)
open Iris Iris.Std Iris.BI OFE CMRA Ordinal ProgramLogic Language Relation

/-- Ordinals under the natural sum, as a camera over the step-index type `SI` (Rocq: `OrdR`). -/
@[ext] structure OrdCam (SI : Type v) : Type (max v (w + 1)) where
  o : Ordinal.{w}

section Camera

variable {SI : Type v} [instSI : Iris.SIdx SI]
local stepindex SI

namespace OrdCam

instance : Add (OrdCam.{w} SI) := ⟨fun a b => ⟨a.o ♯ b.o⟩⟩
instance : Zero (OrdCam.{w} SI) := ⟨⟨0⟩⟩

instance : Associative (α := OrdCam.{w} SI) (· + ·) :=
  ⟨fun _ _ _ => OrdCam.ext (nadd_assoc _ _ _)⟩
instance : Commutative (α := OrdCam.{w} SI) (· + ·) := ⟨fun _ _ => OrdCam.ext (nadd_comm _ _)⟩
instance : LeftIdentity (α := OrdCam.{w} SI) (· + ·) (0 : OrdCam.{w} SI) where
instance : LawfulLeftIdentity (α := OrdCam.{w} SI) (· + ·) (0 : OrdCam.{w} SI) :=
  ⟨fun _ => OrdCam.ext (zero_nadd _)⟩

instance : COFE (OrdCam.{w} SI) := COFE.ofDiscrete _
instance : OFE.Discrete (OrdCam.{w} SI) := ⟨fun h => h⟩
instance : UCMRA (OrdCam.{w} SI) := CommMonoidLike.instUCMRA
instance : CMRA.Discrete (OrdCam.{w} SI) := CommMonoidLike.instDiscrete
instance : CMRA.CoreId (0 : OrdCam.{w} SI) := CommMonoidLike.instCoreIdZero
instance : CMRA.CoreId (⟨0⟩ : OrdCam.{w} SI) := CommMonoidLike.instCoreIdZero

theorem op_o (a b : OrdCam.{w} SI) : (a • b).o = a.o ♯ b.o := rfl

theorem unit_eq : (UCMRA.unit : OrdCam.{w} SI) = ⟨0⟩ := rfl

end OrdCam

end Camera

variable {SI : Type v} [instSI : Iris.SIdx SI]
local stepindex SI

/-- The ghost state of time credits (Rocq: `tcG`, i.e. `auth_sourceG Σ ordA`). -/
class TcGS (GF : BundledGFunctors.{u}) where
  elem : ElemG GF (constOFU.{max u v} (Auth (OrdCam.{w} SI)))
  name : GName

attribute [reducible, instance] TcGS.elem

variable {GF : BundledGFunctors.{u}} [G : TcGS.{w} GF]

/-- The authoritative time-credit budget (Rocq: `●$ α`). -/
def tcAuth (α : Ordinal.{w}) : IProp GF :=
  iOwn (E := G.elem) G.name (ULift.up (● (⟨α⟩ : OrdCam.{w} SI)))

/-- Time credits (Rocq: `$ α`). -/
def tc (α : Ordinal.{w}) : IProp GF :=
  iOwn (E := G.elem) G.name (ULift.up (◯ (⟨α⟩ : OrdCam.{w} SI)))

/-- The ordinal source: a source step strictly decreases the ordinal (Rocq: `ordA`,
`ord_credit`). -/
instance tcSource : Source GF Ordinal.{w} where
  rel a b := b < a
  interp := tcAuth

/-- Rocq: `tc_split`. -/
theorem tc_split (α β : Ordinal.{w}) : tc (GF := GF) (α ♯ β) ⊣⊢ tc α ∗ tc β := by
  unfold tc
  rw [show (◯ (⟨α ♯ β⟩ : OrdCam.{w} SI) : Auth (OrdCam.{w} SI)) =
    (◯ (⟨α⟩ : OrdCam.{w} SI)) • (◯ (⟨β⟩ : OrdCam.{w} SI)) from Auth.frag_op, ULift.up_op]
  exact iOwn_op

/-- Rocq: `tc_succ`. -/
theorem tc_succ (α : Ordinal.{w}) : tc (GF := GF) (Order.succ α) ⊣⊢ tc α ∗ tc 1 := by
  rw [← nadd_one]
  exact tc_split α 1

instance tc_timeless (α : Ordinal.{w}) : Timeless (tc (GF := GF) α) := by
  unfold tc
  infer_instance

instance zero_persistent : Persistent (tc (GF := GF) 0) := by
  unfold tc
  haveI : CMRA.CoreId (α := (constOFU.{max u v} (Auth (OrdCam.{w} SI))).ap (IProp GF))
      (ULift.up (◯ (⟨0⟩ : OrdCam.{w} SI))) := ULift.instCoreId
  infer_instance

section Update

variable [W : WsatGS GF]

/-- Spending time credits is a source step (Rocq: `auth_src_update` for `ordA`). -/
theorem tc_update (E : CoPset) {α β : Ordinal.{w}} (h : β < α) :
    tc (GF := GF) α ⊢ srcUpdate (src := tcSource) E (tc β) := by
  unfold srcUpdate
  delta tcSource
  dsimp only
  unfold tcAuth tc
  iintro HF %A HA
  ihave H := (iOwn_op (E := G.elem) (γ := G.name) (a1 := ULift.up (● (⟨A⟩ : OrdCam.{w} SI)))
    (a2 := ULift.up (◯ (⟨α⟩ : OrdCam.{w} SI)))).mpr $$ [HA HF]
  · iframe
  ihave ⟨Hv, H⟩ := iOwn_valid_l $$ H
  icases internalCmraValid_discrete.mp $$ Hv with %Hv
  obtain ⟨⟨f, hf⟩, -⟩ := Auth.auth_both_valid_discrete.mp Hv
  have hA : A = α ♯ f.o := congrArg OrdCam.o hf
  have hlu : ((⟨A⟩ : OrdCam.{w} SI), (⟨α⟩ : OrdCam.{w} SI)) ~l~> (⟨β ♯ f.o⟩, ⟨β⟩) := by
    refine (local_update_unital_discrete _ _ _ _).mpr fun z _ hz => ⟨trivial, ?_⟩
    have hz' : A = α ♯ z.o := congrArg OrdCam.o hz
    have : f.o = z.o := nadd_left_cancel (hA.symm.trans hz')
    exact OrdCam.ext (by rw [OrdCam.op_o, this])
  imod iOwn_update (ULift.update (Auth.auth_update hlu)) $$ H with H
  icases (iOwn_op (E := G.elem)).mp $$ H with ⟨HA, HF⟩
  iapply fupd_intro
  iexists (β ♯ f.o)
  iframe
  ipureintro
  exact .single (hA ▸ nadd_lt_nadd_right h f.o)

end Update

/-! ## The time-credit weakest precondition -/

variable {Expr State Obs Val : Type _} [Λ : Language Expr State Obs Val] [ι : RefIrisGS Expr GF]
variable {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF}

/-- The time-credit weakest precondition (Rocq: `tcwp`, notation `WP e @ s; E [{ Φ }]`). -/
abbrev tcwp (s : Stuckness) (E : CoPset) (e : Expr) (Φ : Val → IProp GF) : IProp GF :=
  rwp (src := tcSource) (ι := ι) s E e Φ

instance hlwp_tcwp [ι : RefIrisGS HeapLang.Exp GF] {s : Stuckness} {E : CoPset} :
    HLWp (tcwp (G := G) (ι := ι) s E) (tcwp (G := G) (ι := ι) s E) := hlwp_rwp

instance hlwpValue_tcwp [ι : RefIrisGS HeapLang.Exp GF] {s : Stuckness} {E : CoPset} :
    HLWpValue (tcwp (G := G) (ι := ι) s E) := hlwpValue_rwp

/-- Rocq: `tcwp_burn_credit`. -/
theorem tcwp_burn_credit (he : toVal e = none) :
    ⊢ tc (GF := GF) 1 -∗ ▷ rswp (src := tcSource) (ι := ι) 0 s E e Φ -∗ tcwp (ι := ι) s E e Φ := by
  iintro Hone Hwp
  iapply rwp_take_step (P := tc (GF := GF) 0) he $$ [Hwp] [Hone]
  · iintro -
    iapply rswp_do_step
    iexact Hwp
  · iapply tc_update E zero_lt_one $$ Hone

/-- Rocq: `tc_weaken`. -/
theorem tc_weaken {α β : Ordinal.{w}} (he : toVal e = none) (hβα : β ≤ α) :
    (tc (GF := GF) β -∗ tcwp (ι := ι) s E e Φ) ∗ tc α ⊢ tcwp (ι := ι) s E e Φ := by
  iintro ⟨Hwp, Hc⟩
  rcases lt_or_eq_of_le hβα with h | rfl
  · iapply rwp_weaken he $$ Hwp
    iapply tc_update E h $$ Hc
  · iapply Hwp $$ Hc

/-- Rocq: `tc_alloc_zero`. -/
theorem tc_alloc_zero :
    (tc (GF := GF) 0 -∗ tcwp (ι := ι) s E e Φ) ⊢ tcwp (ι := ι) s E e Φ := by
  iintro H
  iapply fupd_rwp
  imod (iOwn_unit (E := G.elem) (γ := G.name) (ε := (UCMRA.unit : (constOFU.{max u v} (Auth (OrdCam.{w} SI))).ap (IProp GF))))
    with Hz
  have hunit : (UCMRA.unit : (constOFU.{max u v} (Auth (OrdCam.{w} SI))).ap (IProp GF)) =
      ULift.up (◯ (⟨0⟩ : OrdCam.{w} SI)) := rfl
  rw [hunit]
  imodintro
  iapply H
  unfold tc
  iexact Hz

/-- The ordinals are well-founded: the ordinal source is strongly normalizing. -/
theorem tcSource_sn (α : Ordinal.{w}) : StronglyNormalizing (tcSource (GF := GF)).rel α := by
  induction α using Ordinal.lt_wf.induction with
  | _ α IH => exact ⟨_, fun β h => IH β h⟩

/-- Time credits ensure termination (Rocq: `tcwp_adequacy`). -/
theorem tcwp_adequacy [SIdxLarge.{w + 1} SI] {α : Ordinal.{w}} {σ : State} {n : Nat}
    (hsat : satisfiableAt ⊤ iprop(tcAuth (GF := GF) α ∗ ι.refStateInterp σ n ∗
      tcwp (ι := ι) .NotStuck ⊤ e Φ))
    (hloop : ExLoop ErasedStep ([e], σ)) : False :=
  rwp_adequacy (src := tcSource) (tcSource_sn α) hloop hsat

end Iris.Transfinite
