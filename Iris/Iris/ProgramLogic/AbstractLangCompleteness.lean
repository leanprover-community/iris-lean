/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra
public import Iris.BI
public import Iris.ProofMode
public import Iris.ProgramLogic.Language
public import Iris.ProgramLogic.Adequacy
public import Iris.ProgramLogic.ThreadPool
public import Iris.ProgramLogic.AbstractWeakestPre
public import Iris.Instances.Lib.Invariants
public import Iris.Instances.Lib.CInvariants
public import Iris.Instances.Lib.GhostMap
public import Iris.Std.FromMathlib

namespace Iris.ProgramLogic

open Iris Iris.BI Iris.Algebra Std FromMathlib
open Iris.ProgramLogic.PrimStep
open Language Language.Notation

@[expose] public section

section AbstractCompleteness

variable {Expr State Obs Val : Type _} [Language Expr State Obs Val]
variable {GF : BundledGFunctors} {HLC : HasLC} [IrisGS_gen HLC Expr GF]
variable {F : Type _} [UFraction F]
variable {H : Type _ → Type _} [LawfulFiniteMap H Nat]
variable [TI : TpinvGS GF F Expr H]

public abbrev abstractECTXLangComplete (wp : AbstractWP Expr Val GF) (I : List Expr → State → IProp GF)
  (n : Nat) (C : List Expr) (e₁ : Expr) (σ : State) (E : CoPset) :
    IProp GF := iprop%
   ⌜PrimStep.Reducible (e₁, σ)⌝ -∗ (n ↪thread e₁) -∗ I C σ ∗ tpInv C ∗ ⌜cfgSafe (C, σ)⌝ ={E}=∗
   ((∃ (K : Expr → Expr) (e₁' : Expr),
       ⌜Context K⌝ ∗ ⌜e₁ = K e₁'⌝ ∗ ⌜ToVal.toVal e₁' = none⌝ ∗ ⌜Atomic .WeaklyAtomic e₁'⌝ ∗
       ∀ Ψ,
         (▷ ∀ κ v₂ σ' efs,
           ⌜PrimStep.primStep (e₁', σ) κ ((ToVal.ofVal v₂ : Expr), σ', efs)⌝ -∗
           (n ↪thread e₁) -∗
           tpInv C ==∗
           (I ((C.set n (K (ToVal.ofVal v₂))) ++ efs) σ' -∗ Ψ v₂) ∗
           [∗list] _i ↦ etp ∈ efs, wp ⊤ etp (fun (_ : Val) => iprop% True)) -∗
         wp E e₁' Ψ) ∨
     (I C σ ∗ tpInv C ∗ ∀ Ψ,
       (▷ ∀ e₂ efs,
         (∀ σ₁ C₁, I C₁ σ₁ ∗ tpInv C₁ ∗ ⌜cfgSafe (C₁, σ₁)⌝ ={E}=∗
            ∃ κ σ₁',
              ⌜PrimSteps e₁ σ₁ κ e₂ σ₁' efs⌝ ∗ (n ↪thread e₁) ∗ tpInv C₁ ∗
              I ((C₁.set n e₂) ++ efs) σ₁') ={⊤}=∗
           wp ⊤ e₂ Ψ ∗ ([∗list] _j ↦ etp ∈ efs, wp ⊤ etp (fun (_ : Val) => iprop% True))) -∗
       wp ⊤ e₁ Ψ))

/-- A weakest precondition for a Language is complete -/
public class AbstractLangCompletenessGen
    (wp : AbstractWP Expr Val GF) [LawfulAbstractWP wp] where
  heap_inv : List Expr → State → IProp GF
  heap_inv_timeless (C : List Expr) (σ : State) : Timeless (heap_inv C σ)
  lang_completeness {n C e₁ σ E} : ⊢ abstractECTXLangComplete wp heap_inv n C e₁ σ E

attribute [instance] AbstractLangCompletenessGen.heap_inv_timeless

end AbstractCompleteness

section Completeness

variable {Expr State Obs Val : Type _} [Language Expr State Obs Val]
variable {GF : BundledGFunctors} {HLC : HasLC} [IrisGS_gen HLC Expr GF]
variable {F : Type _} [UFraction F]
variable {H : Type _ → Type _} [LawfulFiniteMap H Nat]
variable [TI : TpinvGS GF F Expr H]
variable {wp : AbstractWP Expr Val GF}
variable [LWP : LawfulAbstractWP wp] [IAO : InvOpenAbstractWP wp]
variable [ACG : AbstractLangCompletenessGen wp]
variable [CInvG F GF]

/-- Namespace under which the completeness invariant lives. -/
public def completenessN : Namespace := nroot .@ (1 : Pos)

/-- The configuration invariant: ownership of a current configuration
(thread pool + state) reachable from the initial one, with the heap and
thread-pool invariants. -/
public def cfgInv (Cini : List Expr × State) (f : Forking) : IProp GF := iprop%
  ∃ cfg : List Expr × State,
    ACG.heap_inv cfg.1 cfg.2 ∗ tpInv cfg.1 ∗ ⌜cfgSafeForking cfg f⌝ ∗ ⌜Cini -·->ₜₚ* cfg⌝

/-- `cfgInv` is timeless: `heap_inv` is timeless by the class field, `tpInv` by
`tpInv_timeless`, and the reachability/safety conjunct is pure. This is what
lets the later be stripped off the invariant contents after opening it. -/
instance cfgInv_timeless (Cini : List Expr × State) (f : Forking) :
    Timeless (cfgInv (wp := wp) Cini f) := by
  unfold cfgInv; infer_instance

/-- Cancelable invariant package wrapping `cfgInv`. -/
public def isCcfg (Cini : List Expr × State) (f : Forking) (γ : GName) : IProp GF :=
  CancelableInvariant.cinv (F := F) completenessN γ (cfgInv (wp := wp) Cini f)

instance isCcfg_persistent (Cini : List Expr × State) (f : Forking) (γ : GName) :
    Persistent (isCcfg (wp := wp) Cini f γ : IProp GF) := by
  unfold isCcfg; infer_instance

theorem weakestpre_completeness
    (Cini : List Expr × State) (f : Forking) (γ : GName) (q : Frac F)
    (n : Nat) (e : Expr) :
    isCcfg (TI := TI) (wp := wp) Cini f γ -∗
    CancelableInvariant.own γ q -∗
    isThread (TI := TI) n (.own 1) e -∗
    wp ⊤ e (fun v => iprop%
        isThread (TI := TI) n (.own 1) (ToVal.ofVal v) ∗
        ∃ q' : Frac F, CancelableInvariant.own γ q' ∗ ⌜f = .doesNotFork → q = q'⌝) := by
  iintro #Hinv
  iloeb as IH generalizing %q %n %e
  iintro Hq He
  have Hn : nclose completenessN ⊆ ⊤ := sorry -- TODO Solve then inline?
  have Hn' : ⊤ \ nclose completenessN ⊆ ⊤ := sorry -- TODO Solve then inline?
  iapply IAO.inv_open_maybe (E₂ := ⊤ \ nclose completenessN) _ _ _ Hn'
  unfold isCcfg
  imod CancelableInvariant.acc _ _ _ _ _ Hn $$ [$] [$] with ⟨>Hinv2, Hq, Hclose⟩
  unfold cfgInv
  icases Hinv2 with ⟨%cfg, Hheap, HtpInv, %Hx⟩
  rcases Hx with ⟨Hsafe, Hreach⟩
  ihave %Hlu := tpInv_lookup $$ [$] [$]
  have ⟨HnotStuck, Hforking⟩ := Hsafe .refl
  rcases HnotStuck (List.mem_of_getElem? Hlu) with Hv|HnotStuck'
  · replace ⟨v, Hv⟩ := Option.isSome_iff_exists.mp Hv
    obtain rfl := (coe_of_toVal_eq_some Hv).symm; clear Hv
    imodintro
    ileft
    -- TODO: Can iframe be improved to supply these directly?
    have Hframe1 : Context (Expr := Expr) id := by infer_instance
    have Hframe2 : (↑v : Expr) = id ↑v := rfl
    have Hframe3 : Atomic Atomicity.WeaklyAtomic (↑v : Expr) := val_atomic
    iexists id, v
    iframe %Hframe1 %Hframe2 %Hframe3
    clear Hframe1 Hframe2 Hframe3
    simp only [id_eq]
    iapply LWP.wp_value
    imodintro
    imod Hclose $$ [HtpInv Hheap] with -
    · inext
      iexists cfg
      iframe Hheap HtpInv %Hreach %Hsafe
    · imodintro
      iapply LWP.wp_value
      imodintro
      iframe
      iexists q
      iframe
      ipureintro
      grind
  · imod AbstractLangCompletenessGen.lang_completeness $$ %HnotStuck' He [Hheap HtpInv]
        with (⟨%K, %e₁, %Hctx, %Heq, %Hval, %Hatom, H⟩|⟨Hheap, Htpinv, H⟩)
    · have aux : cfgSafe (cfg.fst, cfg.snd) := cfgSafe_of_cfgSafeForking Hsafe
      iframe %aux Hheap HtpInv
    · imodintro
      ileft
      iexists K, e₁
      iframe %Hctx %Heq %Hatom
      iapply H
      iintro !> %κ %v₂ %σ₂' %Hefs %Hbase He HtpInv
      -- Now we need fractional divide n
      sorry
    · imodintro
      iright
      imod Hclose $$ [Hheap Htpinv] with -
      · inext
        iexists cfg
        -- FIXME: A. needs a better proof of this
        have Hframe : cfgSafeForking cfg f :=
          @«inferInstanceAs» (cfgSafeForking cfg f) Hsafe
        iframe Hheap Htpinv %Hreach %Hframe
      imodintro
      iapply H
      inext
      iintro %e₂ %efs H
      imod CancelableInvariant.acc _ _ _ _ _ Hn $$ [$] [$] with ⟨>Hinv2, Hq, Hclose⟩
      all_goals sorry


/-- **Top-level theorem**: `adequate` gives a WP with a pure postcondition.
This is the entry point consumed by the heap-lang case study. Stated on the
generic `AbstractLangCompletenessGen`, carrying `[InvOpenAbstractWP wp]`
(mirrors Rocq's `abstract_weakestpre_gen_magic` hypothesis). -/
theorem weakestpre_sem_completeness
    (e : Expr) (σ : State) (φ : Val → Prop)
    (Hade : adequate .NotStuck e σ (fun v _ => φ v)) :
    ⊢ tpInvIni (TI := TI) -∗
      ACG.heap_inv [e] σ -∗
      wp ⊤ e (fun v => iprop% ⌜φ v⌝) := by
  sorry

/-- Strong nofork variant. -/
theorem weakestpre_sem_completeness_nofork_strong
    (e : Expr) (σ : State) (φ : Val → State → Prop)
    (Hade : AdequateNoFork .NotStuck e σ (fun v σ' => φ v σ')) :
    ⊢ tpInvIni (TI := TI) -∗
      ACG.heap_inv [e] σ -∗
      wp ⊤ e (fun v =>
        iprop% ∃ σ' : State,
          tpInv (TI := TI) [ToVal.ofVal v] ∗
          isThread (TI := TI) 0 (.own 1) (ToVal.ofVal v) ∗
          ACG.heap_inv [ToVal.ofVal v] σ' ∗
          ⌜φ v σ'⌝) := by
  sorry

/-- User-facing nofork variant. -/
theorem weakestpre_sem_completeness_nofork
    (e : Expr) (σ : State) (φ : Val → State → Prop)
    (Hade : AdequateNoFork .NotStuck e σ (fun v σ' => φ v σ')) :
    ⊢ tpInvIni (TI := TI) -∗
      ACG.heap_inv [e] σ -∗
      wp ⊤ e (fun v =>
        iprop% ∃ σ' : State, ACG.heap_inv [ToVal.ofVal v] σ' ∗ ⌜φ v σ'⌝) := by
  sorry

end Completeness

end

end Iris.ProgramLogic
