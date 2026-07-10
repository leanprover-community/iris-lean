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
variable {H : Type _ → Type _} [LawfulFiniteMap H Nat]
variable [TI : TpinvGS GF Expr H]

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
variable {H : Type _ → Type _} [LawfulFiniteMap H Nat]
variable [TI : TpinvGS GF Expr H]
variable {wp : AbstractWP Expr Val GF}
variable [LWP : LawfulAbstractWP wp] [IAO : InvOpenAbstractWP wp]
variable [ACG : AbstractLangCompletenessGen wp]
variable [CInvG GF]

/-- Namespace under which the completeness invariant lives. -/
public def completenessN : Namespace := nroot .@ (1 : Pos)

public def cfgInv (Cini : List Expr × State) (f : Forking) : IProp GF := iprop%
  ∃ cfg : List Expr × State,
    ACG.heap_inv cfg.1 cfg.2 ∗ tpInv cfg.1 ∗ ⌜cfgSafeForking cfg f⌝ ∗ ⌜Cini -·->ₜₚ* cfg⌝

instance cfgInv_timeless (Cini : List Expr × State) (f : Forking) :
    Timeless (cfgInv (wp := wp) Cini f) := by
  unfold cfgInv; infer_instance

public def isCcfg (Cini : List Expr × State) (f : Forking) (γ : GName) : IProp GF :=
  CancelableInvariant.cinv completenessN γ (cfgInv (wp := wp) Cini f)

instance isCcfg_persistent (Cini : List Expr × State) (f : Forking) (γ : GName) :
    Persistent (isCcfg (wp := wp) Cini f γ : IProp GF) := by
  unfold isCcfg; infer_instance

omit [CInvG GF] in
theorem bigSepL_const_congr {α β : Type _} {P : IProp GF} {l1 : List α} {l2 : List β}
    (h : l1.length = l2.length) : ([∗list] _x ∈ l1, P) ⊣⊢ ([∗list] _x ∈ l2, P) :=
  BigSepL.bigSepL_replicate.symm.trans (.trans (h ▸ .rfl) (BigSepL.bigSepL_replicate))

theorem own_divide_forks {α : Type _} (γ : GName) (qc : Qp) (l : List α) :
    CancelableInvariant.own (GF := GF) γ qc ⊢
      CancelableInvariant.own γ (qc.divide_even (l.length + 1) (Nat.succ_pos _) : Qp) ∗
      ([∗list] _x ∈ l,
        CancelableInvariant.own γ (qc.divide_even (l.length + 1) (Nat.succ_pos _) : Qp)) := by
  have h := fractional_divide_equal
    (Φ := fun p : Qp => CancelableInvariant.own (GF := GF) γ p) qc l.length
  rw [List.replicate_succ'] at h
  refine h.trans ((BigSepL.bigSepL_snoc).1.trans
    (sep_comm.1.trans (sep_mono_right (bigSepL_const_congr (by simp)).1)))

theorem qp_div_ofPNat_succ_nil {α : Type _} (qc : Qp) {l : List α} (h : l = []) :
    qc.divide_even (l.length + 1) (Nat.succ_pos _) = qc := by
  simp only [h, List.length_nil, Nat.zero_add]; grind

-- Here

theorem weakestpre_completeness (Cini : List Expr × State) (f : Forking) (γ : GName) (q : Qp)
    (n : Nat) (e : Expr) :
    isCcfg (TI := TI) (wp := wp) Cini f γ -∗
    CancelableInvariant.own γ q -∗
    isThread (TI := TI) n (.own 1) e -∗
    wp ⊤ e (fun v => iprop%
        isThread (TI := TI) n (.own 1) (ToVal.ofVal v) ∗
        ∃ q' : Qp, CancelableInvariant.own γ q' ∗ ⌜f = .doesNotFork → q = q'⌝) := by
  iintro #Hinv
  iloeb as IH generalizing %q %n %e
  iintro Hq He
  have Hn : nclose completenessN ⊆ ⊤ := fun _ _ => CoPset.mem_full
  iapply IAO.inv_open_maybe (E₂ := ⊤ \ nclose completenessN) _ _ _ Std.LawfulSet.diff_subset_left
  unfold isCcfg
  imod CancelableInvariant.acc Hn $$ [$] [$] with ⟨>Hinv2, Hq, Hclose⟩
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
      icases own_divide_forks γ q Hefs $$ Hq with ⟨Hq, Hefsfrac⟩
      imod (tpInv_update cfg.fst n e (K ↑v₂)) $$ HtpInv He with ⟨HtpInv, He⟩
      imod (tpInv_new_threads Hefs (cfg.fst.set n (K ↑v₂))) $$ HtpInv with ⟨HtpInv, Hefs_threads⟩
      imodintro
      isplitl [Hclose Hq He HtpInv]
      · iintro Hheap
        have Hprim : (e, cfg.snd) -<κ>-> (K ↑v₂, σ₂', Hefs) := Heq ▸ Context.primStep_fill Hbase
        obtain ⟨Hsafe', Hnf⟩ := cfg_safeStep Hsafe Hlu Hprim
        imod Hclose $$ [Hheap HtpInv] with -
        · inext
          iexists (cfg.fst.set n (K ↑v₂) ++ Hefs, σ₂')
          iframe Hheap HtpInv
          ipureintro
          exact ⟨Hsafe', Hreach.tail ⟨κ, cfg_step Hlu Hprim⟩⟩
        imodintro
        iapply LWP.wp_wand $$ [Hq He]
        · iapply IH $$ Hq He
        iintro %v ⟨Hthread, %q', Hq', %Hfork⟩
        iframe Hthread
        iexists q'
        iframe Hq'
        ipureintro
        intro hnf
        rw [← Hfork hnf]
        congr 1
        exact (qp_div_ofPNat_succ_nil q (Hnf hnf)).symm
      · ihave Hcomb : iprop([∗list] k ↦ e' ∈ Hefs,
            (((cfg.fst.set n (K ↑v₂)).length + k) ↪thread e') ∗
            CancelableInvariant.own γ
              (q.divide_even (Hefs.length + 1) (Nat.succ_pos _) : Qp))
            $$ [Hefs_threads Hefsfrac]
        · iapply (BigSepL.bigSepL_sep_eqv).2
          iframe Hefs_threads Hefsfrac
        iapply BigSepL.bigSepL_impl $$ Hcomb
        iintro !> %k %e' %_ ⟨He, Hq⟩
        iapply LWP.wp_wand $$ [Hq He]
        · iapply IH $$ Hq He
        iintro %v _
        ipureintro
        trivial
    · imodintro
      iright
      imod Hclose $$ [Hheap Htpinv] with -
      · inext
        iexists cfg
        -- FIXME: needs a better proof of this
        have Hframe : cfgSafeForking cfg f := @«inferInstanceAs» (cfgSafeForking cfg f) Hsafe
        iframe Hheap Htpinv %Hreach %Hframe
      imodintro
      iapply H
      inext
      iintro %e₂ %efs H
      imod CancelableInvariant.acc Hn $$ [$] [$] with ⟨>Hinv2, Hq, Hclose⟩
      icases Hinv2 with ⟨%cfg2, Hheap, Htpinv, %Hsafe2, %Hreach2⟩
      imod H $$ [Hheap Htpinv] with ⟨%κ, %σ1', %Hprim, He, Htpinv, Hhp⟩
      · iframe Hheap Htpinv
        ipureintro
        exact cfgSafe_of_cfgSafeForking Hsafe2
      icases own_divide_forks γ q efs $$ Hq with ⟨Hq, Hefsfrac⟩
      ihave %Hlu2 := tpInv_lookup $$ Htpinv He
      obtain ⟨Hsafe2', Hforking2⟩ := cfg_safeSteps Hsafe2 Hlu2 Hprim
      imod (tpInv_update cfg2.fst n e e₂) $$ Htpinv He with ⟨Htpinv, He⟩
      imod (tpInv_new_threads efs (cfg2.fst.set n e₂)) $$ Htpinv with ⟨Htpinv, Hefs_threads⟩
      imod Hclose $$ [Hhp Htpinv] with -
      · inext
        iexists (cfg2.fst.set n e₂ ++ efs, σ1')
        iframe Hhp Htpinv
        ipureintro
        exact ⟨Hsafe2', Hreach2.trans (cfg_steps Hlu2 Hprim)⟩
      imodintro
      isplitl [Hq He]
      · iapply LWP.wp_wand $$ [Hq He]
        · iapply IH $$ Hq He
        iintro %v ⟨Hthread, %q', Hq', %Hfork⟩
        iframe Hthread
        iexists q'
        iframe Hq'
        ipureintro
        intro hnf
        rw [← Hfork hnf]
        congr 1
        exact (qp_div_ofPNat_succ_nil q (Hforking2 hnf)).symm
      · ihave Hcomb : iprop([∗list] k ↦ e' ∈ efs,
            (((cfg2.fst.set n e₂).length + k) ↪thread e') ∗
            CancelableInvariant.own γ
              (q.divide_even (efs.length + 1) (Nat.succ_pos _) : Qp))
            $$ [Hefs_threads Hefsfrac]
        · iapply (BigSepL.bigSepL_sep_eqv).2
          iframe Hefs_threads Hefsfrac
        iapply BigSepL.bigSepL_impl $$ Hcomb
        iintro !> %k %e' %_ ⟨He, Hq⟩
        iapply LWP.wp_wand $$ [Hq He]
        · iapply IH $$ Hq He
        iintro %v _
        ipureintro
        trivial


/-- `adequate` gives a WP with a pure postcondition from an `adequate` fact. -/
theorem weakestpre_sem_completeness
    (e : Expr) (σ : State) (φ : Val → Prop)
    (Hade : adequate .NotStuck e σ (fun v _ => φ v)) :
    ⊢ tpInvIni (TI := TI) -∗
      ACG.heap_inv [e] σ -∗
      wp ⊤ e (fun v => iprop% ⌜φ v⌝) := by
  have Hsafe0 : cfgSafeForking ([e], σ) .doesFork :=
    fun {C₂} hreach =>
      ⟨fun {e2} hmem => Hade.adequate_not_stuck _ _ e2 rfl hreach hmem,
       fun hf => Forking.noConfusion hf⟩
  iintro Hini Hheap
  iapply LWP.fupd_wp
  imod (tpInv_set [e]) $$ Hini with ⟨Hauth, Hfrags⟩
  imod (CancelableInvariant.alloc ⊤ completenessN
      (cfgInv (wp := wp) ([e], σ) .doesFork)) $$ [Hauth Hheap] with ⟨%γ, #Hinv, Hq⟩
  · inext
    unfold cfgInv
    iexists ([e], σ)
    iframe Hheap Hauth %Hsafe0
    ipureintro
    exact .refl
  have Hn0 : (completenessN : CoPset) ⊆ ⊤ := fun _ _ => CoPset.mem_full
  ihave He0 := (Iris.BI.BigSepL.bigSepL_singleton
    (Φ := fun n e' => isThread (TI := TI) n (.own 1) e') (x := e)).1 $$ Hfrags
  imodintro
  iapply LWP.wp_fupd
  ihave Hccfg : iprop(isCcfg (wp := wp) ([e], σ) .doesFork γ) $$ [Hinv]
  · unfold isCcfg; iexact Hinv
  ihave Hwp := weakestpre_completeness (wp := wp) ([e], σ) .doesFork γ (One.one : Qp) 0 e
    $$ Hccfg Hq He0
  iapply LWP.wp_wand $$ Hwp
  iintro %v ⟨Hv, %q', Hq', _⟩
  imod (CancelableInvariant.acc (E := ⊤) (N := completenessN) (γ := γ) (p := q')
    (P := cfgInv (wp := wp) ([e], σ) .doesFork) Hn0) $$ Hinv Hq' with ⟨>Hinv2, Hq', Hclose2⟩
  unfold cfgInv
  icases Hinv2 with ⟨%cfg, Hheap, Htpinv, %Hsafe2, %Hreach2⟩
  ihave %Hlu := tpInv_lookup $$ Htpinv Hv
  imod Hclose2 $$ [Hheap Htpinv] with -
  · inext
    iexists cfg
    iframe Hheap Htpinv %Hsafe2 %Hreach2
  imodintro
  ipureintro
  obtain ⟨tp2, σ2⟩ := cfg
  rcases tp2 with _ | ⟨hd, rest⟩
  · simp at Hlu
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hlu
    subst Hlu
    exact Hade.adequate_result rest σ2 v Hreach2

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
  have Hsafe0 : cfgSafeForking ([e], σ) .doesNotFork := by
    rintro ⟨tp2, σ2⟩ hreach
    refine ⟨fun {e2} hmem => Hade.not_stuck rfl hreach hmem, ?_⟩
    intro _ e2 hmem e' σ' κ efs hstep
    exact adequateNoFork_efs_nil Hade hreach hmem hstep
  have Hn0 : (completenessN : CoPset) ⊆ ⊤ := fun _ _ => CoPset.mem_full
  iintro Hini Hheap
  iapply LWP.fupd_wp
  imod (tpInv_set [e]) $$ Hini with ⟨Hauth, Hfrags⟩
  imod (CancelableInvariant.alloc ⊤ completenessN
      (cfgInv (wp := wp) ([e], σ) .doesNotFork)) $$ [Hauth Hheap] with ⟨%γ, #Hinv, Hq⟩
  · inext
    unfold cfgInv
    iexists ([e], σ)
    iframe Hheap Hauth %Hsafe0
    ipureintro
    exact .refl
  ihave He0 := (Iris.BI.BigSepL.bigSepL_singleton
    (Φ := fun n e' => isThread (TI := TI) n (.own 1) e') (x := e)).1 $$ Hfrags
  imodintro
  iapply LWP.wp_fupd
  ihave Hccfg : iprop(isCcfg (wp := wp) ([e], σ) .doesNotFork γ) $$ [Hinv]
  · unfold isCcfg; iexact Hinv
  ihave Hwp := weakestpre_completeness (wp := wp) ([e], σ) .doesNotFork γ (One.one : Qp) 0 e
    $$ Hccfg Hq He0
  iapply LWP.wp_wand $$ Hwp
  iintro %v ⟨Hv, %q', Hq', %His1⟩
  obtain rfl := His1 rfl
  imod (CancelableInvariant.cancel ⊤ completenessN γ
      (cfgInv (wp := wp) ([e], σ) .doesNotFork) Hn0) $$ Hinv Hq' with >Hinv2
  unfold cfgInv
  icases Hinv2 with ⟨%cfg, Hheap, Htpinv, %Hsafe2, %Hreach2⟩
  ihave %Hlu := tpInv_lookup $$ Htpinv Hv
  imodintro
  obtain ⟨tp2, σ2⟩ := cfg
  rcases tp2 with _ | ⟨hd, rest⟩
  · simp at Hlu
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hlu
    subst Hlu
    have hlen := Hade.no_fork Hreach2
    rw [List.length_cons] at hlen
    obtain rfl := List.length_eq_zero_iff.mp (by omega : rest.length = 0)
    iexists σ2
    iframe Htpinv Hv Hheap
    ipureintro
    exact Hade.result Hreach2

theorem weakestpre_sem_completeness_nofork
    (e : Expr) (σ : State) (φ : Val → State → Prop)
    (Hade : AdequateNoFork .NotStuck e σ (fun v σ' => φ v σ')) :
    ⊢ tpInvIni (TI := TI) -∗
      ACG.heap_inv [e] σ -∗
      wp ⊤ e (fun v =>
        iprop% ∃ σ' : State, ACG.heap_inv [ToVal.ofVal v] σ' ∗ ⌜φ v σ'⌝) := by
  iintro Hini Hheap
  ihave Hw := weakestpre_sem_completeness_nofork_strong (wp := wp) e σ φ Hade $$ Hini Hheap
  iapply LWP.wp_wand $$ Hw
  iintro %v ⟨%σ2, _, _, Hh, Hphi⟩
  iexists σ2
  iframe

end Completeness

end

end Iris.ProgramLogic
