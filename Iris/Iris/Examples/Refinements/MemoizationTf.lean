/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Examples.Refinements.Memoization
public import Iris.Algebra.Lib.ExclAuth

/-! # Repeatable refinements

This file ports the section `repeatable_refinements` of
`theories/examples/refinements/memoization.v` of Transfinite Iris: memoization where the
knowledge about the stored results (`eval (f k') v'`) is not timeless, so it is kept in a second
(non-timeless) non-atomic invariant, and the source stutters when a result is looked up
(`tf_memoize_spec`, `tf_mem_rec_spec`).
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite.Refinement.Memoization

open Iris Iris.Std Iris.BI Iris.HeapLang Iris.HeapLang.Transfinite ProgramLogic Language
open Language.Notation Iris.Transfinite.Refinement.Examples ExclAuth

set_option linter.unusedSectionVars false

section RepeatableRefinements

variable {GF : BundledGFunctors} [G : RHeapG GF] [N : NatSourceG GF] [S : SeqG GF]
variable [Esync : ElemG GF (constOF (ExclAuthR (A := DiscreteO (List (Val × Val)))))]
variable (Pre Post : Val → Val → IProp GF) (Comparable : Val → IProp GF)
  (Eq : Val → Val → IProp GF)
variable [∀ v v', Persistent (Pre v v')] [∀ v v', Persistent (Post v v')]
  [∀ v v', Persistent (Eq v v')] [∀ v, Timeless (Comparable v)]
variable (Pre_Comparable : ∀ v v', Pre v v' ⊢ |={⊤}=> Comparable v)
  (Pre_Eq_Proper : ∀ v₁ v₁' v₂, Eq v₁ v₁' ∗ Pre v₁' v₂ ⊢ Pre v₁ v₂)

/-- The authoritative table of results. -/
def tableAuth (γ : GName) (kvs : List (Val × Val)) : IProp GF :=
  iOwn (E := Esync) γ (●E (DiscreteO.mk kvs))

/-- The fragment of the table of results. -/
def tableFrag (γ : GName) (kvs : List (Val × Val)) : IProp GF :=
  iOwn (E := Esync) γ (◯E (DiscreteO.mk kvs))

instance tableAuth_timeless (γ : GName) (kvs : List (Val × Val)) :
    Timeless (tableAuth (GF := GF) γ kvs) := by
  unfold tableAuth; infer_instance

instance stutter_timeless (n : Nat) : Timeless (stutter (GF := GF) n) := by
  unfold stutter srcF; infer_instance

/-- The timeless invariant (Rocq: `mem_rec_tl_inv`). -/
def memRecTlInv (γ : GName) (m : Val) : IProp GF :=
  iprop(∃ kvs, Map Comparable m kvs ∗ tableAuth γ kvs ∗ stutter 1)

/-- The persistent knowledge about a stored result. -/
def tfEntry (f : Val) (kv : Val × Val) : IProp GF :=
  iprop(□ (∀ k', Pre kv.1 k' -∗ ∃ v', □ evalS hl(v(&f) v(&k')) v' ∗ Post kv.2 v'))

/-- The non-timeless invariant (Rocq: `mem_rec_tf_inv`). -/
def memRecTfInv (γ : GName) (f : Val) : IProp GF :=
  iprop(∃ kvs, tableFrag γ kvs ∗ [∗list] kv ∈ kvs, tfEntry Pre Post f kv)

instance memRecTlInv_timeless (γ : GName) (m : Val) :
    Timeless (memRecTlInv Comparable γ m) := by
  unfold memRecTlInv
  refine @UPred.exists_timeless' _ _ _ _ _ _ (fun kvs => ?_)
  exact @UPred.sep_timeless' _ _ _ _ _ _ inferInstance
    (@UPred.sep_timeless' _ _ _ _ _ _ inferInstance inferInstance)

instance tfEntry_persistent (f : Val) (kv : Val × Val) : Persistent (tfEntry Pre Post f kv) := by
  unfold tfEntry; infer_instance

/-- Rocq: `tf_implements`. -/
def tfImplements (g f : Val) : IProp GF :=
  iprop(□ ∀ x : Val, ∀ x' : Val, ∀ c : Nat, ∀ K : List ECtxItem, Pre x x' -∗
    src (fill K hl(v(&f) v(&x'))) -∗
    rseq ⊤ hl(v(&g) v(&x)) fun v => iprop(∃ v' : Val, Post v v' ∗ stutter c ∗
      src (fill K (v' : Exp)) ∗
      □ (∀ x', Pre x x' -∗ ∃ v', □ evalS hl(v(&f) v(&x')) v' ∗ Post v v')))

instance tfImplements_persistent (g f : Val) : Persistent (tfImplements Pre Post g f) := by
  unfold tfImplements; infer_instance

theorem table_agree (γ : GName) (kvs kvs' : List (Val × Val)) :
    ⊢ tableAuth (GF := GF) γ kvs -∗ tableFrag γ kvs' -∗ ⌜kvs = kvs'⌝ := by
  unfold tableAuth tableFrag
  iintro Ha Hf
  ihave H := (iOwn_op (E := Esync) (γ := γ)).mpr $$ [Ha Hf]
  · iframe
  ihave ⟨Hv, -⟩ := iOwn_valid_l $$ H
  icases internalCmraValid_discrete.mp $$ Hv with %Hv
  ipureintro
  exact DiscreteO.eqv_inj (ExclAuth.agree Hv)

theorem table_update (γ : GName) (kvs kvs' kvs'' : List (Val × Val)) :
    ⊢ tableAuth (GF := GF) γ kvs -∗ tableFrag γ kvs' ==∗ tableAuth γ kvs'' ∗ tableFrag γ kvs'' := by
  unfold tableAuth tableFrag
  iintro Ha Hf
  ihave H := (iOwn_op (E := Esync) (γ := γ)).mpr $$ [Ha Hf]
  · iframe
  imod iOwn_update ExclAuth.update $$ H with H
  icases (iOwn_op (E := Esync)).mp $$ H with ⟨Ha, Hf⟩
  imodintro
  iframe

theorem tl_top : (↑(refN.@"tl") : CoPset) ⊆ ⊤ := fun _ _ => CoPset.mem_full
theorem tf_top : (↑(refN.@"tf") : CoPset) ⊆ ⊤ := fun _ _ => CoPset.mem_full
theorem tf_sub : (↑(refN.@"tf") : CoPset) ⊆ ⊤ \ ↑(refN.@"tl") := fun _ hp =>
  LawfulSet.mem_diff.mpr ⟨CoPset.mem_full, fun hg => ndot_ne_disjoint refN (by decide) _ ⟨hp, hg⟩⟩

include Pre_Comparable Pre_Eq_Proper in
/-- Rocq: `tf_memoization_core`. -/
theorem tf_memoization_core (eq f : Val) (e : Exp) (c : Nat) (γ : GName) (n n' m : Val)
    (K : List ECtxItem) :
    rseq ⊤ e (fun h => tfImplements Pre Post h f) ∗
      NonAtomicInvariant.inv S.name (refN.@"tl") (memRecTlInv Comparable γ m) ∗
      NonAtomicInvariant.inv S.name (refN.@"tf") (memRecTfInv Pre Post γ f) ∗
      Pre n n' ∗ eqfun (src := refSrc (GF := GF)) Comparable eq Eq ∗
      src (fill K hl(v(&f) v(&n'))) ⊢
      rseq ⊤ (memoBody e m eq n) fun v => iprop(∃ v' : Val, Post v v' ∗ stutter c ∗
        src (fill K (v' : Exp)) ∗
        □ (∀ n', Pre n n' -∗ ∃ v', □ evalS hl(v(&f) v(&n')) v' ∗ Post v v')) := by
  unfold rseq seq
  iintro ⟨Spec, #IM, #IC, #HPre, #Heqfun, Hsrc⟩ Hna
  iapply fupd_rwp (src := refSrc (GF := GF))
  imod NonAtomicInvariant.inv_acc_open_timeless tl_top tl_top $$ IM Hna with ⟨Hc, Hna, Hclose1⟩
  imod Pre_Comparable n n' $$ HPre with HComp
  imodintro
  unfold memRecTlInv
  icases Hc with ⟨%kvs, HM, Hauth, Hone⟩
  unfold memoBody
  twp_bind (v(&get) v(&m) v(&eq) v(&n))
  ihave Hget := get_spec (src := refSrc (GF := GF)) Comparable kvs eq Eq m n
  unfold texan
  iapply Hget $$ [HM HComp]
  · isplitl [HM]
    · iexact HM
    isplitr [HComp]
    · iexact Heqfun
    iexact HComp
  iintro %v ⟨%o, %rfl, Ho, HM⟩
  cases o with
  | some k =>
    -- the result was stored before
    unfold getPost
    icases Ho with ⟨%n₀, %hlook, #Heq⟩
    iapply fupd_rwp (src := refSrc (GF := GF))
    imod NonAtomicInvariant.inv_acc_open tf_top tf_sub $$ IC Hna with Hcache
    imodintro
    iapply rwp_take_step_src rfl
    iapply weakSrcUpdate_bind_r (src := refSrc (GF := GF))
    isplitl [Hone]
    · iapply step_stutter ⊤ 0 $$ Hone
    iintro -
    iapply weakSrcUpd_return
    iapply rswp_do_step (src := refSrc (GF := GF))
    inext
    icases Hcache with ⟨HsrcI, Hna, Hclose2⟩
    unfold memRecTfInv
    icases HsrcI with ⟨%kvs', Hfrag, #Hupd⟩
    icases table_agree γ kvs kvs' $$ Hauth Hfrag with %hk
    subst hk
    simp only [embed]
    twp_pure
    obtain ⟨i, hi⟩ := lookupKV_getElem? hlook
    ihave #Hk := BigSepL.bigSepL_lookup hi $$ Hupd
    unfold tfEntry
    ihave ⟨%v', #Heval, #HP⟩ := Hk $$ %n' []
    · iapply Pre_Eq_Proper n₀ n n'
      iframe Heq HPre
    iapply rwp_weaken (src := refSrc (GF := GF))
      (P := iprop((∃ _ : Unit, src (fill K (v' : Exp)) ∗ emp) ∗ stutter (c + 1))) rfl
      $$ [Hfrag Hauth HM Hna Hclose1 Hclose2] [Hsrc]
    · iintro ⟨⟨%_, Hsrc, -⟩, Hc⟩
      icases (nat_srcF_succ c).mp $$ Hc with ⟨Hone, Hc⟩
      iapply fupd_rwp (src := refSrc (GF := GF))
      imod Hclose2 $$ [Hfrag Hna] with Hna
      · iframe Hna
        inext
        iexists kvs
        iframe Hfrag
        iexact Hupd
      imod Hclose1 $$ [HM Hauth Hna Hone] with Hna
      · iframe Hna
        inext
        iexists kvs
        iframe
      imodintro
      twp_pures
      iframe Hna
      iexists v'
      iframe HP Hsrc Hc
      iintro !> %n'' #HPre''
      iapply Hk $$ %n''
      iapply Pre_Eq_Proper n₀ n n''
      iframe Heq HPre''
    · ihave H := step_inv_alloc (c + 1) ⊤ 0 (fill K hl(v(&f) v(&n')))
        (fun _ : Unit => fill K (v' : Exp)) (fun _ => iprop(emp))
        (fun _ => Derived.fill_ne (by simp)) $$ []
      · iintro Hsrc
        unfold evalS
        ihave He := Heval $$ %K Hsrc
        iapply srcUpdate_mono (src := refSrc (GF := GF))
        isplitl [He]
        · iexact He
        iintro Hsrc
        iexists ()
        iframe
      iapply H $$ Hsrc
  | none =>
    -- close the invariant again for the recursive call
    unfold getPost
    iapply fupd_rwp (src := refSrc (GF := GF))
    imod Hclose1 $$ [HM Hauth Hna Hone] with Hna
    · iframe Hna
      inext
      iexists kvs
      iframe
    imodintro
    simp only [embed]
    twp_pures
    twp_bind (&e)
    ihave Spec := Spec $$ Hna
    twp_apply rwpR_wand $$ Spec
    iintro %g ⟨Hna, #Himpl⟩
    unfold tfImplements rseq seq
    ihave Hres := Himpl $$ %n %n' %(c + 1) %K HPre Hsrc Hna
    twp_bind (v(&g) v(&n))
    twp_apply rwpR_wand $$ Hres
    iintro %v ⟨Hna, %k, #HPost, Hcred, Hsrc, #Hk⟩
    icases (nat_srcF_succ c).mp $$ Hcred with ⟨Hone, Hcred⟩
    iapply fupd_rwp (src := refSrc (GF := GF))
    imod NonAtomicInvariant.inv_acc_open_timeless tl_top tl_top $$ IM Hna with ⟨Hc, Hna, Hclose1⟩
    imod NonAtomicInvariant.inv_acc_open tf_top tf_sub $$ IC Hna with Hcache
    imod Pre_Comparable n n' $$ HPre with HComp
    imodintro
    icases Hc with ⟨%kvs₂, HM, Hauth, Hone'⟩
    iapply rwp_take_step_src rfl
    iapply weakSrcUpdate_bind_r (src := refSrc (GF := GF))
    isplitl [Hone]
    · iapply step_stutter ⊤ 0 $$ Hone
    iintro -
    iapply weakSrcUpd_return
    iapply rswp_do_step (src := refSrc (GF := GF))
    inext
    icases Hcache with ⟨HsrcI, Hna, Hclose2⟩
    unfold memRecTfInv
    icases HsrcI with ⟨%kvs₂', Hfrag, #Hupd⟩
    icases table_agree γ kvs₂ kvs₂' $$ Hauth Hfrag with %hk
    subst hk
    twp_pures
    ihave Hset := set_spec (src := refSrc (GF := GF)) Comparable kvs₂ m v n
    unfold texan
    twp_apply Hset $$ [HM HComp]
    · isplitl [HM]
      · iexact HM
      iexact HComp
    iintro %r ⟨%rfl, HM⟩
    iapply fupd_rwp (src := refSrc (GF := GF))
    imod table_update γ kvs₂ kvs₂ ((n, v) :: kvs₂) $$ Hauth Hfrag with ⟨Hauth, Hfrag⟩
    imod Hclose2 $$ [Hfrag Hna] with Hna
    · iframe Hna
      inext
      iexists (n, v) :: kvs₂
      iframe Hfrag
      iapply BigSepL.bigSepL_cons.mpr
      iframe Hupd
      unfold tfEntry
      iexact Hk
    imod Hclose1 $$ [HM Hauth Hna Hone'] with Hna
    · iframe Hna
      inext
      iexists (n, v) :: kvs₂
      iframe
    imodintro
    twp_pures
    iframe Hna
    iexists k
    iframe HPost Hcred Hsrc Hk

theorem table_alloc :
    ⊢@{IProp GF} |==> ∃ γ, tableAuth γ [] ∗ tableFrag γ [] := by
  unfold tableAuth tableFrag
  imod iOwn_alloc (E := Esync) ((●E (DiscreteO.mk ([] : List (Val × Val)))) •
    ◯E (DiscreteO.mk ([] : List (Val × Val)))) ExclAuth.valid with ⟨%γ, H⟩
  icases (iOwn_op (E := Esync)).mp $$ H with ⟨Ha, Hf⟩
  imodintro
  iexists γ
  iframe

include Pre_Comparable Pre_Eq_Proper in
/-- Allocating the invariants of the memoization table. -/
theorem tf_alloc_invs (f m : Val) (P : IProp GF) :
    Map Comparable m [] ∗ stutter 1 ∗
      (∀ γ, NonAtomicInvariant.inv S.name (refN.@"tl") (memRecTlInv Comparable γ m) -∗
        NonAtomicInvariant.inv S.name (refN.@"tf") (memRecTfInv Pre Post γ f) -∗ P) ⊢
      |={⊤}=> P := by
  iintro ⟨Hm, Hone, HP⟩
  imod table_alloc (GF := GF) with ⟨%γ, Ha, Hf⟩
  ihave HI₁ : ▷ memRecTlInv Comparable γ m $$ [Hm Ha Hone]
  · inext
    unfold memRecTlInv
    iexists []
    iframe
  imod NonAtomicInvariant.inv_alloc (p := S.name) (N := refN.@"tl") $$ HI₁ with #IM
  ihave HI₂ : ▷ memRecTfInv Pre Post γ f $$ [Hf]
  · inext
    unfold memRecTfInv
    iexists []
    iframe
    iapply BigSepL.bigSepL_nil.mpr
    itrivial
  imod NonAtomicInvariant.inv_alloc (p := S.name) (N := refN.@"tf") $$ HI₂ with #IS
  imodintro
  iapply HP $$ %γ IM IS

include Pre_Comparable Pre_Eq_Proper in
/-- Rocq: `tf_memoize_spec`. -/
theorem tf_memoize_spec (eq f g : Val) :
    eqfun (src := refSrc (GF := GF)) Comparable eq Eq ∗ tfImplements Pre Post g f ∗ stutter 1 ⊢
      rseq ⊤ hl(v(&memoize) v(&eq) v(&g)) fun h => tfImplements Pre Post h f := by
  unfold rseq seq
  iintro ⟨#Heq, #H, Hcred⟩ Hna
  unfold memoize
  twp_pures
  ihave Hm := map_spec (src := refSrc (GF := GF)) Comparable
  unfold texan
  twp_apply Hm
  · itrivial
  iintro %m Hm
  iapply fupd_rwp (src := refSrc (GF := GF))
  iapply tf_alloc_invs Pre Post Comparable Eq Pre_Comparable Pre_Eq_Proper f m
  iframe Hm Hcred
  iintro %γ #IM #IS
  twp_pures
  iframe Hna
  unfold tfImplements
  iintro !> %n %n' %c %K #HPre Hsrc
  unfold rseq seq
  iintro Hna
  twp_pure
  ihave Hcore := tf_memoization_core Pre Post Comparable Eq Pre_Comparable Pre_Eq_Proper eq f
    (g : Exp) c γ n n' m K $$ [Hsrc]
  · isplitl []
    · iapply seq_value (src := refSrc (GF := GF))
      unfold tfImplements rseq seq
      iexact H
    iframe Hsrc
    isplitr
    · iexact IM
    isplitr
    · iexact IS
    isplitr
    · iexact HPre
    iexact Heq
  unfold rseq seq memoBody
  iapply Hcore $$ Hna

include Pre_Comparable Pre_Eq_Proper in
/-- Rocq: `tf_mem_rec_spec`. -/
theorem tf_mem_rec_spec (eq F f : Val) :
    eqfun (src := refSrc (GF := GF)) Comparable eq Eq ∗
      (□ ∀ g, ▷ tfImplements Pre Post g f -∗
        rseq ⊤ hl(v(&F) v(&g)) fun h => tfImplements Pre Post h f) ∗ stutter 1 ⊢
      rseq ⊤ hl(v(&memRec) v(&eq) v(&F)) fun h => tfImplements Pre Post h f := by
  unfold rseq seq
  iintro ⟨#Heq, #HF, Hcred⟩ Hna
  unfold memRec
  twp_pures
  ihave Hm := map_spec (src := refSrc (GF := GF)) Comparable
  unfold texan
  twp_apply Hm
  · itrivial
  iintro %m Hm
  iapply fupd_rwp (src := refSrc (GF := GF))
  iapply tf_alloc_invs Pre Post Comparable Eq Pre_Comparable Pre_Eq_Proper f m
  iframe Hm Hcred
  iintro %γ #IM #IS
  twp_pures
  iframe Hna
  iloeb as IH
  unfold tfImplements
  iintro !> %n %n' %c %K #HPre Hsrc
  unfold rseq seq
  iintro Hna
  twp_pure
  ihave Hcore := tf_memoization_core Pre Post Comparable Eq Pre_Comparable Pre_Eq_Proper eq f
    hl(v(&F) v(&(memRecClosure eq F m))) c γ n n' m K $$ [Hsrc]
  · isplitl []
    · unfold tfImplements rseq seq
      iapply HF $$ %(memRecClosure eq F m) IH
    iframe Hsrc
    isplitr
    · iexact IM
    isplitr
    · iexact IS
    isplitr
    · iexact HPre
    iexact Heq
  unfold rseq seq memoBody
  iapply Hcore $$ Hna

end RepeatableRefinements

end Iris.Transfinite.Refinement.Memoization
