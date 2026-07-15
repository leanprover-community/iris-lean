/-
Copyright (c) 2026 Haokun Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haokun Li, Sergei Stepanenko
-/
module

public import Iris.BI.BI
public import Iris.BI.BIBase
public import Iris.BI.DerivedLaws
public import Iris.BI.DerivedLawsLater
public import Iris.BI.Extensions
public import Iris.BI.Classes
public import Iris.BI.Embedding
public import Iris.BI.Updates
public import Iris.BI.Plainly
public import Iris.BI.Sbi
public import Iris.BI.BigOp.BigOp
public import Iris.BI.BigOp.BigSepList
public import Iris.BI.BigOp.BigSepMap
public import Iris.BI.BigOp.BigSepSet

/-! ### TODO

The following Rocq names from `monpred.v` are not yet ported:

- `monPred_at_big_sepMS`
- `big_sepMS_objective`
- `monPred_objectively_big_sepMS`
- `monPred_objectively_big_sepMS_entails`

(`BigSepMSet` not ported in iris-lean)
-/

@[expose] public section

namespace Iris.BI
open Iris Iris.Std OFE

/-- A `BiIndex` is an inhabited type equipped with a preorder `⊑`. Monotone
predicates are functions out of a `BiIndex` that are monotone w.r.t. this order. -/
@[rocq_alias biIndex]
structure BiIndex where
  car : Type _
  [inhabited : Inhabited car]
  -- rel : car → car → Prop

  rel : LE car

  [preorder : Std.IsPreorder car]

attribute [instance] BiIndex.inhabited BiIndex.preorder

instance : CoeSort BiIndex (Type _) := ⟨BiIndex.car⟩

/-- Notation for the `BiIndex` order, written `i ⊑ j` in Rocq. -/
scoped infix:40 " ⊑ᵢ " => BiIndex.rel _

/-- A `BiIndex` with a bottom element `bot`: every index is above `bot`. -/
@[rocq_alias BiIndexBottom]
class BiIndexBottom (I : BiIndex) (bot : I.car) : Prop where
  bot_le : ∀ i : I.car, I.rel.le bot i

/-- A monotone predicate over `BiIndex` `I` valued in the base BI `PROP`: a function
`monPred_at : I → PROP` monotone w.r.t. the index order. -/
@[rocq_alias monPred]
structure MonPred (I : BiIndex) (PROP : Type _) [BIBase PROP] where
  /-- The underlying index-indexed family (Rocq `monPred_at`). -/
  monPred_at : I.car → PROP
  /-- Monotonicity in the index (Rocq `monPred_mono`: `Proper ((⊑) ==> (⊢))`). -/
  monPred_mono : ∀ {i j : I.car}, I.rel.le i j → (monPred_at i ⊢ monPred_at j)

namespace MonPred

variable {I : BiIndex} {PROP : Type _} [BIBase PROP]

/-- Extensionality for `MonPred`: two monotone predicates are equal when their
`monPred_at` projections agree (proof-irrelevant on `monPred_mono`).
Lean addition (not in Rocq): Rocq has no `=` on `monpred`; the analog is the `⊣⊢`
lemma `monPred_at_equiv`. -/
theorem ext {P Q : MonPred I PROP} (h : ∀ i, P.monPred_at i = Q.monPred_at i) :
    P = Q := by
  cases P; cases Q
  simp only [MonPred.mk.injEq]
  exact funext h

/-- Kripke up-closure: `upclosed Φ i := ∀ j, ⌜i ⊑ j⌝ → Φ j`. Used by `impl`/`wand`
so the result is monotone. -/
@[rocq_alias monPred_defs.monPred_upclosed]
def upclosed [BI PROP] (Φ : I.car → PROP) : I.car → PROP :=
  fun i => iprop(∀ j, ⌜I.rel.le i j⌝ → Φ j)

end MonPred

section OFE
variable {I : BiIndex} {PROP : Type _} [BI PROP]

/-- Pointwise OFE: `P ≡ Q := ∀ i, P i ≡ Q i`, `P ≡{n}≡ Q := ∀ i, P i ≡{n}≡ Q i`
(Rocq `monPredO`). -/
@[rocq_alias monPredO]
instance : OFE (MonPred I PROP) where
  Dist n P Q := ∀ i, P.monPred_at i ≡{n}≡ Q.monPred_at i
  dist_eqv :=
    { refl _ _ := dist_eqv.refl _
      symm h i := dist_eqv.symm (h i)
      trans h1 h2 i := dist_eqv.trans (h1 i) (h2 i) }
  eq_dist {P Q} := by
    refine ⟨fun h _ _ => h ▸ .rfl, fun h => ?_⟩
    exact MonPred.ext fun i => eq_dist.mpr fun n => h n i
  dist_lt h1 h2 i := dist_lt (h1 i) h2

#rocq_ignore monPred_ofe_mixin "Rocq mixin record; subsumed by the OFE instance."

/-! `MonPred I PROP` is isomorphic, as an OFE, to the subtype of *monotone* functions
`I.car → PROP`, packaging the `monPred_mono` field as a subtype predicate. Rocq
`sig_monPred` / `monPred_sig`. -/

namespace MonPred

/-- `MonPred I PROP` as the subtype of monotone families: the forward map. Rocq
`monPred_sig`. -/
@[rocq_alias monPred_sig]
def toSig :
    MonPred I PROP -n> { f : I.car → PROP // ∀ {i j : I.car}, I.rel.le i j → (f i ⊢ f j) } where
  f P := ⟨P.monPred_at, fun h => P.monPred_mono h⟩
  ne.1 _ _ _ h := h

/-- The inverse of `MonPred.toSig`: rebuild a monotone predicate from a monotone family.
Rocq `sig_monPred`. -/
@[rocq_alias sig_monPred]
def ofSig :
    { f : I.car → PROP // ∀ {i j : I.car}, I.rel.le i j → (f i ⊢ f j) } -n> MonPred I PROP where
  f P := ⟨P.val, P.property⟩
  ne.1 _ _ _ h := h

@[rocq_alias sig_monPred_ne]
theorem ofSig_ne : OFE.NonExpansive (ofSig (I := I) (PROP := PROP)) := ofSig.ne

@[rocq_alias sig_monPred_proper]
theorem ofSig_proper {P Q : { f : I.car → PROP // ∀ {i j : I.car}, I.rel.le i j → (f i ⊢ f j) }}
    (h : P ≡ Q) : ofSig P ≡ ofSig Q := ofSig.ne.eqv h

@[rocq_alias monPred_sig_ne]
theorem toSig_ne : OFE.NonExpansive (toSig (I := I) (PROP := PROP)) := toSig.ne

@[rocq_alias monPred_sig_proper]
theorem toSig_proper {P Q : MonPred I PROP} (h : P ≡ Q) : toSig P ≡ toSig Q := toSig.ne.eqv h

@[rocq_alias sig_monPred_sig]
theorem ofSig_toSig (P : MonPred I PROP) : ofSig (toSig P) = P := rfl

@[rocq_alias monPred_sig_monPred]
theorem toSig_ofSig (P : { f : I.car → PROP // ∀ {i j : I.car}, I.rel.le i j → (f i ⊢ f j) }) :
    toSig (ofSig P) = P := rfl

end MonPred

@[rocq_alias monPred_cofe]
instance : IsCOFE (MonPred I PROP) where
  compl c :=
    let cf := c.map ((⟨Subtype.val, inferInstance⟩ : _ -n> (I.car → PROP)).comp MonPred.toSig)
    { monPred_at := fun i => COFE.compl cf i
      monPred_mono := fun {i j} h =>
        LimitPreserving.entails (applyHom i) (applyHom j) cf (fun n => (c n).monPred_mono h) }
  conv_compl {n c} :=
    IsCOFE.conv_compl (n := n)
      (c := c.map ((⟨Subtype.val, inferInstance⟩ : _ -n> (I.car → PROP)).comp MonPred.toSig))

end OFE

namespace MonPred
variable {I : BiIndex} {PROP : Type _}
variable [BI PROP]

@[rocq_alias monPred_defs.monPred_entails]
def Entails (P Q : MonPred I PROP) : Prop := ∀ i, P.monPred_at i ⊢ Q.monPred_at i

@[rocq_alias monPred_defs.monPred_emp]
def emp : MonPred I PROP where
  monPred_at _ := iprop(emp)
  monPred_mono _ := .rfl

#rocq_ignore monPred_defs.monPred_emp_def "Rocq unsealed definition body; use MonPred.emp."
#rocq_ignore monPred_defs.monPred_emp_aux "Rocq sealing auxiliary definition."
#rocq_ignore monPred_defs.monPred_emp_unseal "Rocq unsealing lemma."
#rocq_ignore monPred_emp_unseal "Rocq unsealing lemma."
#rocq_ignore monPred_emp_unfold "Rocq unfold lemma; Lean definitions are transparent."

@[rocq_alias monPred_defs.monPred_pure]
def pure (φ : Prop) : MonPred I PROP where
  monPred_at _ := iprop(⌜φ⌝)
  monPred_mono _ := .rfl

#rocq_ignore monPred_defs.monPred_pure_def "Rocq unsealed definition body; use MonPred.pure."
#rocq_ignore monPred_defs.monPred_pure_aux "Rocq sealing auxiliary definition."
#rocq_ignore monPred_defs.monPred_pure_unseal "Rocq unsealing lemma."
#rocq_ignore monPred_pure_unseal "Rocq unsealing lemma."
#rocq_ignore monPred_pure_unfold "Rocq unfold lemma; Lean definitions are transparent."

@[rocq_alias monPred_defs.monPred_and]
def and (P Q : MonPred I PROP) : MonPred I PROP where
  monPred_at i := iprop(P.monPred_at i ∧ Q.monPred_at i)
  monPred_mono h := and_mono (P.monPred_mono h) (Q.monPred_mono h)

#rocq_ignore monPred_defs.monPred_and_def "Rocq unsealed definition body; use MonPred.and."
#rocq_ignore monPred_defs.monPred_and_aux "Rocq sealing auxiliary definition."
#rocq_ignore monPred_defs.monPred_and_unseal "Rocq unsealing lemma."
#rocq_ignore monPred_and_unseal "Rocq unsealing lemma."

@[rocq_alias monPred_defs.monPred_or]
def or (P Q : MonPred I PROP) : MonPred I PROP where
  monPred_at i := iprop(P.monPred_at i ∨ Q.monPred_at i)
  monPred_mono h := or_mono (P.monPred_mono h) (Q.monPred_mono h)

#rocq_ignore monPred_defs.monPred_or_def "Rocq unsealed definition body; use MonPred.or."
#rocq_ignore monPred_defs.monPred_or_aux "Rocq sealing auxiliary definition."
#rocq_ignore monPred_defs.monPred_or_unseal "Rocq unsealing lemma."
#rocq_ignore monPred_or_unseal "Rocq unsealing lemma."

@[rocq_alias monPred_defs.monPred_impl]
def imp (P Q : MonPred I PROP) : MonPred I PROP where
  monPred_at := MonPred.upclosed (fun i => iprop(P.monPred_at i → Q.monPred_at i))
  monPred_mono h :=
    forall_intro fun k => (forall_elim k).trans
      (imp_mono_left (pure_mono fun hjk => Trans.trans h hjk))

#rocq_ignore monPred_defs.monPred_impl_def "Rocq unsealed definition body; use MonPred.imp."
#rocq_ignore monPred_defs.monPred_impl_aux "Rocq sealing auxiliary definition."
#rocq_ignore monPred_defs.monPred_impl_unseal "Rocq unsealing lemma."
#rocq_ignore monPred_impl_unseal "Rocq unsealing lemma."

@[rocq_alias monPred_defs.monPred_forall]
def sForall (Ψ : MonPred I PROP → Prop) : MonPred I PROP where
  monPred_at i := BIBase.sForall (fun p => ∃ q : MonPred I PROP, Ψ q ∧ q.monPred_at i = p)
  monPred_mono h :=
    sForall_intro fun _p ⟨q, hq, hp⟩ => (sForall_elim ⟨q, hq, rfl⟩).trans (hp ▸ q.monPred_mono h)

#rocq_ignore monPred_defs.monPred_forall_def "Rocq unsealed definition body; use MonPred.sForall."
#rocq_ignore monPred_defs.monPred_forall_aux "Rocq sealing auxiliary definition."
#rocq_ignore monPred_defs.monPred_forall_unseal "Rocq unsealing lemma."
#rocq_ignore monPred_forall_unseal "Rocq unsealing lemma."

@[rocq_alias monPred_defs.monPred_exist]
def sExists (Ψ : MonPred I PROP → Prop) : MonPred I PROP where
  monPred_at i := BIBase.sExists (fun p => ∃ q : MonPred I PROP, Ψ q ∧ q.monPred_at i = p)
  monPred_mono h :=
    sExists_elim fun _p ⟨q, hq, hp⟩ => (hp ▸ q.monPred_mono h).trans (sExists_intro ⟨q, hq, rfl⟩)

#rocq_ignore monPred_defs.monPred_exist_def "Rocq unsealed definition body; use MonPred.sExists."
#rocq_ignore monPred_defs.monPred_exist_aux "Rocq sealing auxiliary definition."
#rocq_ignore monPred_defs.monPred_exist_unseal "Rocq unsealing lemma."
#rocq_ignore monPred_exist_unseal "Rocq unsealing lemma."

theorem sForall_at_elim {Ψ : MonPred I PROP → Prop} {q : MonPred I PROP} (i : I.car) (hq : Ψ q) :
    (MonPred.sForall Ψ).monPred_at i ⊢ q.monPred_at i :=
  sForall_elim ⟨q, hq, rfl⟩

theorem sForall_at_intro {Ψ : MonPred I PROP → Prop} {R : PROP} (i : I.car)
    (h : ∀ q, Ψ q → R ⊢ q.monPred_at i) : R ⊢ (MonPred.sForall Ψ).monPred_at i :=
  sForall_intro fun _ ⟨q, hq, hp⟩ => hp ▸ h q hq

theorem sExists_at_intro {Ψ : MonPred I PROP → Prop} {q : MonPred I PROP} (i : I.car) (hq : Ψ q) :
    q.monPred_at i ⊢ (MonPred.sExists Ψ).monPred_at i :=
  sExists_intro ⟨q, hq, rfl⟩

theorem sExists_at_elim {Ψ : MonPred I PROP → Prop} {R : PROP} (i : I.car)
    (h : ∀ q, Ψ q → q.monPred_at i ⊢ R) : (MonPred.sExists Ψ).monPred_at i ⊢ R :=
  sExists_elim fun _ ⟨q, hq, hp⟩ => hp ▸ h q hq

@[rocq_alias monPred_defs.monPred_sep]
def sep (P Q : MonPred I PROP) : MonPred I PROP where
  monPred_at i := iprop(P.monPred_at i ∗ Q.monPred_at i)
  monPred_mono h := sep_mono (P.monPred_mono h) (Q.monPred_mono h)

#rocq_ignore monPred_defs.monPred_sep_def "Rocq unsealed definition body; use MonPred.sep."
#rocq_ignore monPred_defs.monPred_sep_aux "Rocq sealing auxiliary definition."
#rocq_ignore monPred_defs.monPred_sep_unseal "Rocq unsealing lemma."
#rocq_ignore monPred_sep_unseal "Rocq unsealing lemma."

@[rocq_alias monPred_defs.monPred_wand]
def wand (P Q : MonPred I PROP) : MonPred I PROP where
  monPred_at := MonPred.upclosed (fun i => iprop(P.monPred_at i -∗ Q.monPred_at i))
  monPred_mono h :=
    forall_intro fun k => (forall_elim k).trans
      (imp_mono_left (pure_mono fun hjk => Trans.trans h hjk))

#rocq_ignore monPred_defs.monPred_wand_def "Rocq unsealed definition body; use MonPred.wand."
#rocq_ignore monPred_defs.monPred_wand_aux "Rocq sealing auxiliary definition."
#rocq_ignore monPred_defs.monPred_wand_unseal "Rocq unsealing lemma."
#rocq_ignore monPred_wand_unseal "Rocq unsealing lemma."

@[rocq_alias monPred_defs.monPred_persistently]
def persistently (P : MonPred I PROP) : MonPred I PROP where
  monPred_at i := iprop(<pers> (P.monPred_at i))
  monPred_mono h := persistently_mono (P.monPred_mono h)

#rocq_ignore monPred_defs.monPred_persistently_def
  "Rocq unsealed definition body; use MonPred.persistently."
#rocq_ignore monPred_defs.monPred_persistently_aux "Rocq sealing auxiliary definition."
#rocq_ignore monPred_defs.monPred_persistently_unseal "Rocq unsealing lemma."
#rocq_ignore monPred_persistently_unseal "Rocq unsealing lemma."

@[rocq_alias monPred_defs.monPred_later]
def later (P : MonPred I PROP) : MonPred I PROP where
  monPred_at i := iprop(▷ (P.monPred_at i))
  monPred_mono h := later_mono (P.monPred_mono h)

#rocq_ignore monPred_defs.monPred_later_def "Rocq unsealed definition body; use MonPred.later."
#rocq_ignore monPred_defs.monPred_later_aux "Rocq sealing auxiliary definition."
#rocq_ignore monPred_defs.monPred_later_unseal "Rocq unsealing lemma."
#rocq_ignore monPred_later_unseal "Rocq unsealing lemma."

@[rocq_alias monPred_defs.monPred_in]
def monPred_in (j : I.car) : MonPred I PROP where
  monPred_at i := iprop(⌜I.rel.le j i⌝)
  monPred_mono h := pure_mono fun hji => Trans.trans hji h

#rocq_ignore monPred_defs.monPred_in_def "Rocq unsealed definition body; use MonPred.monPred_in."
#rocq_ignore monPred_defs.monPred_in_aux "Rocq sealing auxiliary definition."
#rocq_ignore monPred_defs.monPred_in_unseal "Rocq unsealing lemma."

@[rocq_alias monPred_defs.monPred_embed]
def embed (P : PROP) : MonPred I PROP where
  monPred_at _ := P
  monPred_mono _ := .rfl

#rocq_ignore monPred_defs.monPred_embed_def "Rocq unsealed definition body; use MonPred.embed."
#rocq_ignore monPred_defs.monPred_embed_aux "Rocq sealing auxiliary definition."
#rocq_ignore monPred_defs.monPred_embed_unseal "Rocq unsealing lemma."
#rocq_ignore monPred_embed_unseal "Rocq unsealing lemma."

/-- The "objectively" modality: `<obj> P` forces `P` at *every* index, so the result
is index-independent. -/
@[rocq_alias monPred_defs.monPred_objectively]
def objectively (P : MonPred I PROP) : MonPred I PROP where
  monPred_at _ := iprop(∀ i, P.monPred_at i)
  monPred_mono _ := .rfl

#rocq_ignore monPred_defs.monPred_objectively_def
  "Rocq unsealed definition body; use MonPred.objectively."
#rocq_ignore monPred_defs.monPred_objectively_aux "Rocq sealing auxiliary definition."
#rocq_ignore monPred_defs.monPred_objectively_unseal "Rocq unsealing lemma."
#rocq_ignore monPred_objectively_unfold "Rocq unfold lemma; Lean definitions are transparent."

/-- The "subjectively" modality: `<subj> P` holds if `P` holds at *some* index; the
result is index-independent. -/
@[rocq_alias monPred_defs.monPred_subjectively]
def subjectively (P : MonPred I PROP) : MonPred I PROP where
  monPred_at _ := iprop(∃ i, P.monPred_at i)
  monPred_mono _ := .rfl

#rocq_ignore monPred_defs.monPred_subjectively_def
  "Rocq unsealed definition body; use MonPred.subjectively."
#rocq_ignore monPred_defs.monPred_subjectively_aux "Rocq sealing auxiliary definition."
#rocq_ignore monPred_defs.monPred_subjectively_unseal "Rocq unsealing lemma."
#rocq_ignore monPred_subjectively_unfold "Rocq unfold lemma; Lean definitions are transparent."

end MonPred

section Instances
variable {I : BiIndex} {PROP : Type _} [BI PROP]

instance : BIBase (MonPred I PROP) where
  le            := MonPred.Entails
  emp           := MonPred.emp
  pure          := MonPred.pure
  and           := MonPred.and
  or            := MonPred.or
  imp           := MonPred.imp
  sForall       := MonPred.sForall
  sExists       := MonPred.sExists
  sep           := MonPred.sep
  wand          := MonPred.wand
  persistently  := MonPred.persistently
  later         := MonPred.later

@[rocq_alias monPred_at_entails]
theorem entails_at {P Q : MonPred I PROP} :
    (P ⊢ Q) ↔ ∀ i, P.monPred_at i ⊢ Q.monPred_at i := Iff.rfl

@[rocq_alias monPred_at_equiv]
theorem equiv_at {P Q : MonPred I PROP} :
    (P ≡ Q) ↔ ∀ i, P.monPred_at i ≡ Q.monPred_at i := forall_comm

@[rocq_alias monPred_at_dist]
theorem dist_at {n : Nat} {P Q : MonPred I PROP} :
    (P ≡{n}≡ Q) ↔ ∀ i, P.monPred_at i ≡{n}≡ Q.monPred_at i := Iff.rfl

#rocq_ignore monPred_dist "Covered by dist_at."
#rocq_ignore monPred_dist' "Covered by dist_at."
#rocq_ignore monPred_equiv "Covered by equiv_at."
#rocq_ignore monPred_equiv' "Covered by equiv_at."

/-- BI instance on monotone predicates (Rocq `monPred_bi_mixin` + persistently/later
mixins, packaged into `monPredI : bi`). -/
@[rocq_alias monPredI]
instance : BI (MonPred I PROP) where
  entails_preorder :=
    { le_refl _ := entails_at.mpr fun _ => BIBase.Entails.rfl
      le_trans := fun _ _ _ h h' => entails_at.mpr fun i => (entails_at.mp h i).trans (entails_at.mp h' i) }
  equiv_iff := fun {P Q} =>
    ⟨fun h => ⟨entails_at.mpr fun i => (equiv_iff.mp (equiv_at.mp h i)).mp,
              entails_at.mpr fun i => (equiv_iff.mp (equiv_at.mp h i)).mpr⟩,
     fun h => equiv_at.mpr fun i => equiv_iff.mpr ⟨entails_at.mp h.1 i, entails_at.mp h.2 i⟩⟩
  and_ne := ⟨fun _ _ _ h _ _ h' =>
    dist_at.mpr fun i => and_ne.ne (dist_at.mp h i) (dist_at.mp h' i)⟩
  or_ne := ⟨fun _ _ _ h _ _ h' => dist_at.mpr fun i => or_ne.ne (dist_at.mp h i) (dist_at.mp h' i)⟩
  imp_ne := ⟨fun _ _ _ h _ _ h' => dist_at.mpr fun i =>
    forall_ne fun j => imp_ne.ne Dist.rfl (imp_ne.ne (dist_at.mp h j) (dist_at.mp h' j))⟩
  sForall_ne := fun {n Ψ₁ Ψ₂} h => dist_at.mpr fun i =>
    Iris.BI.sForall_ne
      ⟨fun _ ⟨q, hq, hp⟩ =>
          let ⟨q', hq', hr⟩ := h.1 q hq; ⟨_, ⟨q', hq', rfl⟩, hp ▸ dist_at.mp hr i⟩,
       fun _ ⟨q, hq, hp⟩ =>
          let ⟨q', hq', hr⟩ := h.2 q hq; ⟨_, ⟨q', hq', rfl⟩, hp ▸ dist_at.mp hr i⟩⟩
  sExists_ne := fun {n Ψ₁ Ψ₂} h => dist_at.mpr fun i =>
    Iris.BI.sExists_ne
      ⟨fun _ ⟨q, hq, hp⟩ =>
          let ⟨q', hq', hr⟩ := h.1 q hq; ⟨_, ⟨q', hq', rfl⟩, hp ▸ dist_at.mp hr i⟩,
       fun _ ⟨q, hq, hp⟩ =>
          let ⟨q', hq', hr⟩ := h.2 q hq; ⟨_, ⟨q', hq', rfl⟩, hp ▸ dist_at.mp hr i⟩⟩
  sep_ne := ⟨fun _ _ _ h _ _ h' =>
    dist_at.mpr fun i => sep_ne.ne (dist_at.mp h i) (dist_at.mp h' i)⟩
  wand_ne := ⟨fun _ _ _ h _ _ h' => dist_at.mpr fun i =>
    forall_ne fun j => imp_ne.ne Dist.rfl (wand_ne.ne (dist_at.mp h j) (dist_at.mp h' j))⟩
  persistently_ne := ⟨fun _ _ _ h => dist_at.mpr fun i => persistently_ne.ne (dist_at.mp h i)⟩
  later_ne := ⟨fun _ _ _ h => dist_at.mpr fun i => later_ne.ne (dist_at.mp h i)⟩
  pure_intro h := entails_at.mpr fun i => pure_intro h
  pure_elim' := fun {φ P} h => entails_at.mpr fun i => pure_elim' fun hφ => entails_at.mp (h hφ) i
  and_elim_l := entails_at.mpr fun i => and_elim_l
  and_elim_r := entails_at.mpr fun i => and_elim_r
  and_intro h h' := entails_at.mpr fun i => and_intro (entails_at.mp h i) (entails_at.mp h' i)
  or_intro_l := entails_at.mpr fun i => or_intro_l
  or_intro_r := entails_at.mpr fun i => or_intro_r
  or_elim h h' := entails_at.mpr fun i => or_elim (entails_at.mp h i) (entails_at.mp h' i)
  imp_intro {P Q R} h := entails_at.mpr fun i =>
    forall_intro fun j => imp_intro <| pure_elim_right fun (hij : I.rel.le i j) =>
      (P.monPred_mono hij).trans <| imp_intro (entails_at.mp h j)
  imp_elim {P Q R} h := entails_at.mpr fun i =>
    imp_elim <| (entails_at.mp h i).trans <|
      (forall_elim i).trans <| pure_imp_elim (Std.Refl.refl i : I.rel.le i i)
  sForall_intro h := entails_at.mpr fun i =>
    MonPred.sForall_at_intro i fun q hΨ => entails_at.mp (h q hΨ) i
  sForall_elim h := entails_at.mpr fun i => MonPred.sForall_at_elim i h
  sExists_intro h := entails_at.mpr fun i => MonPred.sExists_at_intro i h
  sExists_elim h := entails_at.mpr fun i =>
    MonPred.sExists_at_elim i fun q hΨ => entails_at.mp (h q hΨ) i
  sep_mono h h' := entails_at.mpr fun i => sep_mono (entails_at.mp h i) (entails_at.mp h' i)
  emp_sep := ⟨entails_at.mpr fun i => emp_sep.mp, entails_at.mpr fun i => emp_sep.mpr⟩
  sep_symm := entails_at.mpr fun i => sep_symm
  sep_assoc_l := entails_at.mpr fun i => sep_assoc_l
  wand_intro {P Q R} h := entails_at.mpr fun i => by
    refine forall_intro fun j => imp_intro ?_
    refine pure_elim_right fun (hij : I.rel.le i j) => ?_
    refine wand_intro (sep_symm.trans ?_)
    exact (sep_mono_right (P.monPred_mono hij)).trans (sep_symm.trans (entails_at.mp h j))
  wand_elim {P Q R} h := entails_at.mpr fun i =>
    (sep_mono_left ((entails_at.mp h i).trans
      ((forall_elim i).trans (pure_imp_elim (Std.Refl.refl i : I.rel.le i i))))).trans wand_elim_left
  persistently_mono h := entails_at.mpr fun i => persistently_mono (entails_at.mp h i)
  persistently_idem_2 := entails_at.mpr fun i => persistently_idem_2
  persistently_emp_2 := entails_at.mpr fun i => persistently_emp_2
  persistently_and_2 := entails_at.mpr fun i => persistently_and_2
  persistently_sExists_1 := fun {Ψ} => entails_at.mpr fun i => by
    refine persistently_sExists_1.trans ?_
    refine exists_elim fun p => pure_elim_left fun ⟨q, hΨ, hq⟩ => ?_
    subst hq
    exact (and_intro (pure_intro hΨ) BIBase.Entails.rfl).trans
      (MonPred.sExists_at_intro (q := iprop(⌜Ψ q⌝ ∧ <pers> q)) i ⟨q, rfl⟩)
  persistently_absorb_l := entails_at.mpr fun i => persistently_absorb_l
  persistently_and_l := entails_at.mpr fun i => persistently_and_l
  later_mono h := entails_at.mpr fun i => later_mono (entails_at.mp h i)
  later_intro := entails_at.mpr fun i => later_intro
  later_sForall_2 := fun {Φ} => entails_at.mpr fun i => by
    refine .trans ?_ later_sForall_2
    refine sForall_intro fun _ ⟨_, ha⟩ => ?_
    subst ha
    refine imp_intro <| pure_elim_right ?_
    rintro ⟨r, hΦ, rfl⟩
    refine (MonPred.sForall_at_elim (q := MonPred.imp (MonPred.pure (Φ r)) (MonPred.later r))
        i ⟨r, rfl⟩).trans ?_
    refine (forall_elim i).trans ?_
    exact (pure_imp_elim (Std.Refl.refl i : I.rel.le i i)).trans (pure_imp_elim hΦ)
  later_sExists_false := fun {Φ} => entails_at.mpr fun i => by
    refine later_sExists_false.trans (or_mono BIBase.Entails.rfl ?_)
    refine exists_elim fun p => pure_elim_left fun ⟨q, hΦ, hq⟩ => ?_
    subst hq
    exact (and_intro (pure_intro hΦ) BIBase.Entails.rfl).trans
      (MonPred.sExists_at_intro (q := iprop(⌜Φ q⌝ ∧ ▷ q)) i ⟨q, rfl⟩)
  later_sep := ⟨entails_at.mpr fun i => later_sep.mp, entails_at.mpr fun i => later_sep.mpr⟩
  later_persistently :=
    ⟨entails_at.mpr fun i => later_persistently.mp,
     entails_at.mpr fun i => later_persistently.mpr⟩
  later_false_em {P} := entails_at.mpr fun i => by
    refine later_false_em.trans (or_mono_right ?_)
    refine forall_intro fun j => imp_intro ?_
    refine pure_elim_right fun (hij : I.rel.le i j) => ?_
    exact imp_mono BIBase.Entails.rfl (P.monPred_mono hij)

#rocq_ignore monPred_unseal "Rocq unsealing command."
#rocq_ignore monPred_unseal_bi "Rocq unsealing command."
#rocq_ignore monPred_defs.monPred_unseal "Rocq unsealing lemma."
#rocq_ignore monPred_bi_mixin "Rocq mixin record; subsumed by monPredI."
#rocq_ignore monPred_bi_persistently_mixin "Rocq mixin record; subsumed by monPredI."
#rocq_ignore monPred_bi_later_mixin "Rocq mixin record; subsumed by monPredI."
#rocq_ignore monPred_bi_pure_forall
  "BIPureForall is provable for all BIs classically; see pure_forall_2."

end Instances

/-! ### Embedding of the base BI into MonPred -/

section Embedding
variable {I : BiIndex} {PROP : Type _} [BI PROP]

@[rocq_alias monPred_bi_embed]
instance : BiEmbed PROP (MonPred I PROP) where
  embed := MonPred.embed
  ne := ⟨fun _ _ _ h => dist_at.mpr fun _ => h⟩
  mono h := entails_at.mpr fun _ => h
  emp_valid_inj _ h := entails_at.mp h (Inhabited.default : I.car)
  emp_2 := entails_at.mpr fun _ => .rfl
  impl_2 _ _ := entails_at.mpr fun i =>
    (forall_elim i).trans (pure_imp_elim (Std.Refl.refl i : I.rel.le i i))
  forall_2 := fun _Ψ {_} h => entails_at.mpr fun i =>
    sForall_intro fun P hΨ => entails_at.mp (h P hΨ) i
  exist_1 := fun _Ψ {_} h => entails_at.mpr fun i =>
    sExists_elim fun P hΨ => entails_at.mp (h P hΨ) i
  sep _ _ := BIBase.BiEntails.of_eq rfl
  wand_2 _ _ := entails_at.mpr fun i =>
    (forall_elim i).trans (pure_imp_elim (Std.Refl.refl i : I.rel.le i i))
  persistently _ := BIBase.BiEntails.of_eq rfl

#rocq_ignore monPred_embedding_mixin "Rocq mixin record; subsumed by the BiEmbed instance."

@[rocq_alias monPred_bi_embed_emp]
instance : BiEmbedEmp PROP (MonPred I PROP) where
  embed_emp_1 := (BIBase.BiEntails.of_eq (MonPred.ext fun _ => rfl)).mp

@[rocq_alias monPred_bi_embed_later]
instance : BiEmbedLater PROP (MonPred I PROP) where
  embed_later _ := BIBase.BiEntails.of_eq (MonPred.ext fun _ => rfl)

end Embedding

/-! ### BI extension instances -/

section Extensions
variable {I : BiIndex} {PROP : Type _} [BI PROP]

@[rocq_alias monPred_bi_löb]
instance [BILoeb PROP] : BILoeb (MonPred I PROP) where
  loeb_weak h := entails_at.mpr fun i => loeb_weak (entails_at.mp h i)

@[rocq_alias monPred_bi_positive]
instance [BIPositive PROP] : BIPositive (MonPred I PROP) where
  affinely_sep_l := entails_at.mpr fun _ => affinely_sep_l

@[rocq_alias monPred_bi_affine]
instance [BIAffine PROP] : BIAffine (MonPred I PROP) where
  affine P := ⟨entails_at.mpr fun _ => (BIAffine.affine (P.monPred_at _)).affine⟩

@[rocq_alias monPred_bi_persistently_forall]
instance [BIPersistentlyForall PROP] : BIPersistentlyForall (MonPred I PROP) where
  persistently_sForall_2 Ψ := entails_at.mpr fun i =>
    (forall_intro fun _ =>
      imp_intro_swap <|
      pure_elim_left fun ⟨q, hΨq, hqip⟩ =>
        hqip ▸ entails_at.mp
          (imp_mp (forall_elim (Ψ := fun p : MonPred I PROP => iprop(⌜Ψ p⌝ → <pers> p)) q)
            (pure_intro hΨq)) i).trans
    (BIPersistentlyForall.persistently_sForall_2
      (fun p => ∃ q : MonPred I PROP, Ψ q ∧ q.monPred_at i = p))

@[rocq_alias monPred_bi_later_contractive]
instance [BILaterContractive PROP] : BILaterContractive (MonPred I PROP) where
  distLater_dist h := dist_at.mpr fun i =>
    (‹BILaterContractive PROP›).distLater_dist fun m hm => dist_at.mp (h m hm) i

end Extensions

/-! ### BUpd / FUpd instances -/

section Updates
variable {I : BiIndex} {PROP : Type _} [BI PROP]

/-- Pointwise basic update on `MonPred I PROP`. Rocq `monPred_defs.monPred_bupd_def`. -/
@[rocq_alias monPred_defs.monPred_bupd]
def MonPred.bupd [BIUpdate PROP] (P : MonPred I PROP) : MonPred I PROP :=
  MonPred.mk (fun i => BUpd.bupd (P.monPred_at i)) fun h => BIUpdate.mono (P.monPred_mono h)

#rocq_ignore monPred_defs.monPred_bupd_def "Rocq unsealed definition body; use MonPred.bupd."
#rocq_ignore monPred_defs.monPred_bupd_aux "Rocq sealing auxiliary definition."
#rocq_ignore monPred_defs.monPred_bupd_unseal "Rocq unsealing lemma."
#rocq_ignore monPred_bupd_unseal "Rocq unsealing lemma."

@[rocq_alias monPred_bi_bupd]
instance [BIUpdate PROP] : BIUpdate (MonPred I PROP) where
  bupd := MonPred.bupd
  bupd_ne := ⟨fun _ _ _ h => dist_at.mpr fun i => bupd_ne.ne (dist_at.mp h i)⟩
  intro := entails_at.mpr fun _ => bupd_intro
  mono h := entails_at.mpr fun i => BIUpdate.mono (entails_at.mp h i)
  trans := entails_at.mpr fun _ => BIUpdate.trans
  frame_right := entails_at.mpr fun _ => bupd_frame_right

#rocq_ignore monPred_bupd_mixin "Rocq mixin record; subsumed by the BIUpdate instance."

@[rocq_alias monPred_bi_embed_bupd]
instance [BIUpdate PROP] : BiEmbedBUpd PROP (MonPred I PROP) where
  embed_bupd _ := BIBase.BiEntails.of_eq (MonPred.ext fun _ => rfl)

/-- Pointwise fancy update on `MonPred I PROP`. Rocq `monPred_defs.monPred_fupd_def`. -/
@[rocq_alias monPred_defs.monPred_fupd]
def MonPred.fupd [BIFUpdate PROP] (E1 E2 : CoPset) (P : MonPred I PROP) : MonPred I PROP :=
  MonPred.mk (fun i => FUpd.fupd E1 E2 (P.monPred_at i)) fun h =>
    BIFUpdate.mono (P.monPred_mono h)

#rocq_ignore monPred_defs.monPred_fupd_def "Rocq unsealed definition body; use MonPred.fupd."
#rocq_ignore monPred_defs.monPred_fupd_aux "Rocq sealing auxiliary definition."
#rocq_ignore monPred_defs.monPred_fupd_unseal "Rocq unsealing lemma."
#rocq_ignore monPred_fupd_unseal "Rocq unsealing lemma."

@[rocq_alias monPred_bi_fupd]
instance [BIFUpdate PROP] : BIFUpdate (MonPred I PROP) where
  fupd := MonPred.fupd
  ne := ⟨fun _ _ _ h => dist_at.mpr fun i => BIFUpdate.ne.ne (dist_at.mp h i)⟩
  subset h := entails_at.mpr fun _ => BIFUpdate.subset h
  except0 := entails_at.mpr fun _ => BIFUpdate.except0
  mono h := entails_at.mpr fun i => BIFUpdate.mono (entails_at.mp h i)
  trans := entails_at.mpr fun _ => BIFUpdate.trans
  mask_frame_right_strong h := entails_at.mpr fun i =>
    (BIFUpdate.mono
      (((forall_elim i).trans (pure_imp_elim (Std.Refl.refl i : I.rel.le i i))) : _ ⊢@{PROP} _)).trans
      (BIFUpdate.mask_frame_right_strong h)
  frame_right := entails_at.mpr fun _ => fupd_frame_right

#rocq_ignore monPred_fupd_mixin "Rocq mixin record; subsumed by the BIFUpdate instance."

@[rocq_alias monPred_bi_bupd_fupd]
instance [BIUpdate PROP] [BIFUpdate PROP] [BIUpdateFUpdate PROP] :
    BIUpdateFUpdate (MonPred I PROP) where
  fupd_of_bupd := entails_at.mpr fun _ => BIUpdateFUpdate.fupd_of_bupd

@[rocq_alias monPred_bi_embed_fupd]
instance [BIFUpdate PROP] : BiEmbedFUpd PROP (MonPred I PROP) where
  embed_fupd _ _ _ := BIBase.BiEntails.of_eq (MonPred.ext fun _ => rfl)

end Updates

/-- A monotone predicate `P` is *objective* if its value does not depend on the
index: `P i ⊢ P j` for all `i j`. Equivalently `P ⊣⊢ <obj> P`. -/
@[rocq_alias Objective]
class Objective {I : BiIndex} {PROP : Type _} [BI PROP] (P : MonPred I PROP) : Prop where
  objective_at : ∀ i j : I.car, P.monPred_at i ⊢ P.monPred_at j

namespace MonPred
variable {I : BiIndex} {PROP : Type _} [BI PROP]

@[rocq_alias monPred_at_emp]
theorem monPred_at_emp (i : I.car) :
    (iprop(emp) : MonPred I PROP).monPred_at i ⊣⊢ iprop(emp) :=
  BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_pure]
theorem monPred_at_pure (i : I.car) (φ : Prop) :
    (iprop(⌜φ⌝) : MonPred I PROP).monPred_at i ⊣⊢ iprop(⌜φ⌝) :=
  BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_and]
theorem monPred_at_and (i : I.car) (P Q : MonPred I PROP) :
    (iprop(P ∧ Q)).monPred_at i ⊣⊢ iprop(P.monPred_at i ∧ Q.monPred_at i) :=
  BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_or]
theorem monPred_at_or (i : I.car) (P Q : MonPred I PROP) :
    (iprop(P ∨ Q)).monPred_at i ⊣⊢ iprop(P.monPred_at i ∨ Q.monPred_at i) :=
  BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_impl]
theorem monPred_at_impl (i : I.car) (P Q : MonPred I PROP) :
    (iprop(P → Q)).monPred_at i ⊣⊢
      iprop(∀ j, ⌜I.rel.le i j⌝ → (P.monPred_at j → Q.monPred_at j)) :=
  BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_forall]
theorem monPred_at_forall {α : Sort _} (i : I.car) (Φ : α → MonPred I PROP) :
    (iprop(∀ x, Φ x)).monPred_at i ⊣⊢ iprop(∀ x, (Φ x).monPred_at i) :=
  ⟨forall_intro fun x => MonPred.sForall_at_elim i ⟨x, rfl⟩,
   MonPred.sForall_at_intro i fun _ ⟨x, hx⟩ => hx ▸ forall_elim x⟩

@[rocq_alias monPred_at_exist]
theorem monPred_at_exist {α : Sort _} (i : I.car) (Φ : α → MonPred I PROP) :
    (iprop(∃ x, Φ x)).monPred_at i ⊣⊢ iprop(∃ x, (Φ x).monPred_at i) :=
  ⟨MonPred.sExists_at_elim i fun _ ⟨x, hx⟩ =>
    hx ▸ exists_intro (Ψ := fun y => (Φ y).monPred_at i) x,
   exists_elim fun x => MonPred.sExists_at_intro i ⟨x, rfl⟩⟩

@[rocq_alias monPred_at_sep]
theorem monPred_at_sep (i : I.car) (P Q : MonPred I PROP) :
    (iprop(P ∗ Q)).monPred_at i ⊣⊢ iprop(P.monPred_at i ∗ Q.monPred_at i) :=
  BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_wand]
theorem monPred_at_wand (i : I.car) (P Q : MonPred I PROP) :
    (iprop(P -∗ Q)).monPred_at i ⊣⊢
      iprop(∀ j, ⌜I.rel.le i j⌝ → (P.monPred_at j -∗ Q.monPred_at j)) :=
  BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_persistently]
theorem monPred_at_persistently (i : I.car) (P : MonPred I PROP) :
    (iprop(<pers> P)).monPred_at i ⊣⊢ iprop(<pers> (P.monPred_at i)) :=
  BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_later]
theorem monPred_at_later (i : I.car) (P : MonPred I PROP) :
    (iprop(▷ P)).monPred_at i ⊣⊢ iprop(▷ (P.monPred_at i)) :=
  BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_in]
theorem monPred_at_in (i j : I.car) :
    (MonPred.monPred_in j : MonPred I PROP).monPred_at i ⊣⊢ iprop(⌜I.rel.le j i⌝) :=
  BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_embed]
theorem monPred_at_embed (i : I.car) (P : PROP) :
    (MonPred.embed P : MonPred I PROP).monPred_at i ⊣⊢ P :=
  BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_objectively]
theorem monPred_at_objectively (i : I.car) (P : MonPred I PROP) :
    (MonPred.objectively P).monPred_at i ⊣⊢ iprop(∀ j, P.monPred_at j) :=
  BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_subjectively]
theorem monPred_at_subjectively (i : I.car) (P : MonPred I PROP) :
    (MonPred.subjectively P).monPred_at i ⊣⊢ iprop(∃ j, P.monPred_at j) :=
  BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_affinely]
theorem monPred_at_affinely (i : I.car) (P : MonPred I PROP) :
    (iprop(<affine> P) : MonPred I PROP).monPred_at i ⊣⊢ iprop(<affine> (P.monPred_at i)) :=
  BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_absorbingly]
theorem monPred_at_absorbingly (i : I.car) (P : MonPred I PROP) :
    (iprop(<absorb> P) : MonPred I PROP).monPred_at i ⊣⊢ iprop(<absorb> (P.monPred_at i)) :=
  BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_intuitionistically]
theorem monPred_at_intuitionistically (i : I.car) (P : MonPred I PROP) :
    (iprop(□ P) : MonPred I PROP).monPred_at i ⊣⊢ iprop(□ (P.monPred_at i)) :=
  BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_affinely_if]
theorem monPred_at_affinely_if (i : I.car) (p : Bool) (P : MonPred I PROP) :
    (iprop(<affine>?p P) : MonPred I PROP).monPred_at i ⊣⊢ iprop(<affine>?p (P.monPred_at i)) := by
  cases p <;> exact BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_absorbingly_if]
theorem monPred_at_absorbingly_if (i : I.car) (p : Bool) (P : MonPred I PROP) :
    (iprop(<absorb>?p P) : MonPred I PROP).monPred_at i ⊣⊢ iprop(<absorb>?p (P.monPred_at i)) := by
  cases p <;> exact BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_intuitionistically_if]
theorem monPred_at_intuitionistically_if (i : I.car) (p : Bool) (P : MonPred I PROP) :
    (iprop(□?p P) : MonPred I PROP).monPred_at i ⊣⊢ iprop(□?p (P.monPred_at i)) := by
  cases p <;> exact BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_persistently_if]
theorem monPred_at_persistently_if (i : I.car) (p : Bool) (P : MonPred I PROP) :
    (iprop(<pers>?p P) : MonPred I PROP).monPred_at i ⊣⊢ iprop(<pers>?p (P.monPred_at i)) := by
  cases p <;> exact BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_except_0]
theorem monPred_at_except_0 (i : I.car) (P : MonPred I PROP) :
    (iprop(◇ P) : MonPred I PROP).monPred_at i ⊣⊢ iprop(◇ (P.monPred_at i)) :=
  BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_laterN]
theorem monPred_at_laterN (n : Nat) (i : I.car) (P : MonPred I PROP) :
    (iprop(▷^[n] P) : MonPred I PROP).monPred_at i ⊣⊢ iprop(▷^[n] (P.monPred_at i)) := by
  induction n with
  | zero => exact .rfl
  | succ n ih => exact (monPred_at_later i _).trans (later_congr ih)

@[rocq_alias monPred_at_bupd]
theorem monPred_at_bupd [BIUpdate PROP] (i : I.car) (P : MonPred I PROP) :
    (iprop(|==> P) : MonPred I PROP).monPred_at i ⊣⊢ iprop(|==> (P.monPred_at i)) :=
  BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_fupd]
theorem monPred_at_fupd [BIFUpdate PROP] (i : I.car) (E1 E2 : CoPset) (P : MonPred I PROP) :
    (iprop(|={E1,E2}=> P) : MonPred I PROP).monPred_at i ⊣⊢ iprop(|={E1,E2}=> (P.monPred_at i)) :=
  BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_emp_valid]
theorem monPred_at_emp_valid (P : MonPred I PROP) : (⊢ P) ↔ ∀ i, ⊢ P.monPred_at i :=
  entails_at

@[rocq_alias monPred_at_mono]
theorem monPred_at_mono {P Q : MonPred I PROP} {i j : I.car} (h : P ⊢ Q) (hij : I.rel.le i j) :
    P.monPred_at i ⊢ Q.monPred_at j :=
  (entails_at.mp h i).trans (Q.monPred_mono hij)

@[rocq_alias monPred_at_flip_mono]
theorem monPred_at_flip_mono {P Q : MonPred I PROP} {i j : I.car} (h : Q ⊢ P) (hij : I.rel.le j i) :
    Q.monPred_at j ⊢ P.monPred_at i :=
  monPred_at_mono h hij

@[rocq_alias monPred_at_ne]
theorem monPred_at_ne (i : I.car) :
    OFE.NonExpansive (fun P : MonPred I PROP => P.monPred_at i) :=
  ⟨fun _ _ _ h => dist_at.mp h i⟩

#rocq_ignore monPred_at_proper "Use monPred_at_ne / monPred_at_mono."

@[rocq_alias monPred_at_persistent]
instance monPred_at_persistent (P : MonPred I PROP) [Persistent P] (i : I.car) :
    Persistent (P.monPred_at i) where
  persistent := entails_at.mp persistent i

@[rocq_alias monPred_at_absorbing]
instance monPred_at_absorbing (P : MonPred I PROP) [Absorbing P] (i : I.car) :
    Absorbing (P.monPred_at i) where
  absorbing := (monPred_at_absorbingly i P).mpr.trans (entails_at.mp absorbing i)

@[rocq_alias monPred_at_affine]
instance monPred_at_affine (P : MonPred I PROP) [Affine P] (i : I.car) :
    Affine (P.monPred_at i) where
  affine := entails_at.mp affine i

@[rocq_alias monPred_at_timeless]
instance monPred_at_timeless (P : MonPred I PROP) [Timeless P] (i : I.car) :
    Timeless (P.monPred_at i) where
  timeless := (entails_at.mp Timeless.timeless i).trans (monPred_at_except_0 i P).mp

@[rocq_alias monPred_persistent]
instance monPred_persistent (P : MonPred I PROP) [∀ i, Persistent (P.monPred_at i)] :
    Persistent P where
  persistent := entails_at.mpr fun _ => Persistent.persistent

@[rocq_alias monPred_absorbing]
instance monPred_absorbing (P : MonPred I PROP) [∀ i, Absorbing (P.monPred_at i)] :
    Absorbing P where
  absorbing := entails_at.mpr fun _ => Absorbing.absorbing

@[rocq_alias monPred_affine]
instance monPred_affine (P : MonPred I PROP) [∀ i, Affine (P.monPred_at i)] :
    Affine P where
  affine := entails_at.mpr fun _ => Affine.affine

@[rocq_alias monPred_impl_force]
theorem monPred_impl_force (i : I.car) (P Q : MonPred I PROP) :
    (iprop(P → Q) : MonPred I PROP).monPred_at i ⊢ iprop(P.monPred_at i → Q.monPred_at i) :=
  (forall_elim i).trans (pure_imp_elim (Std.Refl.refl i : I.rel.le i i))

@[rocq_alias monPred_wand_force]
theorem monPred_wand_force (i : I.car) (P Q : MonPred I PROP) :
    (iprop(P -∗ Q) : MonPred I PROP).monPred_at i ⊢ iprop(P.monPred_at i -∗ Q.monPred_at i) :=
  (forall_elim i).trans (pure_imp_elim (Std.Refl.refl i : I.rel.le i i))

/-! ### The `monPred_in` assertion -/

@[rocq_alias monPred_in_intro]
theorem monPred_in_intro (P : MonPred I PROP) :
    P ⊢ iprop(∃ i, MonPred.monPred_in i ∧ ⎡P.monPred_at i⎤) :=
  entails_at.mpr fun j =>
    (and_intro (pure_intro (Std.Refl.refl j : I.rel.le j j)) .rfl).trans <|
      (exists_intro (Ψ := fun i =>
          (iprop(MonPred.monPred_in i ∧ ⎡P.monPred_at i⎤) : MonPred I PROP).monPred_at j) j).trans
        (monPred_at_exist j fun i => iprop(MonPred.monPred_in i ∧ ⎡P.monPred_at i⎤)).mpr

@[rocq_alias monPred_in_elim]
theorem monPred_in_elim (P : MonPred I PROP) (i : I.car) :
    (MonPred.monPred_in i : MonPred I PROP) ⊢ iprop(⎡P.monPred_at i⎤ → P) :=
  entails_at.mpr fun j =>
    pure_elim (I.rel.le i j) .rfl fun hij =>
      forall_intro fun _k => imp_intro_swap <| pure_elim_left fun hjk =>
        imp_intro <| and_elim_r.trans (P.monPred_mono (Trans.trans hij hjk))

@[rocq_alias monPred_in_mono]
theorem monPred_in_mono {i j : I.car} (h : I.rel.le j i) :
    (MonPred.monPred_in i : MonPred I PROP) ⊢ MonPred.monPred_in j :=
  entails_at.mpr fun _ => pure_mono fun hik => Trans.trans h hik

#rocq_ignore monPred_in_proper "Use monPred_in_mono."

@[rocq_alias monPred_in_flip_mono]
theorem monPred_in_flip_mono {i j : I.car} (h : I.rel.le i j) :
    (MonPred.monPred_in j : MonPred I PROP) ⊢ MonPred.monPred_in i :=
  monPred_in_mono h

@[rocq_alias monPred_in_persistent]
instance monPred_in_persistent (i : I.car) :
    Persistent (MonPred.monPred_in i : MonPred I PROP) where
  persistent := entails_at.mpr fun j => (pure_persistent (I.rel.le i j)).persistent

@[rocq_alias monPred_in_absorbing]
instance monPred_in_absorbing (i : I.car) :
    Absorbing (MonPred.monPred_in i : MonPred I PROP) where
  absorbing := entails_at.mpr fun j => (pure_absorbing (I.rel.le i j)).absorbing

@[rocq_alias monPred_in_timeless]
instance monPred_in_timeless (i : I.car) :
    Timeless (MonPred.monPred_in i : MonPred I PROP) where
  timeless := entails_at.mpr fun j => (pure_timeless (I.rel.le i j)).timeless

/-! ### Objective predicates -/

@[rocq_alias embed_objective]
instance embed_objective (P : PROP) : Objective (iprop(⎡P⎤) : MonPred I PROP) where
  objective_at _ _ := .rfl

@[rocq_alias pure_objective]
instance pure_objective (φ : Prop) : Objective (iprop(⌜φ⌝) : MonPred I PROP) where
  objective_at _ _ := .rfl

@[rocq_alias emp_objective]
instance emp_objective : Objective (iprop(emp) : MonPred I PROP) where
  objective_at _ _ := .rfl

@[rocq_alias objectively_objective]
instance objectively_objective (P : MonPred I PROP) : Objective (MonPred.objectively P) where
  objective_at _ _ := .rfl

@[rocq_alias subjectively_objective]
instance subjectively_objective (P : MonPred I PROP) : Objective (MonPred.subjectively P) where
  objective_at _ _ := .rfl

@[rocq_alias and_objective]
instance and_objective (P Q : MonPred I PROP) [Objective P] [Objective Q] :
    Objective (iprop(P ∧ Q)) where
  objective_at i j := and_mono (Objective.objective_at i j) (Objective.objective_at i j)

@[rocq_alias or_objective]
instance or_objective (P Q : MonPred I PROP) [Objective P] [Objective Q] :
    Objective (iprop(P ∨ Q)) where
  objective_at i j := or_mono (Objective.objective_at i j) (Objective.objective_at i j)

@[rocq_alias sep_objective]
instance sep_objective (P Q : MonPred I PROP) [Objective P] [Objective Q] :
    Objective (iprop(P ∗ Q)) where
  objective_at i j := sep_mono (Objective.objective_at i j) (Objective.objective_at i j)

@[rocq_alias impl_objective]
instance impl_objective (P Q : MonPred I PROP) [Objective P] [Objective Q] :
    Objective (iprop(P → Q)) where
  objective_at i _j := forall_intro fun k => imp_intro <|
    and_elim_l.trans <|
      (((forall_elim i).trans (pure_imp_elim (Std.Refl.refl i : I.rel.le i i))) : _ ⊢@{PROP} _).trans <|
      imp_mono (Objective.objective_at k i) (Objective.objective_at i k)

@[rocq_alias wand_objective]
instance wand_objective (P Q : MonPred I PROP) [Objective P] [Objective Q] :
    Objective (iprop(P -∗ Q)) where
  objective_at i _j := forall_intro fun k => imp_intro <|
    and_elim_l.trans <|
      (((forall_elim i).trans (pure_imp_elim (Std.Refl.refl i : I.rel.le i i))) : _ ⊢@{PROP} _).trans <|
      wand_mono (Objective.objective_at k i) (Objective.objective_at i k)

@[rocq_alias forall_objective]
instance forall_objective {α : Sort _} (Φ : α → MonPred I PROP) [∀ x, Objective (Φ x)] :
    Objective (iprop(∀ x, Φ x)) where
  objective_at i j := (monPred_at_forall i Φ).mp.trans <|
    (forall_mono fun _ => Objective.objective_at i j).trans (monPred_at_forall j Φ).mpr

@[rocq_alias exists_objective]
instance exists_objective {α : Sort _} (Φ : α → MonPred I PROP) [∀ x, Objective (Φ x)] :
    Objective (iprop(∃ x, Φ x)) where
  objective_at i j := (monPred_at_exist i Φ).mp.trans <|
    (exists_mono fun _ => Objective.objective_at i j).trans (monPred_at_exist j Φ).mpr

@[rocq_alias persistently_objective]
instance persistently_objective (P : MonPred I PROP) [Objective P] :
    Objective (iprop(<pers> P)) where
  objective_at i j := persistently_mono (Objective.objective_at i j)

@[rocq_alias affinely_objective]
instance affinely_objective (P : MonPred I PROP) [Objective P] :
    Objective (iprop(<affine> P)) where
  objective_at i j := affinely_mono (Objective.objective_at i j)

@[rocq_alias absorbingly_objective]
instance absorbingly_objective (P : MonPred I PROP) [Objective P] :
    Objective (iprop(<absorb> P)) where
  objective_at i j := absorbingly_mono (Objective.objective_at i j)

@[rocq_alias intuitionistically_objective]
instance intuitionistically_objective (P : MonPred I PROP) [Objective P] :
    Objective (iprop(□ P)) where
  objective_at i j := intuitionistically_mono (Objective.objective_at i j)

@[rocq_alias persistently_if_objective]
instance persistently_if_objective (p : Bool) (P : MonPred I PROP) [Objective P] :
    Objective (iprop(<pers>?p P)) where
  objective_at i j := (monPred_at_persistently_if i p P).mp.trans <|
    (persistentlyIf_mono (Objective.objective_at i j)).trans (monPred_at_persistently_if j p P).mpr

@[rocq_alias affinely_if_objective]
instance affinely_if_objective (p : Bool) (P : MonPred I PROP) [Objective P] :
    Objective (iprop(<affine>?p P)) where
  objective_at i j := (monPred_at_affinely_if i p P).mp.trans <|
    (affinelyIf_mono (Objective.objective_at i j)).trans (monPred_at_affinely_if j p P).mpr

@[rocq_alias absorbingly_if_objective]
instance absorbingly_if_objective (p : Bool) (P : MonPred I PROP) [Objective P] :
    Objective (iprop(<absorb>?p P)) where
  objective_at i j := (monPred_at_absorbingly_if i p P).mp.trans <|
    (absorbinglyIf_mono (Objective.objective_at i j)).trans (monPred_at_absorbingly_if j p P).mpr

@[rocq_alias intuitionistically_if_objective]
instance intuitionistically_if_objective (p : Bool) (P : MonPred I PROP) [Objective P] :
    Objective (iprop(□?p P)) where
  objective_at i j := (monPred_at_intuitionistically_if i p P).mp.trans <|
    (intuitionisticallyIf_mono (Objective.objective_at i j)).trans
      (monPred_at_intuitionistically_if j p P).mpr

@[rocq_alias later_objective]
instance later_objective (P : MonPred I PROP) [Objective P] : Objective (iprop(▷ P)) where
  objective_at i j := later_mono (Objective.objective_at i j)

@[rocq_alias laterN_objective]
instance laterN_objective (n : Nat) (P : MonPred I PROP) [Objective P] :
    Objective (iprop(▷^[n] P)) where
  objective_at i j := (monPred_at_laterN n i P).mp.trans <|
    (laterN_mono n (Objective.objective_at i j)).trans (monPred_at_laterN n j P).mpr

@[rocq_alias except0_objective]
instance except0_objective (P : MonPred I PROP) [Objective P] : Objective (iprop(◇ P)) where
  objective_at i j := except0_mono (Objective.objective_at i j)

@[rocq_alias bupd_objective]
instance bupd_objective [BIUpdate PROP] (P : MonPred I PROP) [Objective P] :
    Objective (iprop(|==> P)) where
  objective_at i j := BIUpdate.mono (Objective.objective_at i j)

@[rocq_alias fupd_objective]
instance fupd_objective [BIFUpdate PROP] (E1 E2 : CoPset) (P : MonPred I PROP) [Objective P] :
    Objective (iprop(|={E1,E2}=> P)) where
  objective_at i j := BIFUpdate.mono (Objective.objective_at i j)

/-! ### The `objectively` modality -/

@[rocq_alias objective_objectively]
theorem objective_objectively (P : MonPred I PROP) [Objective P] :
    P ⊢ MonPred.objectively P :=
  entails_at.mpr fun i => forall_intro fun k => Objective.objective_at i k

@[rocq_alias objective_subjectively]
theorem objective_subjectively (P : MonPred I PROP) [Objective P] :
    MonPred.subjectively P ⊢ P :=
  entails_at.mpr fun i => exists_elim fun k => Objective.objective_at k i

@[rocq_alias monPred_objectively_elim]
theorem monPred_objectively_elim (P : MonPred I PROP) : MonPred.objectively P ⊢ P :=
  entails_at.mpr fun i => forall_elim i

@[rocq_alias monPred_objectively_idemp]
theorem monPred_objectively_idemp (P : MonPred I PROP) :
    MonPred.objectively (MonPred.objectively P) ⊣⊢ MonPred.objectively P :=
  ⟨monPred_objectively_elim _, objective_objectively _⟩

@[rocq_alias monPred_objectively_mono]
theorem monPred_objectively_mono {P Q : MonPred I PROP} (h : P ⊢ Q) :
    MonPred.objectively P ⊢ MonPred.objectively Q :=
  entails_at.mpr fun _ => forall_mono fun k => entails_at.mp h k

@[rocq_alias monPred_objectively_ne]
theorem monPred_objectively_ne :
    OFE.NonExpansive (MonPred.objectively (I := I) (PROP := PROP)) :=
  ⟨fun _ _ _ h => dist_at.mpr fun _ => forall_ne fun k => dist_at.mp h k⟩

#rocq_ignore monPred_objectively_mono' "Use monPred_objectively_mono."
#rocq_ignore monPred_objectively_flip_mono' "Use monPred_objectively_mono."
#rocq_ignore monPred_objectively_proper "Use monPred_objectively_ne."

@[rocq_alias monPred_objectively_embed]
theorem monPred_objectively_embed (P : PROP) :
    MonPred.objectively (iprop(⎡P⎤) : MonPred I PROP) ⊣⊢ iprop(⎡P⎤) :=
  ⟨monPred_objectively_elim _, objective_objectively _⟩

@[rocq_alias monPred_objectively_emp]
theorem monPred_objectively_emp :
    MonPred.objectively (iprop(emp) : MonPred I PROP) ⊣⊢ iprop(emp) :=
  ⟨monPred_objectively_elim _, objective_objectively _⟩

@[rocq_alias monPred_objectively_pure]
theorem monPred_objectively_pure (φ : Prop) :
    MonPred.objectively (iprop(⌜φ⌝) : MonPred I PROP) ⊣⊢ iprop(⌜φ⌝) :=
  ⟨monPred_objectively_elim _, objective_objectively _⟩

@[rocq_alias monPred_objectively_and]
theorem monPred_objectively_and (P Q : MonPred I PROP) :
    MonPred.objectively (iprop(P ∧ Q)) ⊣⊢ iprop(MonPred.objectively P ∧ MonPred.objectively Q) :=
  ⟨entails_at.mpr fun _ => and_intro
      (forall_intro fun k => (forall_elim k).trans and_elim_l)
      (forall_intro fun k => (forall_elim k).trans and_elim_r),
   entails_at.mpr fun _ => forall_intro fun k =>
      and_intro (and_elim_l.trans (forall_elim k)) (and_elim_r.trans (forall_elim k))⟩

@[rocq_alias monPred_objectively_or]
theorem monPred_objectively_or (P Q : MonPred I PROP) :
    iprop(MonPred.objectively P ∨ MonPred.objectively Q) ⊢ MonPred.objectively (iprop(P ∨ Q)) :=
  entails_at.mpr fun _ => or_elim
    (forall_intro fun k => (forall_elim k).trans or_intro_l)
    (forall_intro fun k => (forall_elim k).trans or_intro_r)

@[rocq_alias monPred_objectively_forall]
theorem monPred_objectively_forall {α : Sort _} (Φ : α → MonPred I PROP) :
    MonPred.objectively (iprop(∀ x, Φ x)) ⊣⊢ iprop(∀ x, MonPred.objectively (Φ x)) :=
  ⟨entails_at.mpr fun i =>
      (forall_intro fun x => forall_intro fun k =>
        (forall_elim k).trans <| (monPred_at_forall k Φ).mp.trans (forall_elim x)).trans
      (monPred_at_forall i fun x => MonPred.objectively (Φ x)).mpr,
   entails_at.mpr fun i =>
      forall_intro fun k =>
        ((monPred_at_forall i fun x => MonPred.objectively (Φ x)).mp.trans
          (forall_intro fun x => (forall_elim x).trans (forall_elim k))).trans
        (monPred_at_forall k Φ).mpr⟩

@[rocq_alias monPred_objectively_exist]
theorem monPred_objectively_exist {α : Sort _} (Φ : α → MonPred I PROP) :
    iprop(∃ x, MonPred.objectively (Φ x)) ⊢ MonPred.objectively (iprop(∃ x, Φ x)) :=
  entails_at.mpr fun i =>
    (monPred_at_exist i fun x => MonPred.objectively (Φ x)).mp.trans <|
    exists_elim fun x => forall_intro fun k =>
      ((forall_elim k).trans (exists_intro (Ψ := fun x => (Φ x).monPred_at k) x)).trans
        (monPred_at_exist k Φ).mpr

@[rocq_alias monPred_objectively_sep_2]
theorem monPred_objectively_sep_2 (P Q : MonPred I PROP) :
    iprop(MonPred.objectively P ∗ MonPred.objectively Q) ⊢ MonPred.objectively (iprop(P ∗ Q)) :=
  entails_at.mpr fun _ => forall_intro fun k => sep_mono (forall_elim k) (forall_elim k)

@[rocq_alias monPred_objectively_sep]
theorem monPred_objectively_sep {bot : I.car} [BiIndexBottom I bot] (P Q : MonPred I PROP) :
    MonPred.objectively (iprop(P ∗ Q)) ⊣⊢ iprop(MonPred.objectively P ∗ MonPred.objectively Q) :=
  ⟨entails_at.mpr fun _ =>
      (forall_elim bot).trans (sep_mono
        (forall_intro fun k => P.monPred_mono (BiIndexBottom.bot_le k))
        (forall_intro fun k => Q.monPred_mono (BiIndexBottom.bot_le k))),
   monPred_objectively_sep_2 P Q⟩

@[rocq_alias monPred_objectively_affine]
instance monPred_objectively_affine (P : MonPred I PROP) [Affine P] :
    Affine (MonPred.objectively P) where
  affine := entails_at.mpr fun _ => (forall_elim (default : I.car)).trans Affine.affine

@[rocq_alias monPred_objectively_absorbing]
instance monPred_objectively_absorbing (P : MonPred I PROP) [Absorbing P] :
    Absorbing (MonPred.objectively P) where
  absorbing := entails_at.mpr fun _ => forall_intro fun k =>
    (absorbingly_mono (forall_elim k)).trans Absorbing.absorbing

@[rocq_alias monPred_objectively_persistent]
instance monPred_objectively_persistent [BIPersistentlyForall PROP] (P : MonPred I PROP)
    [Persistent P] : Persistent (MonPred.objectively P) where
  persistent := entails_at.mpr fun _ =>
    (forall_mono fun _ => Persistent.persistent).trans persistently_forall.mpr

@[rocq_alias monPred_objectively_timeless]
instance monPred_objectively_timeless (P : MonPred I PROP) [Timeless P] :
    Timeless (MonPred.objectively P) where
  timeless := entails_at.mpr fun _ => Timeless.timeless (P := iprop(∀ j, P.monPred_at j))

/-! ### The `subjectively` modality -/

@[rocq_alias monPred_subjectively_intro]
theorem monPred_subjectively_intro (P : MonPred I PROP) : P ⊢ MonPred.subjectively P :=
  entails_at.mpr fun i => exists_intro i

@[rocq_alias monPred_subjectively_mono]
theorem monPred_subjectively_mono {P Q : MonPred I PROP} (h : P ⊢ Q) :
    MonPred.subjectively P ⊢ MonPred.subjectively Q :=
  entails_at.mpr fun _ => exists_mono fun k => entails_at.mp h k

@[rocq_alias monPred_subjectively_ne]
theorem monPred_subjectively_ne :
    OFE.NonExpansive (MonPred.subjectively (I := I) (PROP := PROP)) :=
  ⟨fun _ _ _ h => dist_at.mpr fun _ => exists_ne fun k => dist_at.mp h k⟩

#rocq_ignore monPred_subjectively_mono' "Use monPred_subjectively_mono."
#rocq_ignore monPred_subjectively_flip_mono' "Use monPred_subjectively_mono."
#rocq_ignore monPred_subjectively_proper "Use monPred_subjectively_ne."

@[rocq_alias monPred_subjectively_idemp]
theorem monPred_subjectively_idemp (P : MonPred I PROP) :
    MonPred.subjectively (MonPred.subjectively P) ⊣⊢ MonPred.subjectively P :=
  ⟨objective_subjectively _, monPred_subjectively_intro _⟩

@[rocq_alias monPred_subjectively_and]
theorem monPred_subjectively_and (P Q : MonPred I PROP) :
    MonPred.subjectively (iprop(P ∧ Q)) ⊢ iprop(MonPred.subjectively P ∧ MonPred.subjectively Q) :=
  entails_at.mpr fun _ =>
    and_intro (exists_mono fun _ => and_elim_l) (exists_mono fun _ => and_elim_r)

@[rocq_alias monPred_subjectively_or]
theorem monPred_subjectively_or (P Q : MonPred I PROP) :
    MonPred.subjectively (iprop(P ∨ Q)) ⊣⊢ iprop(MonPred.subjectively P ∨ MonPred.subjectively Q) :=
  ⟨entails_at.mpr fun _ => or_exists.mp, entails_at.mpr fun _ => or_exists.mpr⟩

@[rocq_alias monPred_subjectively_forall]
theorem monPred_subjectively_forall {α : Sort _} (Φ : α → MonPred I PROP) :
    MonPred.subjectively (iprop(∀ x, Φ x)) ⊢ iprop(∀ x, MonPred.subjectively (Φ x)) :=
  entails_at.mpr fun i =>
    (forall_intro fun x => exists_elim fun k =>
      ((monPred_at_forall k Φ).mp.trans (forall_elim x)).trans (exists_intro k)).trans
    (monPred_at_forall i fun x => MonPred.subjectively (Φ x)).mpr

@[rocq_alias monPred_subjectively_exist]
theorem monPred_subjectively_exist {α : Sort _} (Φ : α → MonPred I PROP) :
    MonPred.subjectively (iprop(∃ x, Φ x)) ⊣⊢ iprop(∃ x, MonPred.subjectively (Φ x)) :=
  ⟨entails_at.mpr fun i =>
      exists_elim fun k => (monPred_at_exist k Φ).mp.trans <|
        exists_elim fun x => (exists_intro k).trans <|
          (exists_intro x).trans (monPred_at_exist i fun x => MonPred.subjectively (Φ x)).mpr,
   entails_at.mpr fun i =>
      (monPred_at_exist i fun x => MonPred.subjectively (Φ x)).mp.trans <|
      exists_elim fun x => exists_elim fun k =>
        ((exists_intro x).trans (monPred_at_exist k Φ).mpr).trans (exists_intro k)⟩

@[rocq_alias monPred_subjectively_sep]
theorem monPred_subjectively_sep (P Q : MonPred I PROP) :
    MonPred.subjectively (iprop(P ∗ Q)) ⊢ iprop(MonPred.subjectively P ∗ MonPred.subjectively Q) :=
  entails_at.mpr fun _ => exists_elim fun k => sep_mono (exists_intro k) (exists_intro k)

@[rocq_alias monPred_subjectively_affine]
instance monPred_subjectively_affine (P : MonPred I PROP) [Affine P] :
    Affine (MonPred.subjectively P) where
  affine := entails_at.mpr fun _ => exists_elim fun _ => Affine.affine

@[rocq_alias monPred_subjectively_absorbing]
instance monPred_subjectively_absorbing (P : MonPred I PROP) [Absorbing P] :
    Absorbing (MonPred.subjectively P) where
  absorbing := entails_at.mpr fun _ =>
    absorbingly_exists.mp.trans (exists_mono fun _ => Absorbing.absorbing)

@[rocq_alias monPred_subjectively_persistent]
instance monPred_subjectively_persistent (P : MonPred I PROP) [Persistent P] :
    Persistent (MonPred.subjectively P) where
  persistent := entails_at.mpr fun _ =>
    (exists_mono fun _ => Persistent.persistent).trans persistently_exists.mpr

@[rocq_alias monPred_subjectively_timeless]
instance monPred_subjectively_timeless (P : MonPred I PROP) [Timeless P] :
    Timeless (MonPred.subjectively P) where
  timeless := entails_at.mpr fun _ => Timeless.timeless (P := iprop(∃ j, P.monPred_at j))

/-! ### Big separating conjunctions -/

section BigOp
open Iris.Algebra Iris.Algebra.BigOpL Iris.Algebra.BigOpM
open Iris.BI.BigSepL Iris.BI.BigSepM Iris.BI.BigSepS

@[reducible] def monPred_at_hom {op₁ : MonPred I PROP → MonPred I PROP → MonPred I PROP}
    {op₂ : PROP → PROP → PROP} {u₁ : MonPred I PROP} {u₂ : PROP}
    [MonoidOps op₁ u₁] [MonoidOps op₂ u₂] (i : I.car)
    (hop : ∀ {x y}, (op₁ x y).monPred_at i ≡ op₂ (x.monPred_at i) (y.monPred_at i))
    (hunit : u₁.monPred_at i ≡ u₂) :
    MonoidHomomorphism op₁ op₂ u₁ u₂ (· ≡ ·) (fun P : MonPred I PROP => P.monPred_at i) where
  rel_refl := .rfl
  rel_trans := .trans
  op_proper ha hb := MonoidOps.op_proper ha hb
  map_ne := monPred_at_ne i
  map_op := hop
  map_unit := hunit

@[rocq_alias monPred_at_monoid_and_homomorphism]
instance monPred_at_monoid_and_homomorphism (i : I.car) :
    MonoidHomomorphism (BIBase.and (PROP := MonPred I PROP)) (BIBase.and (PROP := PROP))
      iprop(True) iprop(True) (· ≡ ·) (fun P => P.monPred_at i) :=
  monPred_at_hom i .rfl .rfl

@[rocq_alias monPred_at_monoid_or_homomorphism]
instance monPred_at_monoid_or_homomorphism (i : I.car) :
    MonoidHomomorphism (BIBase.or (PROP := MonPred I PROP)) (BIBase.or (PROP := PROP))
      iprop(False) iprop(False) (· ≡ ·) (fun P => P.monPred_at i) :=
  monPred_at_hom i .rfl .rfl

@[rocq_alias monPred_at_monoid_sep_homomorphism]
instance monPred_at_monoid_sep_homomorphism (i : I.car) :
    MonoidHomomorphism (BIBase.sep (PROP := MonPred I PROP)) (BIBase.sep (PROP := PROP))
      BIBase.emp BIBase.emp (· ≡ ·) (fun P => P.monPred_at i) :=
  monPred_at_hom i .rfl .rfl

@[rocq_alias monPred_at_big_sepL]
theorem monPred_at_big_sepL {α : Type _} (i : I.car) (Φ : Nat → α → MonPred I PROP) (l : List α) :
    ([∗list] k ↦ x ∈ l, Φ k x).monPred_at i ⊣⊢ [∗list] k ↦ x ∈ l, (Φ k x).monPred_at i :=
  equiv_iff.mp (bigOpL_hom (H := monPred_at_monoid_sep_homomorphism i) Φ l)

@[rocq_alias monPred_at_big_sepM]
theorem monPred_at_big_sepM {K V : Type _} {M : Type _ → Type _} [LawfulFiniteMap M K]
    (i : I.car) (Φ : K → V → MonPred I PROP) (m : M V) :
    ([∗map] k ↦ x ∈ m, Φ k x).monPred_at i ⊣⊢ [∗map] k ↦ x ∈ m, (Φ k x).monPred_at i :=
  equiv_iff.mp (bigOpM_hom (ι := monPred_at_monoid_sep_homomorphism i) Φ m)

@[rocq_alias monPred_at_big_sepS]
theorem monPred_at_big_sepS {S α : Type _} [LawfulFiniteSet S α]
    (i : I.car) (Φ : α → MonPred I PROP) (X : S) :
    ([∗set] x ∈ X, Φ x).monPred_at i ⊣⊢ [∗set] x ∈ X, (Φ x).monPred_at i :=
  equiv_iff.mp (Iris.Algebra.BigOpS.hom (monPred_at_monoid_sep_homomorphism i) Φ X)

@[rocq_alias big_sepL_objective]
instance big_sepL_objective {α : Type _} (Φ : Nat → α → MonPred I PROP) (l : List α)
    [∀ k x, Objective (Φ k x)] : Objective (iprop([∗list] k ↦ x ∈ l, Φ k x)) where
  objective_at i j := (monPred_at_big_sepL i Φ l).mp.trans <|
    (bigSepL_mono fun _ => Objective.objective_at i j).trans (monPred_at_big_sepL j Φ l).mpr

@[rocq_alias big_sepM_objective]
instance big_sepM_objective {K V : Type _} {M : Type _ → Type _} [LawfulFiniteMap M K]
    (Φ : K → V → MonPred I PROP) (m : M V) [∀ k x, Objective (Φ k x)] :
    Objective (iprop([∗map] k ↦ x ∈ m, Φ k x)) where
  objective_at i j := (monPred_at_big_sepM i Φ m).mp.trans <|
    (bigSepM_mono fun _ => Objective.objective_at i j).trans (monPred_at_big_sepM j Φ m).mpr

@[rocq_alias big_sepS_objective]
instance big_sepS_objective {S α : Type _} [LawfulFiniteSet S α] (Φ : α → MonPred I PROP) (X : S)
    [∀ x, Objective (Φ x)] : Objective (iprop([∗set] x ∈ X, Φ x)) where
  objective_at i j := (monPred_at_big_sepS i Φ X).mp.trans <|
    (bigSepS_mono fun _ => Objective.objective_at i j).trans (monPred_at_big_sepS j Φ X).mpr

/-! #### `objectively` over big separating conjunctions -/

@[rocq_alias monPred_objectively_monoid_and_homomorphism]
instance monPred_objectively_monoid_and_homomorphism :
    MonoidHomomorphism (BIBase.and (PROP := MonPred I PROP)) BIBase.and iprop(True) iprop(True)
      (· ≡ ·) MonPred.objectively :=
  MonoidHomomorphism.ofEquiv monPred_objectively_ne
    (fun {x y} => equiv_iff.mpr (monPred_objectively_and x y))
    (equiv_iff.mpr (monPred_objectively_pure True))

@[rocq_alias monPred_objectively_monoid_sep_entails_homomorphism]
instance monPred_objectively_monoid_sep_entails_homomorphism :
    MonoidHomomorphism (BIBase.sep (PROP := MonPred I PROP)) BIBase.sep BIBase.emp BIBase.emp
      (flip Entails) MonPred.objectively where
  rel_refl {a} := show a ⊢ a from BIBase.Entails.rfl
  rel_trans {a b c} h1 h2 := BIBase.Entails.trans (show c ⊢ b from h2) (show b ⊢ a from h1)
  op_proper {a a' b b'} h1 h2 := sep_mono (show a' ⊢ a from h1) (show b' ⊢ b from h2)
  map_ne := monPred_objectively_ne
  map_op := fun {x y} => monPred_objectively_sep_2 x y
  map_unit := monPred_objectively_emp.mpr

@[reducible, rocq_alias monPred_objectively_monoid_sep_homomorphism]
def monPred_objectively_monoid_sep_homomorphism {bot : I.car} [BiIndexBottom I bot] :
    MonoidHomomorphism (BIBase.sep (PROP := MonPred I PROP)) BIBase.sep BIBase.emp BIBase.emp
      (· ≡ ·) MonPred.objectively :=
  MonoidHomomorphism.ofEquiv monPred_objectively_ne
    (fun {x y} => equiv_iff.mpr (monPred_objectively_sep (bot := bot) x y))
    (equiv_iff.mpr monPred_objectively_emp)

@[rocq_alias monPred_objectively_big_sepL_entails]
theorem monPred_objectively_big_sepL_entails {α : Type _} (Φ : Nat → α → MonPred I PROP)
    (l : List α) :
    ([∗list] k ↦ x ∈ l, MonPred.objectively (Φ k x)) ⊢
      MonPred.objectively (iprop([∗list] k ↦ x ∈ l, Φ k x)) :=
  bigOpL_hom (H := monPred_objectively_monoid_sep_entails_homomorphism) Φ l

@[rocq_alias monPred_objectively_big_sepL]
theorem monPred_objectively_big_sepL {bot : I.car} [BiIndexBottom I bot] {α : Type _}
    (Φ : Nat → α → MonPred I PROP) (l : List α) :
    MonPred.objectively (iprop([∗list] k ↦ x ∈ l, Φ k x)) ⊣⊢
      [∗list] k ↦ x ∈ l, MonPred.objectively (Φ k x) :=
  equiv_iff.mp (bigOpL_hom (H := monPred_objectively_monoid_sep_homomorphism (bot := bot)) Φ l)

@[rocq_alias monPred_objectively_big_sepM_entails]
theorem monPred_objectively_big_sepM_entails {K V : Type _} {M : Type _ → Type _}
    [LawfulFiniteMap M K] (Φ : K → V → MonPred I PROP) (m : M V) :
    ([∗map] k ↦ x ∈ m, MonPred.objectively (Φ k x)) ⊢
      MonPred.objectively (iprop([∗map] k ↦ x ∈ m, Φ k x)) :=
  bigOpM_hom (ι := monPred_objectively_monoid_sep_entails_homomorphism) Φ m

@[rocq_alias monPred_objectively_big_sepM]
theorem monPred_objectively_big_sepM {bot : I.car} [BiIndexBottom I bot] {K V : Type _}
    {M : Type _ → Type _} [LawfulFiniteMap M K] (Φ : K → V → MonPred I PROP) (m : M V) :
    MonPred.objectively (iprop([∗map] k ↦ x ∈ m, Φ k x)) ⊣⊢
      [∗map] k ↦ x ∈ m, MonPred.objectively (Φ k x) :=
  equiv_iff.mp (bigOpM_hom (ι := monPred_objectively_monoid_sep_homomorphism (bot := bot)) Φ m)

@[rocq_alias monPred_objectively_big_sepS_entails]
theorem monPred_objectively_big_sepS_entails {S α : Type _} [LawfulFiniteSet S α]
    (Φ : α → MonPred I PROP) (X : S) :
    ([∗set] x ∈ X, MonPred.objectively (Φ x)) ⊢
      MonPred.objectively (iprop([∗set] x ∈ X, Φ x)) :=
  Iris.Algebra.BigOpS.hom monPred_objectively_monoid_sep_entails_homomorphism Φ X

@[rocq_alias monPred_objectively_big_sepS]
theorem monPred_objectively_big_sepS {bot : I.car} [BiIndexBottom I bot] {S α : Type _}
    [LawfulFiniteSet S α] (Φ : α → MonPred I PROP) (X : S) :
    MonPred.objectively (iprop([∗set] x ∈ X, Φ x)) ⊣⊢
      [∗set] x ∈ X, MonPred.objectively (Φ x) :=
  equiv_iff.mp
    (Iris.Algebra.BigOpS.hom (monPred_objectively_monoid_sep_homomorphism (bot := bot)) Φ X)

end BigOp

/-! ### Step-indexed (SBI) structure on `MonPred` -/

section Sbi
variable {I : BiIndex} {PROP : Type _} [Sbi PROP]

@[rocq_alias monPred_defs.monPred_si_pure]
instance : SiPure (MonPred I PROP) where
  siPure Pi := MonPred.embed (SiPure.siPure Pi)

#rocq_ignore monPred_defs.monPred_si_pure_def "Rocq unsealed definition body; use SiPure.siPure."
#rocq_ignore monPred_defs.monPred_si_pure_aux "Rocq sealing auxiliary definition."
#rocq_ignore monPred_defs.monPred_si_pure_unseal "Rocq unsealing lemma."
#rocq_ignore monPred_si_pure_unseal "Rocq unsealing lemma."

@[rocq_alias monPred_defs.monPred_si_emp_valid]
instance : SiEmpValid (MonPred I PROP) where
  siEmpValid P := SiEmpValid.siEmpValid (iprop(∀ i, P.monPred_at i) : PROP)

#rocq_ignore monPred_defs.monPred_si_emp_valid_def
  "Rocq unsealed definition body; use SiEmpValid.siEmpValid."
#rocq_ignore monPred_defs.monPred_si_emp_valid_aux "Rocq sealing auxiliary definition."
#rocq_ignore monPred_defs.monPred_si_emp_valid_unseal "Rocq unsealing lemma."
#rocq_ignore monPred_si_emp_valid_unseal "Rocq unsealing lemma."

@[rocq_alias monPred_si_pure_unfold]
theorem monPred_si_pure_unfold :
    (SiPure.siPure : SiProp → MonPred I PROP) =
      fun Pi => (iprop(⎡(<si_pure> Pi : PROP)⎤) : MonPred I PROP) := rfl

@[rocq_alias monPred_si_emp_valid_unfold]
theorem monPred_si_emp_valid_unfold :
    (SiEmpValid.siEmpValid : MonPred I PROP → SiProp) =
      fun P => SiEmpValid.siEmpValid (iprop(∀ i, P.monPred_at i) : PROP) := rfl

@[rocq_alias monPred_sbi]
instance instSbiMonPred : Sbi (MonPred I PROP) where
  siPure_ne := ⟨fun _ _ _ h => dist_at.mpr fun _ => Sbi.siPure_ne.ne h⟩
  siEmpValid_ne := ⟨fun _ _ _ h => Sbi.siEmpValid_ne.ne (forall_ne fun i => dist_at.mp h i)⟩
  siPure_mono h := entails_at.mpr fun _ => siPure_mono h
  siEmpValid_mono h := siEmpValid_mono (forall_mono fun i => entails_at.mp h i)
  siEmpValid_siPure {Pi} := by
    refine ⟨?_, ?_⟩
    · refine (siEmpValid_mono (P := iprop(∀ _ : I.car, <si_pure> Pi)) (Q := iprop(<si_pure> Pi))
        (forall_elim (default : I.car))).trans siEmpValid_siPure.mp
    · refine siEmpValid_siPure.mpr.trans (siEmpValid_mono
        (P := iprop(<si_pure> Pi)) (Q := iprop(∀ _ : I.car, <si_pure> Pi))
        (forall_intro fun _ => .rfl))
  siPure_siEmpValid {P} := entails_at.mpr fun i =>
    siPure_siEmpValid.trans (persistently_mono (forall_elim i))
  siPure_imp_mpr {Pi Qi} := entails_at.mpr fun i =>
    (monPred_impl_force i (SiPure.siPure Pi : MonPred I PROP) (SiPure.siPure Qi)).trans
      siPure_imp_mpr
  siPure_sForall_mpr {Ψi} := entails_at.mpr fun i => by
    refine .trans ?_ (siPure_sForall_mpr (PROP := PROP))
    refine (monPred_at_forall i (fun q : SiProp => iprop(⌜Ψi q⌝ → <si_pure> q))).mp.trans ?_
    exact forall_mono fun q =>
      monPred_impl_force i (iprop(⌜Ψi q⌝)) (SiPure.siPure q : MonPred I PROP)
  persistently_imp_siPure {P Q} := entails_at.mpr fun i => by
    refine (forall_elim i).trans ?_
    refine (pure_imp_elim (Std.Refl.refl i : I.rel.le i i)).trans ?_
    refine persistently_imp_siPure.trans (persistently_mono ?_)
    refine forall_intro fun j => imp_intro <| pure_elim_right fun (hij : I.rel.le i j) => ?_
    exact imp_mono_right (Q.monPred_mono hij)
  siPure_later {Pi} :=
    ⟨entails_at.mpr fun _ => siPure_later.mp, entails_at.mpr fun _ => siPure_later.mpr⟩
  siPure_absorbing Pi := ⟨entails_at.mpr fun i => (monPred_at_absorbingly i _).mp.trans
    ((Sbi.siPure_absorbing Pi).absorbing)⟩
  siEmpValid_later_mp {P} :=
    (siEmpValid_mono later_forall.mpr).trans (siEmpValid_later_mp.trans (later_mono .rfl))
  siEmpValid_affinely_mpr {P} :=
    siEmpValid_forall.mp.trans <|
      (forall_mono fun i =>
        siEmpValid_affinely_mpr.trans (siEmpValid_mono (monPred_at_affinely i P).mpr)).trans
      siEmpValid_forall.mpr
  prop_ext_siEmpValid {P Q} := by
    have hforce : ∀ i, (iprop(P ∗-∗ Q) : MonPred I PROP).monPred_at i ⊢
        iprop(P.monPred_at i ∗-∗ Q.monPred_at i) := fun i =>
      and_mono (monPred_wand_force i P Q) (monPred_wand_force i Q P)
    have hstep : SiEmpValid.siEmpValid (iprop(∀ i, (iprop(P ∗-∗ Q) : MonPred I PROP).monPred_at i))
        ⊢@{SiProp} ∀ i, internalEq (PROP := SiProp) (P.monPred_at i) (Q.monPred_at i) :=
      siEmpValid_forall.mp.trans <| forall_mono fun i =>
        (siEmpValid_mono (hforce i)).trans (BI.prop_ext_siEmpValid_mpr _ _)
    refine hstep.trans ?_
    refine (BI.discreteFun_equivI (PROP := SiProp) P.monPred_at Q.monPred_at).mpr.trans ?_
    refine (BI.sig_equivI (PROP := SiProp) _ (MonPred.toSig P) (MonPred.toSig Q)).mp.trans ?_
    exact BI.internalEq.of_internalEquiv_ne (PROP := SiProp) MonPred.ofSig

#rocq_ignore monPred_sbi_mixin "Rocq mixin record; subsumed by the Sbi instance."
#rocq_ignore monPred_sbi_prop_ext_mixin "Rocq mixin record; subsumed by the Sbi instance."

/-! ### Internal equality and the plainly modality on `MonPred` -/

@[rocq_alias monPred_internal_eq_unfold]
theorem monPred_internal_eq_unfold {A : Type _} [OFE A] :
    (internalEq : A → A → MonPred I PROP) =
      fun x y => (iprop(⎡(internalEq x y : PROP)⎤) : MonPred I PROP) := rfl

@[rocq_alias monPred_at_internal_eq]
theorem monPred_at_internal_eq {A : Type _} [OFE A] (i : I.car) (a b : A) :
    (internalEq a b : MonPred I PROP).monPred_at i ⊣⊢ internalEq a b :=
  BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_plainly]
theorem monPred_at_plainly (i : I.car) (P : MonPred I PROP) :
    (iprop(■ P) : MonPred I PROP).monPred_at i ⊣⊢ iprop(∀ j, ■ (P.monPred_at j)) := by
  show (SiPure.siPure (SiEmpValid.siEmpValid P) : MonPred I PROP).monPred_at i ⊣⊢
    iprop(∀ j, ■ (P.monPred_at j))
  refine .trans (BIBase.BiEntails.of_eq rfl) ?_
  show iprop(<si_pure> (SiEmpValid.siEmpValid (iprop(∀ j, P.monPred_at j) : PROP)) : PROP) ⊣⊢
    iprop(∀ j, ■ (P.monPred_at j))
  calc iprop(<si_pure> (SiEmpValid.siEmpValid (iprop(∀ j, P.monPred_at j) : PROP)) : PROP)
    _ ⊣⊢ <si_pure> (∀ j, <si_emp_valid> P.monPred_at j) := siPure_mono_bi siEmpValid_forall
    _ ⊣⊢ ∀ j, <si_pure> <si_emp_valid> P.monPred_at j := siPure_forall
    _ ⊣⊢ ∀ j, ■ (P.monPred_at j) := .rfl

@[rocq_alias monPred_equivI]
theorem monPred_equivI {PROP' : Type _} [Sbi PROP'] (P Q : MonPred I PROP) :
    (internalEq P Q : PROP') ⊣⊢ iprop(∀ i, internalEq (P.monPred_at i) (Q.monPred_at i)) := by
  refine ⟨?_, ?_⟩
  · refine forall_intro fun i => ?_
    letI _ := MonPred.monPred_at_ne (PROP := PROP) i
    exact BI.internalEq.of_internalEquiv_ne (PROP := PROP')
      (fun R : MonPred I PROP => R.monPred_at i)
  · refine (BI.discreteFun_equivI (PROP := PROP') P.monPred_at Q.monPred_at).mpr.trans ?_
    refine (BI.sig_equivI (PROP := PROP') _ (MonPred.toSig P) (MonPred.toSig Q)).mp.trans ?_
    exact BI.internalEq.of_internalEquiv_ne (PROP := PROP') MonPred.ofSig

/-! ### Objective and plain instances -/

@[rocq_alias si_pure_objective]
instance si_pure_objective (Pi : SiProp) : Objective (iprop(<si_pure> Pi) : MonPred I PROP) where
  objective_at _ _ := .rfl

@[rocq_alias internal_eq_objective]
instance internal_eq_objective {A : Type _} [OFE A] (x y : A) :
    Objective (internalEq x y : MonPred I PROP) where
  objective_at _ _ := .rfl

@[rocq_alias plainly_objective]
instance plainly_objective (P : MonPred I PROP) : Objective (iprop(■ P)) where
  objective_at _ _ := .rfl

@[rocq_alias plainly_if_objective]
instance plainly_if_objective (p : Bool) (P : MonPred I PROP) [Objective P] :
    Objective (iprop(■?p P)) := by
  cases p
  · exact ‹Objective P›
  · exact plainly_objective P

@[rocq_alias monPred_at_plain]
instance monPred_at_plain (P : MonPred I PROP) [Plain P] (i : I.car) :
    Plain (P.monPred_at i) where
  plain := (entails_at.mp Plain.plain i).trans ((monPred_at_plainly i P).mp.trans (forall_elim i))

@[rocq_alias monPred_objectively_plain]
instance monPred_objectively_plain (P : MonPred I PROP) [Plain P] :
    Plain (MonPred.objectively P) where
  plain := entails_at.mpr fun i => by
    refine (Plain.plain (P := iprop(∀ j, P.monPred_at j))).trans ?_
    refine (forall_intro fun _ => .rfl).trans (monPred_at_plainly i (MonPred.objectively P)).mpr

@[rocq_alias monPred_subjectively_plain]
instance monPred_subjectively_plain (P : MonPred I PROP) [Plain P] :
    Plain (MonPred.subjectively P) where
  plain := entails_at.mpr fun i => by
    refine (Plain.plain (P := iprop(∃ j, P.monPred_at j))).trans ?_
    refine (forall_intro fun _ => .rfl).trans (monPred_at_plainly i (MonPred.subjectively P)).mpr

/-! ### `SbiEmpValidExist` for `MonPred` -/

@[reducible, rocq_alias monPred_sbi_emp_valid_exist]
def monPred_sbi_emp_valid_exist {bot : I.car} [BiIndexBottom I bot] [SbiEmpValidExist PROP] :
    SbiEmpValidExist (MonPred I PROP) where
  siEmpValid_sExists_1 Ψ := by
    refine (siEmpValid_mono (forall_elim bot)).trans ?_
    refine (siEmpValid_sExists_1
      (fun p => ∃ q : MonPred I PROP, Ψ q ∧ q.monPred_at bot = p)).trans ?_
    refine exists_elim fun p => pure_elim_left fun ⟨q, hΨ, hq⟩ => ?_
    subst hq
    refine exists_intro_trans q (and_intro (pure_intro hΨ) ?_)
    exact (siEmpValid_mono (forall_intro fun k => q.monPred_mono (BiIndexBottom.bot_le k)))

/-! ### SBI instances -/

@[rocq_alias monPred_bi_embed_sbi]
instance monPred_bi_embed_sbi : BiEmbedSbi PROP (MonPred I PROP) where
  embed_si_emp_valid _P :=
    ⟨siEmpValid_mono (forall_elim (default : I.car)),
     siEmpValid_mono (forall_intro fun _ => .rfl)⟩
  embed_si_pure_1 _ := .rfl

@[rocq_alias monPred_bi_bupd_sbi]
instance monPred_bi_bupd_sbi [BIUpdate PROP] [BIBUpdateSbi PROP] :
    BIBUpdateSbi (MonPred I PROP) where
  bupd_si_pure Pi := entails_at.mpr fun _ => BIBUpdateSbi.bupd_si_pure Pi

@[rocq_alias monPred_bi_fupd_sbi]
instance monPred_bi_fupd_sbi [BIFUpdate PROP] [BIFUpdatePlainly PROP] :
    BIFUpdatePlainly (MonPred I PROP) where
  fupd_keep_si_pure E' Pi R := entails_at.mpr fun i => by
    refine (and_mono_right
      (monPred_wand_force i (SiPure.siPure Pi : MonPred I PROP) (iprop(|={_}=> R)))).trans ?_
    exact BIFUpdatePlainly.fupd_keep_si_pure E' Pi (R.monPred_at i)
  fupd_plainly_later E P := entails_at.mpr fun i => by
    refine (later_mono
      (BIFUpdate.mono ((monPred_at_plainly i P).mp.trans (forall_elim i)))).trans ?_
    exact BIFUpdatePlainly.fupd_plainly_later E (P.monPred_at i)
  fupd_plainly_sForall_2 E Φ := entails_at.mpr fun i => by
    refine (BIFUpdate.mono
      ((monPred_at_plainly i (BIBase.sForall Φ)).mp.trans (forall_elim i))).trans ?_
    exact BIFUpdatePlainly.fupd_plainly_sForall_2 E
      (fun p => ∃ q : MonPred I PROP, Φ q ∧ q.monPred_at i = p)

end Sbi

end MonPred

end Iris.BI
