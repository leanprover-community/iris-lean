/-
Copyright (c) The Iris-Lean Contributors
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
public import Iris.BI.LaterCredits
public import Iris.BI.Plainly
public import Iris.BI.Sbi
public import Iris.BI.BigOp.BigOp
public import Iris.BI.BigOp.BigSepList
public import Iris.BI.BigOp.BigSepMap
public import Iris.BI.BigOp.BigSepMSet
public import Iris.BI.BigOp.BigSepSet

@[expose] public section


variable {SI : Type _} [Iris.SIdx SI]

namespace Iris.BI
open Iris Iris.Std OFE

/-- A `BiIndex` is an inhabited type equipped with a preorder `⊑`. Monotone
predicates are functions out of a `BiIndex` that are monotone w.r.t. this order. -/
@[rocq_alias biIndex]
structure BiIndex where
  car : Type _
  [inhabited : Inhabited car]
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
def upclosed [BI.BIBase PROP] (Φ : I.car → PROP) : I.car → PROP :=
  fun i => iprop(∀ j, ⌜I.rel.le i j⌝ → Φ j)

end MonPred

section OFE
variable {I : BiIndex} {PROP : Type _} [BI PROP] [BIStepIndexed SI PROP]

/-- Pointwise OFE: `P ≡ Q := ∀ i, P i ≡ Q i`, `P ≡{n}≡ Q := ∀ i, P i ≡{n}≡ Q i`
(Rocq `monPredO`). -/
@[rocq_alias monPredO]
instance : OFE SI (MonPred I PROP) where
  dist n P Q := ∀ i, P.monPred_at i ≡{n}≡ Q.monPred_at i
  dist_eqv :=
    { refl _ _ := dist_eqv.refl _
      symm h i := dist_eqv.symm (h i)
      trans h1 h2 i := dist_eqv.trans (h1 i) (h2 i) }
  eq_dist' {P Q} := by
    refine ⟨fun h _ _ => h ▸ .rfl, fun h => ?_⟩
    exact MonPred.ext fun i => eq_dist_2 fun n => h n i
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
    MonPred I PROP -n>[SI] { f : I.car → PROP // ∀ {i j : I.car}, I.rel.le i j → (f i ⊢ f j) } where
  f P := ⟨P.monPred_at, fun h => P.monPred_mono h⟩
  ne.1 _ _ _ h := h

/-- The inverse of `MonPred.toSig`: rebuild a monotone predicate from a monotone family.
Rocq `sig_monPred`. -/
@[rocq_alias sig_monPred]
def ofSig :
    { f : I.car → PROP // ∀ {i j : I.car}, I.rel.le i j → (f i ⊢ f j) } -n>[SI] MonPred I PROP where
  f P := ⟨P.val, P.property⟩
  ne.1 _ _ _ h := h

@[rocq_alias sig_monPred_ne]
theorem ofSig_ne : OFE.NonExpansive SI (ofSig (SI := SI) (I := I) (PROP := PROP)) := ofSig.ne

#rocq_ignore sig_monPred_proper "OFE is Leibniz; use equality"

@[rocq_alias monPred_sig_ne]
theorem toSig_ne : OFE.NonExpansive SI (toSig (SI := SI) (I := I) (PROP := PROP)) := toSig.ne

#rocq_ignore monPred_sig_proper "OFE is Leibniz; use equality"

@[rocq_alias sig_monPred_sig]
theorem ofSig_toSig (P : MonPred I PROP) : ofSig (SI := SI) (toSig (SI := SI) P) = P := rfl

@[rocq_alias monPred_sig_monPred]
theorem toSig_ofSig (P : { f : I.car → PROP // ∀ {i j : I.car}, I.rel.le i j → (f i ⊢ f j) }) :
    toSig (SI := SI) (ofSig (SI := SI) P) = P := rfl

end MonPred

@[rocq_alias monPred_cofe]
instance [SIdxFinite SI] : IsCOFE SI (MonPred I PROP) where
  compl c :=
    let cf := c.map ((⟨Subtype.val, inferInstance⟩ : _ -n>[SI] (I.car → PROP)).comp MonPred.toSig)
    { monPred_at := fun i => COFE.compl cf i
      monPred_mono := fun {i j} h =>
        (LimitPreserving.entails (applyHom (SI := SI) i) (applyHom (SI := SI) j)).compl cf (fun n => (c n).monPred_mono h) }
  conv_compl {n : SI} {c} :=
    IsCOFE.conv_compl (n := n)
      (c := c.map ((⟨Subtype.val, inferInstance⟩ : _ -n>[SI] (I.car → PROP)).comp MonPred.toSig))
  lbcompl hn _ := absurd hn (SIdx.limit_finite _)
  conv_lbcompl hn _ := absurd hn (SIdx.limit_finite _)
  lbcompl_ne hn _ := absurd hn (SIdx.limit_finite _)

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
  "Rocq unsealed definition body; use <obj>."
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

@[inherit_doc objectively]  syntax:max "<obj> "  term:40 : term
@[inherit_doc subjectively] syntax:max "<subj> " term:40 : term

macro_rules
  | `(iprop(<obj>%$tk $P))  => ``($(wrapIprop tk ``objectively) iprop($P))
  | `(iprop(<subj>%$tk $P)) => ``($(wrapIprop tk ``subjectively) iprop($P))

delab_rule MonPred.objectively
  | `($_ $P) => do ``(iprop(<obj> $(← unpackIprop P)))
delab_rule MonPred.subjectively
  | `($_ $P) => do ``(iprop(<subj> $(← unpackIprop P)))

end MonPred

section Instances
variable {I : BiIndex} {PROP : Type _} [BI PROP]

section BIInstance

/-- `BIBase` data; only reachable globally through `BI.toBIBase`. -/
@[reducible] def instBIBaseMonPred : BIBase (MonPred I PROP) where
  Entails       := MonPred.Entails
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

attribute [local instance] instBIBaseMonPred

@[rocq_alias monPred_at_entails]
theorem entails_at {P Q : MonPred I PROP} :
    (P ⊢ Q) ↔ ∀ i, P.monPred_at i ⊢ Q.monPred_at i := Iff.rfl

#rocq_ignore monPred_at_equiv "OFE is Leibniz; use equality"

@[rocq_alias monPred_at_dist]
theorem dist_at [BIStepIndexed SI PROP] {n : SI} {P Q : MonPred I PROP} :
    (P ≡{n}≡ Q) ↔ ∀ i, P.monPred_at i ≡{n}≡ Q.monPred_at i := Iff.rfl

#rocq_ignore monPred_dist "Covered by dist_at."
#rocq_ignore monPred_dist' "Covered by dist_at."
#rocq_ignore monPred_equiv "Covered by equiv_at."
#rocq_ignore monPred_equiv' "Covered by equiv_at."

/-- Eliminating the up-closure at the current index. -/
theorem upclosed_at_elim {Φ : I.car → PROP} (i : I.car) : MonPred.upclosed Φ i ⊢ Φ i :=
  (forall_elim i).trans (pure_imp_elim (Std.Refl.refl i : I.rel.le i i))

/-- `▷ False → P i` up-closes, by monotonicity of `P`. -/
theorem upclosed_false_imp_intro (P : MonPred I PROP) (i : I.car) :
    iprop(▷ False → P.monPred_at i) ⊢
      MonPred.upclosed (fun j => iprop(▷ False → P.monPred_at j)) i :=
  forall_intro fun _ => imp_intro <| pure_elim_right fun hij => imp_mono_right (P.monPred_mono hij)

/-- BI instance on monotone predicates (Rocq `monPred_bi_mixin` + persistently/later
mixins, packaged into `monPredI : bi`). -/
@[rocq_alias monPredI]
instance : BI (MonPred I PROP) where
  toBIBase := instBIBaseMonPred
  entails_refl := entails_at.mpr fun _ => BIBase.Entails.rfl
  entails_trans := fun h h' => entails_at.mpr fun i => (entails_at.mp h i).trans (entails_at.mp h' i)
  equiv_iff := fun {P Q} =>
    ⟨fun h => ⟨entails_at.mpr fun i => BIBase.Entails.of_eq (congrArg (·.monPred_at i) h),
              entails_at.mpr fun i => BIBase.Entails.of_eq (congrArg (·.monPred_at i) h.symm)⟩,
     fun h => MonPred.ext fun i => equiv_iff.mpr ⟨entails_at.mp h.1 i, entails_at.mp h.2 i⟩⟩
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
  later_false_sExists := fun {Φ} => entails_at.mpr fun i => by
    refine (upclosed_at_elim i).trans (later_false_sExists.trans ?_)
    refine exists_elim fun p => pure_elim_left fun ⟨q, hΦ, hq⟩ => ?_
    subst hq
    exact (and_intro (pure_intro hΦ) (upclosed_false_imp_intro q i)).trans
      (MonPred.sExists_at_intro (q := iprop(⌜Φ q⌝ ∧ (▷ False → q))) i ⟨q, rfl⟩)
  later_false_sep := fun {P Q} => entails_at.mpr fun i =>
    (upclosed_at_elim i).trans <| later_false_sep.trans <|
      sep_mono (upclosed_false_imp_intro P i) (upclosed_false_imp_intro Q i)
  later_sep_2 := entails_at.mpr fun _ => later_sep_2
  later_persistently :=
    ⟨entails_at.mpr fun i => later_persistently.mp,
     entails_at.mpr fun i => later_persistently.mpr⟩
  later_false_em {P} := entails_at.mpr fun i => by
    refine later_false_em.trans (or_mono_right ?_)
    refine forall_intro fun j => imp_intro ?_
    refine pure_elim_right fun (hij : I.rel.le i j) => ?_
    exact imp_mono_right (P.monPred_mono hij)

/-- Step-indexed structure on monotone predicates: pointwise OFE (complete for finite step
indices), non-expansive connectives, and the finite-index later laws. -/
instance [BIStepIndexed SI PROP] [SIdxFinite SI] : BIStepIndexed SI (MonPred I PROP) where
  and_ne := ⟨fun _ _ _ h _ _ h' =>
    dist_at.mpr fun i => and_ne.ne (dist_at.mp h i) (dist_at.mp h' i)⟩
  or_ne := ⟨fun _ _ _ h _ _ h' => dist_at.mpr fun i => or_ne.ne (dist_at.mp h i) (dist_at.mp h' i)⟩
  imp_ne := ⟨fun _ _ _ h _ _ h' => dist_at.mpr fun i =>
    forall_ne fun j => imp_ne.ne Dist.rfl (imp_ne.ne (dist_at.mp h j) (dist_at.mp h' j))⟩
  sForall_ne := fun {n : SI} {Ψ₁ Ψ₂} h => dist_at.mpr fun i =>
    Iris.BI.sForall_ne
      ⟨fun _ ⟨q, hq, hp⟩ =>
          let ⟨q', hq', hr⟩ := h.1 q hq; ⟨_, ⟨q', hq', rfl⟩, hp ▸ dist_at.mp hr i⟩,
       fun _ ⟨q, hq, hp⟩ =>
          let ⟨q', hq', hr⟩ := h.2 q hq; ⟨_, ⟨q', hq', rfl⟩, hp ▸ dist_at.mp hr i⟩⟩
  sExists_ne := fun {n : SI} {Ψ₁ Ψ₂} h => dist_at.mpr fun i =>
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

instance [BILaterFinite PROP] : BILaterFinite (MonPred I PROP) where
  later_sExists_false := @fun Φ => entails_at.mpr fun i => by
    refine later_sExists_false.trans (or_mono_right ?_)
    refine exists_elim fun p => pure_elim_left fun ⟨q, hΦ, hq⟩ => ?_
    subst hq
    exact (and_intro (pure_intro hΦ) BIBase.Entails.rfl).trans
      (MonPred.sExists_at_intro (q := iprop(⌜Φ q⌝ ∧ ▷ q)) i ⟨q, rfl⟩)
  later_sep_1 := entails_at.mpr fun _ => later_sep_1

end BIInstance
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
  mono h := entails_at.mpr fun _ => h
  emp_valid_inj _ h := entails_at.mp h (Inhabited.default : I.car)
  emp_2 := entails_at.mpr fun _ => .rfl
  impl_2 _ _ := entails_at.mpr fun i =>
    (forall_elim i).trans (pure_imp_elim (Std.Refl.refl i : I.rel.le i i))
  forall_2 := fun _Ψ {_} h => entails_at.mpr fun i =>
    sForall_intro fun P hΨ => entails_at.mp (h P hΨ) i
  exist_1 := fun _Ψ {_} h => entails_at.mpr fun i =>
    sExists_elim fun P hΨ => entails_at.mp (h P hΨ) i
  sep _ _ := .rfl
  wand_2 _ _ := entails_at.mpr fun i =>
    (forall_elim i).trans (pure_imp_elim (Std.Refl.refl i : I.rel.le i i))
  persistently _ := .rfl

#rocq_ignore monPred_embedding_mixin "Rocq mixin record; subsumed by the BiEmbed instance."

instance [BIStepIndexed SI PROP] [SIdxFinite SI] : EmbedNE SI PROP (MonPred I PROP) where
  embed_ne := ⟨fun _ _ _ h => dist_at.mpr fun _ => h⟩

@[rocq_alias monPred_bi_embed_emp]
instance : BiEmbedEmp PROP (MonPred I PROP) where
  embed_emp_1 := (MonPred.ext fun _ => rfl).to_bi.mp

@[rocq_alias monPred_bi_embed_later]
instance : BiEmbedLater PROP (MonPred I PROP) where
  embed_later _ := (MonPred.ext fun _ => rfl).to_bi

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

@[rocq_alias monPred_bi_persistently_exist]
instance [BIPersistentlyExist PROP] : BIPersistentlyExist (MonPred I PROP) where
  persistently_sExists_1 Ψ := entails_at.mpr fun i => by
    refine (BIPersistentlyExist.persistently_sExists_1 _).trans ?_
    refine exists_elim fun p => pure_elim_left fun ⟨q, hΨ, hq⟩ => ?_
    subst hq
    exact (and_intro (pure_intro hΨ) BIBase.Entails.rfl).trans
      (MonPred.sExists_at_intro (q := iprop(⌜Ψ q⌝ ∧ <pers> q)) i ⟨q, rfl⟩)

@[rocq_alias monPred_bi_later_contractive]
instance [BIStepIndexed SI PROP] [SIdxFinite SI] [BILaterContractive SI PROP] :
    BILaterContractive SI (MonPred I PROP) where
  distLater_dist h := dist_at.mpr fun i =>
    (‹BILaterContractive SI PROP›).distLater_dist fun m hm => dist_at.mp (h m hm) i

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
  intro := entails_at.mpr fun _ => bupd_intro
  mono h := entails_at.mpr fun i => BIUpdate.mono (entails_at.mp h i)
  trans := entails_at.mpr fun _ => BIUpdate.trans
  frame_right := entails_at.mpr fun _ => bupd_frame_right

#rocq_ignore monPred_bupd_mixin "Rocq mixin record; subsumed by the BIUpdate instance."

instance [BIStepIndexed SI PROP] [SIdxFinite SI] [BIUpdate PROP] [BUpdNE SI PROP] :
    BUpdNE SI (MonPred I PROP) where
  bupd_ne := ⟨fun _ _ _ h => dist_at.mpr fun i => (bupd_ne (SI := SI)).ne (dist_at.mp h i)⟩

@[rocq_alias monPred_bi_embed_bupd]
instance [BIUpdate PROP] : BiEmbedBUpd PROP (MonPred I PROP) where
  embed_bupd _ := (MonPred.ext fun _ => rfl).to_bi

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

instance [BIStepIndexed SI PROP] [SIdxFinite SI] [BIFUpdate PROP] [FUpdNE SI PROP] :
    FUpdNE SI (MonPred I PROP) where
  fupd_ne := ⟨fun _ _ _ h => dist_at.mpr fun i => (FUpdNE.fupd_ne (SI := SI)).ne (dist_at.mp h i)⟩

@[rocq_alias monPred_bi_bupd_fupd]
instance [BIUpdate PROP] [BIFUpdate PROP] [BIUpdateFUpdate PROP] :
    BIUpdateFUpdate (MonPred I PROP) where
  fupd_of_bupd := entails_at.mpr fun _ => BIUpdateFUpdate.fupd_of_bupd

@[rocq_alias monPred_bi_embed_fupd]
instance [BIFUpdate PROP] : BiEmbedFUpd PROP (MonPred I PROP) where
  embed_fupd _ _ _ := (MonPred.ext fun _ => rfl).to_bi

end Updates

/-- A monotone predicate `P` is *objective* if its value does not depend on the
index: `P i ⊢ P j` for all `i j`. Equivalently `P ⊣⊢ <obj> P`. -/
@[rocq_alias Objective]
class Objective {I : BiIndex} {PROP : Type _} [BI.BIBase PROP] (P : MonPred I PROP) : Prop where
  objective_at : ∀ i j : I.car, P.monPred_at i ⊢ P.monPred_at j

namespace MonPred
variable {I : BiIndex} {PROP : Type _} [BI PROP] [BIStepIndexed SI PROP] [SIdxFinite SI]

omit [SIdxFinite SI] in
@[rocq_alias monPred_at_emp]
theorem monPred_at_emp (i : I.car) :
    emp.monPred_at i ⊣⊢@{PROP} emp :=
  .rfl

@[rocq_alias monPred_at_pure]
theorem monPred_at_pure (i : I.car) (φ : Prop) :
    (iprop(⌜φ⌝) : MonPred I PROP).monPred_at i ⊣⊢ ⌜φ⌝ :=
  .rfl

@[rocq_alias monPred_at_and]
theorem monPred_at_and (i : I.car) (P Q : MonPred I PROP) :
    iprop(P ∧ Q).monPred_at i ⊣⊢ P.monPred_at i ∧ Q.monPred_at i :=
  .rfl

@[rocq_alias monPred_at_or]
theorem monPred_at_or (i : I.car) (P Q : MonPred I PROP) :
    iprop(P ∨ Q).monPred_at i ⊣⊢ P.monPred_at i ∨ Q.monPred_at i :=
  .rfl

@[rocq_alias monPred_at_impl]
theorem monPred_at_impl (i : I.car) (P Q : MonPred I PROP) :
    iprop(P → Q).monPred_at i ⊣⊢
      ∀ j, ⌜I.rel.le i j⌝ → P.monPred_at j → Q.monPred_at j :=
  .rfl

@[rocq_alias monPred_at_forall]
theorem monPred_at_forall {α : Sort _} (i : I.car) (Φ : α → MonPred I PROP) :
    iprop(∀ x, Φ x).monPred_at i ⊣⊢ ∀ x, (Φ x).monPred_at i :=
  ⟨forall_intro fun x => sForall_at_elim i ⟨x, rfl⟩,
   sForall_at_intro i fun _ ⟨x, hx⟩ => hx ▸ forall_elim x⟩

@[rocq_alias monPred_at_exist]
theorem monPred_at_exist {α : Sort _} (i : I.car) (Φ : α → MonPred I PROP) :
    iprop(∃ x, Φ x).monPred_at i ⊣⊢ ∃ x, (Φ x).monPred_at i :=
  ⟨sExists_at_elim i fun _ ⟨x, hx⟩ =>
    hx ▸ exists_intro (Ψ := fun y => (Φ y).monPred_at i) x,
   exists_elim fun x => sExists_at_intro i ⟨x, rfl⟩⟩

@[rocq_alias monPred_at_sep]
theorem monPred_at_sep (i : I.car) (P Q : MonPred I PROP) :
    iprop(P ∗ Q).monPred_at i ⊣⊢ P.monPred_at i ∗ Q.monPred_at i :=
  .rfl

@[rocq_alias monPred_at_wand]
theorem monPred_at_wand (i : I.car) (P Q : MonPred I PROP) :
    iprop(P -∗ Q).monPred_at i ⊣⊢
      iprop(∀ j, ⌜I.rel.le i j⌝ → P.monPred_at j -∗ Q.monPred_at j) :=
  .rfl

@[rocq_alias monPred_at_persistently]
theorem monPred_at_persistently (i : I.car) (P : MonPred I PROP) :
    iprop(<pers> P).monPred_at i ⊣⊢ <pers> (P.monPred_at i) :=
  .rfl

@[rocq_alias monPred_at_later]
theorem monPred_at_later (i : I.car) (P : MonPred I PROP) :
    iprop(▷ P).monPred_at i ⊣⊢ ▷ P.monPred_at i :=
  .rfl

omit [SIdxFinite SI] in
@[rocq_alias monPred_at_in]
theorem monPred_at_in (i j : I.car) :
    (monPred_in j : MonPred I PROP).monPred_at i ⊣⊢ ⌜I.rel.le j i⌝ :=
  .rfl

omit [SIdxFinite SI] in
@[rocq_alias monPred_at_embed]
theorem monPred_at_embed (i : I.car) (P : PROP) :
    (embed P : MonPred I PROP).monPred_at i ⊣⊢ P :=
  .rfl

omit [SIdxFinite SI] in
@[rocq_alias monPred_at_objectively]
theorem monPred_at_objectively (i : I.car) (P : MonPred I PROP) :
    iprop(<obj> P).monPred_at i ⊣⊢ ∀ j, P.monPred_at j :=
  .rfl

omit [SIdxFinite SI] in
@[rocq_alias monPred_at_subjectively]
theorem monPred_at_subjectively (i : I.car) (P : MonPred I PROP) :
    iprop(<subj> P).monPred_at i ⊣⊢ ∃ j, P.monPred_at j :=
  .rfl

@[rocq_alias monPred_at_affinely]
theorem monPred_at_affinely (i : I.car) (P : MonPred I PROP) :
    iprop(<affine> P).monPred_at i ⊣⊢ <affine> (P.monPred_at i) :=
  .rfl

@[rocq_alias monPred_at_absorbingly]
theorem monPred_at_absorbingly (i : I.car) (P : MonPred I PROP) :
    iprop(<absorb> P).monPred_at i ⊣⊢ <absorb> (P.monPred_at i) :=
  .rfl

@[rocq_alias monPred_at_intuitionistically]
theorem monPred_at_intuitionistically (i : I.car) (P : MonPred I PROP) :
    iprop(□ P).monPred_at i ⊣⊢ □ P.monPred_at i :=
  .rfl

@[rocq_alias monPred_at_affinely_if]
theorem monPred_at_affinely_if (i : I.car) (p : Bool) (P : MonPred I PROP) :
    iprop(<affine>?p P).monPred_at i ⊣⊢ <affine>?p P.monPred_at i := by
  cases p <;> exact .rfl

@[rocq_alias monPred_at_absorbingly_if]
theorem monPred_at_absorbingly_if (i : I.car) (p : Bool) (P : MonPred I PROP) :
    iprop(<absorb>?p P).monPred_at i ⊣⊢ <absorb>?p P.monPred_at i := by
  cases p <;> exact .rfl

@[rocq_alias monPred_at_intuitionistically_if]
theorem monPred_at_intuitionistically_if (i : I.car) (p : Bool) (P : MonPred I PROP) :
    iprop(□?p P).monPred_at i ⊣⊢ □?p P.monPred_at i := by
  cases p <;> exact .rfl

@[rocq_alias monPred_at_persistently_if]
theorem monPred_at_persistently_if (i : I.car) (p : Bool) (P : MonPred I PROP) :
    iprop(<pers>?p P).monPred_at i ⊣⊢ <pers>?p P.monPred_at i := by
  cases p <;> exact .rfl

@[rocq_alias monPred_at_except_0]
theorem monPred_at_except_0 (i : I.car) (P : MonPred I PROP) :
    iprop(◇ P).monPred_at i ⊣⊢ ◇ P.monPred_at i :=
  .rfl

@[rocq_alias monPred_at_only_0]
theorem monPred_at_only0 (i : I.car) (P : MonPred I PROP) :
    iprop(<only0> P).monPred_at i ⊣⊢ <only0> P.monPred_at i :=
  ⟨upclosed_at_elim i, upclosed_false_imp_intro P i⟩

@[rocq_alias monPred_at_laterN]
theorem monPred_at_laterN (n : Nat) (i : I.car) (P : MonPred I PROP) :
    iprop(▷^[n] P).monPred_at i ⊣⊢ ▷^[n] P.monPred_at i := by
  induction n with
  | zero => exact .rfl
  | succ n ih => exact (monPred_at_later i _).trans (later_congr ih)

@[rocq_alias monPred_at_bupd]
theorem monPred_at_bupd [BIUpdate PROP] (i : I.car) (P : MonPred I PROP) :
    iprop(|==> P).monPred_at i ⊣⊢ |==> P.monPred_at i :=
  .rfl

@[rocq_alias monPred_at_fupd]
theorem monPred_at_fupd [BIFUpdate PROP] (i : I.car) (E1 E2 : CoPset) (P : MonPred I PROP) :
    iprop(|={E1,E2}=> P).monPred_at i ⊣⊢ |={E1,E2}=> P.monPred_at i :=
  .rfl

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

omit [SIdxFinite SI] in
@[rocq_alias monPred_at_ne]
theorem monPred_at_ne (i : I.car) :
    OFE.NonExpansive SI (fun P : MonPred I PROP => P.monPred_at i) :=
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
  timeless := (monPred_at_only0 i P).mpr.trans (entails_at.mp Timeless.timeless i)

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
    iprop(P → Q).monPred_at i ⊢ P.monPred_at i → Q.monPred_at i :=
  (forall_elim i).trans (pure_imp_elim (Std.Refl.refl i : I.rel.le i i))

@[rocq_alias monPred_wand_force]
theorem monPred_wand_force (i : I.car) (P Q : MonPred I PROP) :
    iprop(P -∗ Q).monPred_at i ⊢ P.monPred_at i -∗ Q.monPred_at i :=
  (forall_elim i).trans (pure_imp_elim (Std.Refl.refl i : I.rel.le i i))

/-! ### The `monPred_in` assertion -/

@[rocq_alias monPred_in_intro]
theorem monPred_in_intro (P : MonPred I PROP) :
    P ⊢ iprop(∃ i, monPred_in i ∧ ⎡P.monPred_at i⎤) := by
  refine entails_at.mpr fun j => ?_
  refine (and_intro (pure_intro (Std.Refl.refl j : I.rel.le j j)) .rfl).trans ?_
  refine (exists_intro (Ψ := fun i =>
    (iprop(monPred_in i ∧ ⎡P.monPred_at i⎤) : MonPred I PROP).monPred_at j) j).trans ?_
  refine (monPred_at_exist j fun i => iprop(monPred_in i ∧ ⎡P.monPred_at i⎤)).mpr

@[rocq_alias monPred_in_elim]
theorem monPred_in_elim (P : MonPred I PROP) (i : I.car) :
    monPred_in i ⊢ ⎡P.monPred_at i⎤ → P :=
  entails_at.mpr fun j =>
    pure_elim (I.rel.le i j) .rfl fun hij =>
      forall_intro fun _k => imp_intro_swap <| pure_elim_left fun hjk =>
        imp_intro <| and_elim_r.trans (P.monPred_mono (Trans.trans hij hjk))

@[rocq_alias monPred_in_mono]
theorem monPred_in_mono {i j : I.car} (h : I.rel.le j i) :
    monPred_in i ⊢@{MonPred I PROP} monPred_in j :=
  entails_at.mpr fun _ => pure_mono fun hik => Trans.trans h hik

#rocq_ignore monPred_in_proper "Use monPred_in_mono."

@[rocq_alias monPred_in_flip_mono]
theorem monPred_in_flip_mono {i j : I.car} (h : I.rel.le i j) :
    monPred_in j ⊢@{MonPred I PROP} monPred_in i :=
  monPred_in_mono h

@[rocq_alias monPred_in_persistent]
instance monPred_in_persistent (i : I.car) :
    Persistent (monPred_in i : MonPred I PROP) where
  persistent := entails_at.mpr fun j => (pure_persistent (I.rel.le i j)).persistent

@[rocq_alias monPred_in_absorbing]
instance monPred_in_absorbing (i : I.car) :
    Absorbing (monPred_in i : MonPred I PROP) where
  absorbing := entails_at.mpr fun j => (pure_absorbing (I.rel.le i j)).absorbing

@[rocq_alias monPred_in_timeless]
instance monPred_in_timeless (i : I.car) :
    Timeless (monPred_in i : MonPred I PROP) where
  timeless := entails_at.mpr fun j => (monPred_at_only0 j _).mp.trans only0_pure.mp

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
instance objectively_objective (P : MonPred I PROP) : Objective iprop(<obj> P) where
  objective_at _ _ := .rfl

@[rocq_alias subjectively_objective]
instance subjectively_objective (P : MonPred I PROP) : Objective iprop(<subj> P) where
  objective_at _ _ := .rfl

@[rocq_alias and_objective]
instance and_objective (P Q : MonPred I PROP) [Objective P] [Objective Q] :
    Objective iprop(P ∧ Q) where
  objective_at i j := and_mono (Objective.objective_at i j) (Objective.objective_at i j)

@[rocq_alias or_objective]
instance or_objective (P Q : MonPred I PROP) [Objective P] [Objective Q] :
    Objective iprop(P ∨ Q) where
  objective_at i j := or_mono (Objective.objective_at i j) (Objective.objective_at i j)

@[rocq_alias sep_objective]
instance sep_objective (P Q : MonPred I PROP) [Objective P] [Objective Q] :
    Objective iprop(P ∗ Q) where
  objective_at i j := sep_mono (Objective.objective_at i j) (Objective.objective_at i j)

@[rocq_alias impl_objective]
instance impl_objective (P Q : MonPred I PROP) [Objective P] [Objective Q] :
    Objective iprop(P → Q) where
  objective_at i _j := by
    refine forall_intro fun k => imp_intro ?_
    refine and_elim_l.trans ?_
    refine (forall_elim i).trans ?_
    refine (pure_imp_elim <| Std.Refl.refl i).trans ?_
    exact imp_mono (Objective.objective_at k i) (Objective.objective_at i k)

@[rocq_alias wand_objective]
instance wand_objective (P Q : MonPred I PROP) [Objective P] [Objective Q] :
    Objective iprop(P -∗ Q) where
  objective_at i _j := by
    refine forall_intro fun k => imp_intro ?_
    refine and_elim_l.trans ?_
    refine (forall_elim i).trans ?_
    refine (pure_imp_elim (Std.Refl.refl i : I.rel.le i i)).trans ?_
    exact wand_mono (Objective.objective_at k i) (Objective.objective_at i k)

@[rocq_alias forall_objective]
instance forall_objective {α : Sort _} (Φ : α → MonPred I PROP) [∀ x, Objective (Φ x)] :
    Objective iprop(∀ x, Φ x) where
  objective_at i j := (monPred_at_forall i Φ).mp.trans <|
    (forall_mono fun _ => Objective.objective_at i j).trans (monPred_at_forall j Φ).mpr

@[rocq_alias exists_objective]
instance exists_objective {α : Sort _} (Φ : α → MonPred I PROP) [∀ x, Objective (Φ x)] :
    Objective iprop(∃ x, Φ x) where
  objective_at i j := (monPred_at_exist i Φ).mp.trans <|
    (exists_mono fun _ => Objective.objective_at i j).trans (monPred_at_exist j Φ).mpr

@[rocq_alias persistently_objective]
instance persistently_objective (P : MonPred I PROP) [Objective P] :
    Objective iprop(<pers> P) where
  objective_at i j := persistently_mono (Objective.objective_at i j)

@[rocq_alias affinely_objective]
instance affinely_objective (P : MonPred I PROP) [Objective P] :
    Objective iprop(<affine> P) where
  objective_at i j := affinely_mono (Objective.objective_at i j)

@[rocq_alias absorbingly_objective]
instance absorbingly_objective (P : MonPred I PROP) [Objective P] :
    Objective iprop(<absorb> P) where
  objective_at i j := absorbingly_mono (Objective.objective_at i j)

@[rocq_alias intuitionistically_objective]
instance intuitionistically_objective (P : MonPred I PROP) [Objective P] :
    Objective iprop(□ P) where
  objective_at i j := intuitionistically_mono (Objective.objective_at i j)

@[rocq_alias persistently_if_objective]
instance persistently_if_objective (p : Bool) (P : MonPred I PROP) [Objective P] :
    Objective iprop(<pers>?p P) where
  objective_at i j := calc
    _ ⊢ <pers>?p P.monPred_at i        := (monPred_at_persistently_if i p P).mp
    _ ⊢ <pers>?p P.monPred_at j        := persistentlyIf_mono <| Objective.objective_at i j
    _ ⊢ iprop(<pers>?p P).monPred_at j := (monPred_at_persistently_if j p P).mpr

@[rocq_alias affinely_if_objective]
instance affinely_if_objective (p : Bool) (P : MonPred I PROP) [Objective P] :
    Objective iprop(<affine>?p P) where
  objective_at i j := calc
    _ ⊢ <affine>?p P.monPred_at i        := (monPred_at_affinely_if i p P).mp
    _ ⊢ <affine>?p P.monPred_at j        := affinelyIf_mono <| Objective.objective_at i j
    _ ⊢ iprop(<affine>?p P).monPred_at j := (monPred_at_affinely_if j p P).mpr

@[rocq_alias absorbingly_if_objective]
instance absorbingly_if_objective (p : Bool) (P : MonPred I PROP) [Objective P] :
    Objective iprop(<absorb>?p P) where
  objective_at i j := calc
    _ ⊢ <absorb>?p P.monPred_at i        := (monPred_at_absorbingly_if i p P).mp
    _ ⊢ <absorb>?p P.monPred_at j        := absorbinglyIf_mono <| Objective.objective_at i j
    _ ⊢ iprop(<absorb>?p P).monPred_at j := (monPred_at_absorbingly_if j p P).mpr

@[rocq_alias intuitionistically_if_objective]
instance intuitionistically_if_objective (p : Bool) (P : MonPred I PROP) [Objective P] :
    Objective iprop(□?p P) where
  objective_at i j := calc
    _ ⊢ □?p P.monPred_at i        := (monPred_at_intuitionistically_if i p P).mp
    _ ⊢ □?p P.monPred_at j        := intuitionisticallyIf_mono <| Objective.objective_at i j
    _ ⊢ iprop(□?p P).monPred_at j := (monPred_at_intuitionistically_if j p P).mpr

@[rocq_alias later_objective]
instance later_objective (P : MonPred I PROP) [Objective P] : Objective iprop(▷ P) where
  objective_at i j := later_mono (Objective.objective_at i j)

@[rocq_alias laterN_objective]
instance laterN_objective (n : Nat) (P : MonPred I PROP) [Objective P] :
    Objective iprop(▷^[n] P) where
  objective_at i j := calc
    _ ⊢ ▷^[n] P.monPred_at i        := (monPred_at_laterN n i P).mp
    _ ⊢ ▷^[n] P.monPred_at j        := laterN_mono n <| Objective.objective_at i j
    _ ⊢ iprop(▷^[n] P).monPred_at j := (monPred_at_laterN n j P).mpr

@[rocq_alias except0_objective]
instance except0_objective (P : MonPred I PROP) [Objective P] : Objective iprop(◇ P) where
  objective_at i j := except0_mono (Objective.objective_at i j)

@[rocq_alias bupd_objective]
instance bupd_objective [BIUpdate PROP] (P : MonPred I PROP) [Objective P] :
    Objective iprop(|==> P) where
  objective_at i j := BIUpdate.mono (Objective.objective_at i j)

@[rocq_alias fupd_objective]
instance fupd_objective [BIFUpdate PROP] (E1 E2 : CoPset) (P : MonPred I PROP) [Objective P] :
    Objective iprop(|={E1,E2}=> P) where
  objective_at i j := BIFUpdate.mono (Objective.objective_at i j)

/-! ### Later credits -/

section LaterCredits

variable [BILaterCredits PROP]

@[rocq_alias monPred_defs.monPred_lc]
def lc (n : Nat) : MonPred I PROP := MonPred.mk (fun _ => £ n) fun _ => .rfl

#rocq_ignore monPred_defs.monPred_lc_def "Not needed"
#rocq_ignore monPred_defs.monPred_lc_aux "Not needed"
#rocq_ignore monPred_defs.monPred_lc_unseal "Not needed"
#rocq_ignore monPred_lc_unseal "Not needed"

@[rocq_alias monPred_bi_lc]
instance monPred_bi_lc : BILaterCredits (MonPred I PROP) where
  lc := MonPred.lc
  lc_split := ⟨entails_at.mpr fun _ => lc_split.mp, entails_at.mpr fun _ => lc_split.mpr⟩
  lc_timeless n := ⟨entails_at.mpr fun j => (monPred_at_only0 j _).mp.trans (lc_timeless n).timeless⟩
  lc_0_persistent := ⟨entails_at.mpr fun _ => lc_0_persistent.persistent⟩
  lc_affine n := ⟨entails_at.mpr fun _ => (lc_affine n).affine⟩

#rocq_ignore monPred_lc_mixin "Subsumed by the BILaterCredits instance."

@[rocq_alias monPred_at_lc]
theorem monPred_at_lc (i : I) (n : Nat) :
  (lc (PROP := MonPred I PROP) n).monPred_at i ⊣⊢ £ n := .rfl

@[rocq_alias lc_objective]
instance lc_objective (n : Nat) : Objective (I := I) (PROP := PROP) (£ n) where
  objective_at _ _ := .rfl

@[rocq_alias monPred_bi_bupd_lc]
instance monPred_bi_bupd_lc [BIUpdate PROP] [BIBUpdLaterCredits PROP] :
    BIBUpdLaterCredits (MonPred I PROP) where
  lc_zero := entails_at.mpr fun _ => lc_zero

@[rocq_alias monPred_bi_fupd_lc]
instance monPred_bi_fupd_lc [BIFUpdate PROP] [BIFUpdLaterCredits PROP] :
    BIFUpdLaterCredits (MonPred I PROP) where
  lc_fupd_elim_later := entails_wand <| wand_intro <|
    entails_at.mpr fun _ => wand_elim (wand_entails lc_fupd_elim_later)

end LaterCredits

/-! ### The `objectively` modality -/

@[rocq_alias objective_objectively]
theorem objective_objectively (P : MonPred I PROP) [Objective P] :
    P ⊢ <obj> P :=
  entails_at.mpr fun i => forall_intro fun k => Objective.objective_at i k

@[rocq_alias objective_subjectively]
theorem objective_subjectively (P : MonPred I PROP) [Objective P] :
    <subj> P ⊢ P :=
  entails_at.mpr fun i => exists_elim fun k => Objective.objective_at k i

@[rocq_alias monPred_objectively_elim]
theorem monPred_objectively_elim (P : MonPred I PROP) : <obj> P ⊢ P :=
  entails_at.mpr fun i => forall_elim i

@[rocq_alias monPred_objectively_idemp]
theorem monPred_objectively_idemp (P : MonPred I PROP) :
    <obj> <obj> P ⊣⊢ <obj> P :=
  ⟨monPred_objectively_elim _, objective_objectively _⟩

@[rocq_alias monPred_objectively_mono]
theorem monPred_objectively_mono {P Q : MonPred I PROP} (h : P ⊢ Q) :
    <obj> P ⊢ <obj> Q :=
  entails_at.mpr fun _ => forall_mono fun k => entails_at.mp h k

omit [SIdxFinite SI] in
@[rocq_alias monPred_objectively_ne]
theorem monPred_objectively_ne :
    OFE.NonExpansive SI (objectively (I := I) (PROP := PROP)) :=
  ⟨fun _ _ _ h => dist_at.mpr fun _ => forall_ne fun k => dist_at.mp h k⟩

#rocq_ignore monPred_objectively_mono' "Use monPred_objectively_mono."
#rocq_ignore monPred_objectively_flip_mono' "Use monPred_objectively_mono."
#rocq_ignore monPred_objectively_proper "Use monPred_objectively_ne."

@[rocq_alias monPred_objectively_embed]
theorem monPred_objectively_embed (P : PROP) :
    <obj> ⎡P⎤ ⊣⊢@{MonPred I PROP} ⎡P⎤ :=
  ⟨monPred_objectively_elim _, objective_objectively _⟩

@[rocq_alias monPred_objectively_emp]
theorem monPred_objectively_emp :
    <obj> emp ⊣⊢@{MonPred I PROP} emp :=
  ⟨monPred_objectively_elim _, objective_objectively _⟩

@[rocq_alias monPred_objectively_pure]
theorem monPred_objectively_pure (φ : Prop) :
    <obj> ⌜φ⌝ ⊣⊢@{MonPred I PROP} ⌜φ⌝ :=
  ⟨monPred_objectively_elim _, objective_objectively _⟩

@[rocq_alias monPred_objectively_and]
theorem monPred_objectively_and (P Q : MonPred I PROP) :
    <obj> (P ∧ Q) ⊣⊢ <obj> P ∧ <obj> Q :=
  ⟨entails_at.mpr fun _ => and_intro
      (forall_intro fun k => (forall_elim k).trans and_elim_l)
      (forall_intro fun k => (forall_elim k).trans and_elim_r),
   entails_at.mpr fun _ => forall_intro fun k =>
      and_intro (and_elim_l.trans (forall_elim k)) (and_elim_r.trans (forall_elim k))⟩

@[rocq_alias monPred_objectively_or]
theorem monPred_objectively_or (P Q : MonPred I PROP) :
    <obj> P ∨ <obj> Q ⊢ <obj> (P ∨ Q) :=
  entails_at.mpr fun _ => or_elim
    (forall_intro fun k => (forall_elim k).trans or_intro_l)
    (forall_intro fun k => (forall_elim k).trans or_intro_r)

@[rocq_alias monPred_objectively_forall]
theorem monPred_objectively_forall {α : Sort _} (Φ : α → MonPred I PROP) :
    <obj> (∀ x, Φ x) ⊣⊢ ∀ x, <obj> (Φ x) := by
  constructor
  · refine entails_at.mpr fun i =>
      (forall_intro fun x => forall_intro fun k => ?_).trans
      (monPred_at_forall i fun x => iprop(<obj> (Φ x))).mpr
    calc
      _ ⊢ iprop(∀ x, Φ x).monPred_at k := forall_elim k
      _ ⊢ ∀ x, (Φ x).monPred_at k      := (monPred_at_forall k Φ).mp
      _ ⊢ (Φ x).monPred_at k           := forall_elim x
  · refine entails_at.mpr fun i => forall_intro fun k => ?_
    calc
      _ ⊢ ∀ x, iprop(<obj> Φ x).monPred_at i :=
          (monPred_at_forall i fun x => iprop(<obj> (Φ x))).mp
      _ ⊢ ∀ a, (Φ a).monPred_at k :=
          forall_intro fun x => (forall_elim x).trans (forall_elim k)
      _ ⊢ iprop(∀ x, Φ x).monPred_at k := (monPred_at_forall k Φ).mpr

@[rocq_alias monPred_objectively_exist]
theorem monPred_objectively_exist {α : Sort _} (Φ : α → MonPred I PROP) :
    (∃ x, <obj> (Φ x)) ⊢ <obj> (∃ x, Φ x) := by
  refine entails_at.mpr fun i =>
    (monPred_at_exist i fun x => iprop(<obj> (Φ x))).mp.trans <|
    exists_elim fun x => forall_intro fun k => ?_
  calc
    _ ⊢ (Φ x).monPred_at k           := forall_elim k
    _ ⊢ ∃ a, (Φ a).monPred_at k      := exists_intro (Ψ := fun x => (Φ x).monPred_at k) x
    _ ⊢ iprop(∃ x, Φ x).monPred_at k := (monPred_at_exist k Φ).mpr

@[rocq_alias monPred_objectively_sep_2]
theorem monPred_objectively_sep_2 (P Q : MonPred I PROP) :
    <obj> P ∗ <obj> Q ⊢ <obj> (P ∗ Q) :=
  entails_at.mpr fun _ => forall_intro fun k => sep_mono (forall_elim k) (forall_elim k)

@[rocq_alias monPred_objectively_sep]
theorem monPred_objectively_sep {bot : I.car} [BiIndexBottom I bot] (P Q : MonPred I PROP) :
    <obj> (P ∗ Q) ⊣⊢ <obj> P ∗ <obj> Q :=
  ⟨entails_at.mpr fun _ =>
      (forall_elim bot).trans (sep_mono
        (forall_intro fun k => P.monPred_mono (BiIndexBottom.bot_le k))
        (forall_intro fun k => Q.monPred_mono (BiIndexBottom.bot_le k))),
   monPred_objectively_sep_2 P Q⟩

@[rocq_alias monPred_objectively_affine]
instance monPred_objectively_affine (P : MonPred I PROP) [Affine P] :
    Affine iprop(<obj> P) where
  affine := entails_at.mpr fun _ => (forall_elim (default : I.car)).trans Affine.affine

@[rocq_alias monPred_objectively_absorbing]
instance monPred_objectively_absorbing (P : MonPred I PROP) [Absorbing P] :
    Absorbing iprop(<obj> P) where
  absorbing := entails_at.mpr fun _ => forall_intro fun k =>
    (absorbingly_mono (forall_elim k)).trans Absorbing.absorbing

@[rocq_alias monPred_objectively_persistent]
instance monPred_objectively_persistent [BIPersistentlyForall PROP] (P : MonPred I PROP)
    [Persistent P] : Persistent iprop(<obj> P) where
  persistent := entails_at.mpr fun _ =>
    (forall_mono fun _ => Persistent.persistent).trans persistently_forall.mpr

@[rocq_alias monPred_objectively_timeless]
instance monPred_objectively_timeless (P : MonPred I PROP) [Timeless P] :
    Timeless iprop(<obj> P) where
  timeless := entails_at.mpr fun i =>
    (monPred_at_only0 i _).mp.trans <| only0_forall.mp.trans <| forall_mono fun j =>
      (monPred_at_only0 j P).mpr.trans (entails_at.mp Timeless.timeless j)

/-! ### The `subjectively` modality -/

@[rocq_alias monPred_subjectively_intro]
theorem monPred_subjectively_intro (P : MonPred I PROP) : P ⊢ <subj> P :=
  entails_at.mpr fun i => exists_intro i

@[rocq_alias monPred_subjectively_mono]
theorem monPred_subjectively_mono {P Q : MonPred I PROP} (h : P ⊢ Q) :
    <subj> P ⊢ <subj> Q :=
  entails_at.mpr fun _ => exists_mono fun k => entails_at.mp h k

omit [SIdxFinite SI] in
@[rocq_alias monPred_subjectively_ne]
theorem monPred_subjectively_ne :
    OFE.NonExpansive SI (subjectively (I := I) (PROP := PROP)) :=
  ⟨fun _ _ _ h => dist_at.mpr fun _ => exists_ne fun k => dist_at.mp h k⟩

#rocq_ignore monPred_subjectively_mono' "Use monPred_subjectively_mono."
#rocq_ignore monPred_subjectively_flip_mono' "Use monPred_subjectively_mono."
#rocq_ignore monPred_subjectively_proper "Use monPred_subjectively_ne."

@[rocq_alias monPred_subjectively_idemp]
theorem monPred_subjectively_idemp (P : MonPred I PROP) :
    <subj> (<subj> P) ⊣⊢ <subj> P :=
  ⟨objective_subjectively _, monPred_subjectively_intro _⟩

@[rocq_alias monPred_subjectively_and]
theorem monPred_subjectively_and (P Q : MonPred I PROP) :
    <subj> (P ∧ Q) ⊢ <subj> P ∧ <subj> Q :=
  entails_at.mpr fun _ =>
    and_intro (exists_mono fun _ => and_elim_l) (exists_mono fun _ => and_elim_r)

@[rocq_alias monPred_subjectively_or]
theorem monPred_subjectively_or (P Q : MonPred I PROP) :
    <subj> (P ∨ Q) ⊣⊢ <subj> P ∨ <subj> Q :=
  ⟨entails_at.mpr fun _ => or_exists.mp, entails_at.mpr fun _ => or_exists.mpr⟩

@[rocq_alias monPred_subjectively_forall]
theorem monPred_subjectively_forall {α : Sort _} (Φ : α → MonPred I PROP) :
    <subj> (∀ x, Φ x) ⊢ ∀ x, <subj> (Φ x) := by
  refine entails_at.mpr fun i => ?_
  refine .trans ?_ (monPred_at_forall i fun x => iprop(<subj> (Φ x))).mpr
  refine forall_intro fun x => exists_elim fun k => ?_
  calc
    _ ⊢ ∀ x, (Φ x).monPred_at k := (monPred_at_forall k Φ).mp
    _ ⊢ (Φ x).monPred_at k      := forall_elim x
    _ ⊢ ∃ a, (Φ x).monPred_at a := exists_intro k

@[rocq_alias monPred_subjectively_exist]
theorem monPred_subjectively_exist {α : Sort _} (Φ : α → MonPred I PROP) :
    <subj> (∃ x, Φ x) ⊣⊢ ∃ x, <subj> (Φ x) := by
  constructor
  · refine entails_at.mpr fun i => exists_elim fun k => ?_
    refine (monPred_at_exist k Φ).mp.trans <| exists_elim fun x => ?_
    calc (Φ x).monPred_at k
      _ ⊢ ∃ j, (Φ x).monPred_at j := exists_intro k
      _ ⊢ ∃ x, iprop(<subj> (Φ x)).monPred_at i :=
          exists_intro (Ψ := fun y => iprop(<subj> (Φ y) : MonPred I PROP).monPred_at i) x
      _ ⊢ iprop(∃ x, <subj> (Φ x)).monPred_at i :=
          (monPred_at_exist i fun x => iprop(<subj> (Φ x))).mpr
  · refine entails_at.mpr fun i =>
      (monPred_at_exist i fun x => iprop(<subj> (Φ x))).mp.trans <|
      exists_elim fun x => exists_elim fun k => ?_
    calc (Φ x).monPred_at k
      _ ⊢ ∃ x, (Φ x).monPred_at k := exists_intro (Ψ := fun y => (Φ y).monPred_at k) x
      _ ⊢ iprop(∃ x, Φ x).monPred_at k := (monPred_at_exist k Φ).mpr
      _ ⊢ iprop(<subj> (∃ x, Φ x)).monPred_at i := exists_intro k

@[rocq_alias monPred_subjectively_sep]
theorem monPred_subjectively_sep (P Q : MonPred I PROP) :
    <subj> (P ∗ Q) ⊢ <subj> P ∗ <subj> Q :=
  entails_at.mpr fun _ => exists_elim fun k => sep_mono (exists_intro k) (exists_intro k)

@[rocq_alias monPred_subjectively_affine]
instance monPred_subjectively_affine (P : MonPred I PROP) [Affine P] :
    Affine iprop(<subj> P) where
  affine := entails_at.mpr fun _ => exists_elim fun _ => Affine.affine

@[rocq_alias monPred_subjectively_absorbing]
instance monPred_subjectively_absorbing (P : MonPred I PROP) [Absorbing P] :
    Absorbing iprop(<subj> P) where
  absorbing := entails_at.mpr fun _ =>
    absorbingly_exists.mp.trans (exists_mono fun _ => Absorbing.absorbing)

@[rocq_alias monPred_subjectively_persistent]
instance monPred_subjectively_persistent (P : MonPred I PROP) [Persistent P] :
    Persistent iprop(<subj> P) where
  persistent := entails_at.mpr fun _ =>
    (exists_mono fun _ => Persistent.persistent).trans persistently_exists_mpr

@[rocq_alias monPred_subjectively_timeless]
instance monPred_subjectively_timeless (P : MonPred I PROP) [Timeless P] :
    Timeless iprop(<subj> P) where
  timeless := entails_at.mpr fun i =>
    (monPred_at_only0 i _).mp.trans <| only0_exists.mp.trans <| exists_mono fun j =>
      (monPred_at_only0 j P).mpr.trans (entails_at.mp Timeless.timeless j)

@[rocq_alias monPred_subjectively_persistently]
theorem monPred_subjectively_persistently [BIPersistentlyExist PROP] (P : MonPred I PROP) :
    <subj> (<pers> P) ⊣⊢ <pers> (<subj> P) := by
  constructor
  · exact entails_at.mpr fun _ => persistently_exists_mpr (Ψ := fun j => P.monPred_at j)
  · exact entails_at.mpr fun _ => (persistently_exists (Ψ := fun j => P.monPred_at j)).mp

@[rocq_alias monPred_subjectively_absorbingly]
theorem monPred_subjectively_absorbingly (P : MonPred I PROP) :
    <subj> (<absorb> P) ⊣⊢ <absorb> (<subj> P) := by
  constructor
  · exact entails_at.mpr fun _ => (absorbingly_exists (Φ := fun j => P.monPred_at j)).mpr
  · exact entails_at.mpr fun _ => (absorbingly_exists (Φ := fun j => P.monPred_at j)).mp

@[rocq_alias monPred_subjectively_affinely]
theorem monPred_subjectively_affinely (P : MonPred I PROP) :
    <subj> (<affine> P) ⊣⊢ <affine> (<subj> P) := by
  constructor
  · exact entails_at.mpr fun _ => (affinely_exists (Φ := fun j => P.monPred_at j)).mpr
  · exact entails_at.mpr fun _ => (affinely_exists (Φ := fun j => P.monPred_at j)).mp

@[rocq_alias monPred_subjectively_intuitionistically]
theorem monPred_subjectively_intuitionistically [BIPersistentlyExist PROP] (P : MonPred I PROP) :
    <subj> (□ P) ⊣⊢ □ (<subj> P) :=
  (monPred_subjectively_affinely iprop(<pers> P)).trans <|
    affinely_congr (monPred_subjectively_persistently P)

@[rocq_alias monPred_subjectively_persistently_if]
theorem monPred_subjectively_persistently_if [BIPersistentlyExist PROP]
    (p : Bool) (P : MonPred I PROP) :
    <subj> (<pers>?p P) ⊣⊢ <pers>?p (<subj> P) := by
  cases p
  · exact .rfl
  · exact monPred_subjectively_persistently P

@[rocq_alias monPred_subjectively_absorbingly_if]
theorem monPred_subjectively_absorbingly_if (p : Bool) (P : MonPred I PROP) :
    <subj> (<absorb>?p P) ⊣⊢ <absorb>?p (<subj> P) := by
  cases p
  · exact .rfl
  · exact monPred_subjectively_absorbingly P

@[rocq_alias monPred_subjectively_affinely_if]
theorem monPred_subjectively_affinely_if (p : Bool) (P : MonPred I PROP) :
    <subj> (<affine>?p P) ⊣⊢ <affine>?p (<subj> P) := by
  cases p
  · exact .rfl
  · exact monPred_subjectively_affinely P

@[rocq_alias monPred_subjectively_intuitionistically_if]
theorem monPred_subjectively_intuitionistically_if [BIPersistentlyExist PROP]
    (p : Bool) (P : MonPred I PROP) :
    <subj> (□?p P) ⊣⊢ □?p (<subj> P) := by
  cases p
  · exact .rfl
  · exact monPred_subjectively_intuitionistically P

@[rocq_alias monPred_subjectively_wand]
theorem monPred_subjectively_wand (P Q : MonPred I PROP) :
    ⊢ <subj> P -∗ <obj> (P -∗ <subj> Q) -∗ <subj> Q := by
  refine entails_wand <| wand_intro <| entails_at.mpr fun i => ?_
  refine sep_exists_right.mp.trans <| exists_elim fun j => ?_
  calc
    _ ⊢ P.monPred_at j ∗ iprop(P -∗ <subj> Q).monPred_at j :=
        sep_mono_right (forall_elim j)
    _ ⊢ P.monPred_at j ∗ (P.monPred_at j -∗ iprop(<subj> Q).monPred_at j) :=
        sep_mono_right (monPred_wand_force j P iprop(<subj> Q))
    _ ⊢ iprop(<subj> Q).monPred_at i := wand_elim_right

/-! ### Big separating conjunctions -/

section BigOp
open Iris.Algebra Iris.Algebra.BigOpL Iris.Algebra.BigOpM
open Iris.BI.BigSepL Iris.BI.BigSepM Iris.BI.BigSepS Iris.BI.BigSepMS

omit [SIdxFinite SI] in
theorem monPred_at_hom {op₁ : MonPred I PROP → MonPred I PROP → MonPred I PROP}
    {op₂ : PROP → PROP → PROP} {u₁ : MonPred I PROP} {u₂ : PROP}
    [MonoidOps op₁ u₁] [MonoidOps op₂ u₂] (i : I.car)
    (hop : ∀ {x y}, (op₁ x y).monPred_at i = op₂ (x.monPred_at i) (y.monPred_at i))
    (hunit : u₁.monPred_at i = u₂) :
    MonoidHomomorphism op₁ op₂ u₁ u₂ (· = ·) (fun P : MonPred I PROP => P.monPred_at i) where
  rel_refl := rfl
  rel_trans := Eq.trans
  op_proper ha hb := ha ▸ hb ▸ rfl
  map_op := hop
  map_unit := hunit

@[rocq_alias monPred_at_monoid_and_homomorphism]
instance monPred_at_monoid_and_homomorphism (i : I.car) :
    MonoidHomomorphism (BIBase.and (PROP := MonPred I PROP)) (BIBase.and (PROP := PROP))
      iprop(True) iprop(True) (· = ·) (fun P => P.monPred_at i) :=
  monPred_at_hom i rfl rfl

@[rocq_alias monPred_at_monoid_or_homomorphism]
instance monPred_at_monoid_or_homomorphism (i : I.car) :
    MonoidHomomorphism (BIBase.or (PROP := MonPred I PROP)) (BIBase.or (PROP := PROP))
      iprop(False) iprop(False) (· = ·) (fun P => P.monPred_at i) :=
  monPred_at_hom i rfl rfl

@[rocq_alias monPred_at_monoid_sep_homomorphism]
instance monPred_at_monoid_sep_homomorphism (i : I.car) :
    MonoidHomomorphism (BIBase.sep (PROP := MonPred I PROP)) (BIBase.sep (PROP := PROP))
      BIBase.emp BIBase.emp (· = ·) (fun P => P.monPred_at i) :=
  monPred_at_hom i rfl rfl

@[rocq_alias monPred_at_big_sepL]
theorem monPred_at_big_sepL {α : Type _} (i : I.car) (Φ : Nat → α → MonPred I PROP) (l : List α) :
    ([∗list] k ↦ x ∈ l, Φ k x).monPred_at i ⊣⊢ [∗list] k ↦ x ∈ l, (Φ k x).monPred_at i :=
  (bigOpL_hom (H := monPred_at_monoid_sep_homomorphism i) Φ l).to_bi

@[rocq_alias monPred_at_big_sepM]
theorem monPred_at_big_sepM {K V : Type _} {M : Type _ → Type _} [LawfulFiniteMap M K]
    (i : I.car) (Φ : K → V → MonPred I PROP) (m : M V) :
    ([∗map] k ↦ x ∈ m, Φ k x).monPred_at i ⊣⊢ [∗map] k ↦ x ∈ m, (Φ k x).monPred_at i :=
  (bigOpM_hom (ι := monPred_at_monoid_sep_homomorphism i) Φ m).to_bi

@[rocq_alias monPred_at_big_sepS]
theorem monPred_at_big_sepS {S α : Type _} [LawfulFiniteSet S α]
    (i : I.car) (Φ : α → MonPred I PROP) (X : S) :
    ([∗set] x ∈ X, Φ x).monPred_at i ⊣⊢ [∗set] x ∈ X, (Φ x).monPred_at i :=
  (BigOpS.hom (monPred_at_monoid_sep_homomorphism i) Φ X).to_bi

@[rocq_alias monPred_at_big_sepMS]
theorem monPred_at_big_sepMS {MS α : Type _} [LawfulFiniteMultiSet MS α]
    (i : I.car) (Φ : α → MonPred I PROP) (X : MS) :
    ([∗mset] x ∈ X, Φ x).monPred_at i ⊣⊢ [∗mset] x ∈ X, (Φ x).monPred_at i :=
  (BigOpMS.hom (monPred_at_monoid_sep_homomorphism i) Φ X).to_bi

@[rocq_alias big_sepL_objective]
instance big_sepL_objective {α : Type _} (Φ : Nat → α → MonPred I PROP) (l : List α)
    [∀ k x, Objective (Φ k x)] : Objective ([∗list] k ↦ x ∈ l, Φ k x) where
  objective_at i j := calc
    _ ⊢ [∗list] k ↦ x ∈ l, (Φ k x).monPred_at i := (monPred_at_big_sepL i Φ l).mp
    _ ⊢ [∗list] k ↦ x ∈ l, (Φ k x).monPred_at j := bigSepL_mono fun _ => Objective.objective_at i j
    _ ⊢ ([∗list] k ↦ x ∈ l, Φ k x).monPred_at j := (monPred_at_big_sepL j Φ l).mpr

@[rocq_alias big_sepM_objective]
instance big_sepM_objective {K V : Type _} {M : Type _ → Type _} [LawfulFiniteMap M K]
    (Φ : K → V → MonPred I PROP) (m : M V) [∀ k x, Objective (Φ k x)] :
    Objective ([∗map] k ↦ x ∈ m, Φ k x) where
  objective_at i j := calc
    _ ⊢ [∗map] k ↦ x ∈ m, (Φ k x).monPred_at i := (monPred_at_big_sepM i Φ m).mp
    _ ⊢ [∗map] k ↦ x ∈ m, (Φ k x).monPred_at j := bigSepM_mono fun _ => Objective.objective_at i j
    _ ⊢ ([∗map] k ↦ x ∈ m, Φ k x).monPred_at j := (monPred_at_big_sepM j Φ m).mpr

@[rocq_alias big_sepS_objective]
instance big_sepS_objective {S α : Type _} [LawfulFiniteSet S α] (Φ : α → MonPred I PROP) (X : S)
    [∀ x, Objective (Φ x)] : Objective ([∗set] x ∈ X, Φ x) where
  objective_at i j := calc
    _ ⊢ [∗set] x ∈ X, (Φ x).monPred_at i := (monPred_at_big_sepS i Φ X).mp
    _ ⊢ [∗set] x ∈ X, (Φ x).monPred_at j := bigSepS_mono fun _ => Objective.objective_at i j
    _ ⊢ ([∗set] x ∈ X, Φ x).monPred_at j := (monPred_at_big_sepS j Φ X).mpr

@[rocq_alias big_sepMS_objective]
instance big_sepMS_objective {MS α : Type _} [LawfulFiniteMultiSet MS α]
    (Φ : α → MonPred I PROP) (X : MS) [∀ x, Objective (Φ x)] :
    Objective (iprop([∗mset] x ∈ X, Φ x)) where
  objective_at i j := (monPred_at_big_sepMS i Φ X).mp.trans <|
    (bigSepMS_mono fun _ => Objective.objective_at i j).trans (monPred_at_big_sepMS j Φ X).mpr

/-! #### `objectively` over big separating conjunctions -/

@[rocq_alias monPred_objectively_monoid_and_homomorphism]
instance monPred_objectively_monoid_and_homomorphism :
    MonoidHomomorphism (BIBase.and (PROP := MonPred I PROP)) BIBase.and iprop(True) iprop(True)
      (· = ·) objectively :=
  MonoidHomomorphism.ofEq
    (fun {x y} => (monPred_objectively_and x y).to_eq)
    (monPred_objectively_pure True).to_eq

@[rocq_alias monPred_objectively_monoid_sep_entails_homomorphism]
instance monPred_objectively_monoid_sep_entails_homomorphism :
    MonoidHomomorphism (BIBase.sep (PROP := MonPred I PROP)) BIBase.sep BIBase.emp BIBase.emp
      (flip Entails) objectively where
  rel_refl {a} := show a ⊢ a from .rfl
  rel_trans {a b c} h1 h2 := .trans (show c ⊢ b from h2) (show b ⊢ a from h1)
  op_proper {a a' b b'} h1 h2 := sep_mono (show a' ⊢ a from h1) (show b' ⊢ b from h2)
  map_op := fun {x y} => monPred_objectively_sep_2 x y
  map_unit := monPred_objectively_emp.mpr

@[rocq_alias monPred_objectively_monoid_sep_homomorphism]
theorem monPred_objectively_monoid_sep_homomorphism {bot : I.car} [BiIndexBottom I bot] :
    MonoidHomomorphism (BIBase.sep (PROP := MonPred I PROP)) BIBase.sep BIBase.emp BIBase.emp
      (· = ·) objectively :=
  MonoidHomomorphism.ofEq
    (fun {x y} => (monPred_objectively_sep (bot := bot) x y).to_eq)
    monPred_objectively_emp.to_eq

@[rocq_alias monPred_objectively_big_sepL_entails]
theorem monPred_objectively_big_sepL_entails {α : Type _} (Φ : Nat → α → MonPred I PROP)
    (l : List α) :
    ([∗list] k ↦ x ∈ l, <obj> (Φ k x)) ⊢ <obj> ([∗list] k ↦ x ∈ l, Φ k x) :=
  bigOpL_hom (H := monPred_objectively_monoid_sep_entails_homomorphism) Φ l

@[rocq_alias monPred_objectively_big_sepL]
theorem monPred_objectively_big_sepL {bot : I.car} [BiIndexBottom I bot] {α : Type _}
    (Φ : Nat → α → MonPred I PROP) (l : List α) :
    <obj> ([∗list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∗list] k ↦ x ∈ l, <obj> (Φ k x) :=
  (bigOpL_hom (H := monPred_objectively_monoid_sep_homomorphism (bot := bot)) Φ l).to_bi

@[rocq_alias monPred_objectively_big_sepM_entails]
theorem monPred_objectively_big_sepM_entails {K V : Type _} {M : Type _ → Type _}
    [LawfulFiniteMap M K] (Φ : K → V → MonPred I PROP) (m : M V) :
    ([∗map] k ↦ x ∈ m, <obj> (Φ k x)) ⊢ <obj> ([∗map] k ↦ x ∈ m, Φ k x) :=
  bigOpM_hom (ι := monPred_objectively_monoid_sep_entails_homomorphism) Φ m

@[rocq_alias monPred_objectively_big_sepM]
theorem monPred_objectively_big_sepM {bot : I.car} [BiIndexBottom I bot] {K V : Type _}
    {M : Type _ → Type _} [LawfulFiniteMap M K] (Φ : K → V → MonPred I PROP) (m : M V) :
    <obj> ([∗map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∗map] k ↦ x ∈ m, <obj> (Φ k x) :=
  (bigOpM_hom (ι := monPred_objectively_monoid_sep_homomorphism (bot := bot)) Φ m).to_bi

@[rocq_alias monPred_objectively_big_sepS_entails]
theorem monPred_objectively_big_sepS_entails {S α : Type _} [LawfulFiniteSet S α]
    (Φ : α → MonPred I PROP) (X : S) :
    ([∗set] x ∈ X, <obj> (Φ x)) ⊢ <obj> ([∗set] x ∈ X, Φ x) :=
  Iris.Algebra.BigOpS.hom monPred_objectively_monoid_sep_entails_homomorphism Φ X

@[rocq_alias monPred_objectively_big_sepS]
theorem monPred_objectively_big_sepS {bot : I.car} [BiIndexBottom I bot] {S α : Type _}
    [LawfulFiniteSet S α] (Φ : α → MonPred I PROP) (X : S) :
    <obj> ([∗set] x ∈ X, Φ x) ⊣⊢ [∗set] x ∈ X, <obj> (Φ x) :=
  BIBase.BiEntails.of_eq
    (Iris.Algebra.BigOpS.hom (monPred_objectively_monoid_sep_homomorphism (bot := bot)) Φ X)

@[rocq_alias monPred_objectively_big_sepMS_entails]
theorem monPred_objectively_big_sepMS_entails {MS α} [LawfulFiniteMultiSet MS α]
    (Φ : α → MonPred I PROP) (X : MS) :
    ([∗mset] y ∈ X, <obj> (Φ y)) ⊢ <obj> ([∗mset] y ∈ X, Φ y) :=
  BigOpMS.hom monPred_objectively_monoid_sep_entails_homomorphism Φ X

@[rocq_alias monPred_objectively_big_sepMS]
theorem monPred_objectively_big_sepMS {bot : I.car} [BiIndexBottom I bot] {MS α}
    [LawfulFiniteMultiSet MS α] (Φ : α → MonPred I PROP) (X : MS) :
    <obj> ([∗mset] y ∈ X, Φ y) ⊣⊢ [∗mset] y ∈ X, <obj> (Φ y) :=
  BIBase.BiEntails.of_eq
    (Iris.Algebra.BigOpMS.hom (monPred_objectively_monoid_sep_homomorphism (bot := bot)) Φ X)

end BigOp

end MonPred

namespace MonPred

/-! ### The plainly modality on `MonPred` (SI-free) -/

section Plainly
variable {I : BiIndex} {PROP : Type _} [BI PROP] [BIPlainly PROP]

/-- `■ P` on `MonPred` is the constant predicate `∀ j, ■ P j`. -/
def plainly (P : MonPred I PROP) : MonPred I PROP where
  monPred_at _ := iprop(∀ j, ■ P.monPred_at j)
  monPred_mono _ := .rfl

private theorem plainly_forall_plain (P : MonPred I PROP) :
    iprop(■ (∀ j, P.monPred_at j)) ⊣⊢ ∀ j, ■ P.monPred_at j := BI.plainly_forall

instance : BIPlainly (MonPred I PROP) where
  plainly := MonPred.plainly
  plainly_mono h := entails_at.mpr fun _ => forall_mono fun j => plainly_mono (entails_at.mp h j)
  plainly_elim_persistently := entails_at.mpr fun i =>
    (forall_elim i).trans plainly_elim_persistently
  plainly_idem_mpr {P} := entails_at.mpr fun _ => forall_intro fun _ =>
    (forall_mono fun _ => plainly_idem_mpr).trans BI.plainly_forall.mpr
  plainly_sForall_2 {Φ} := entails_at.mpr fun i => by
    refine (monPred_at_forall i (fun p : MonPred I PROP => iprop(⌜Φ p⌝ → MonPred.plainly p))).mp.trans ?_
    refine forall_intro fun j => .trans ?_ BIPlainly.plainly_sForall_2
    refine forall_intro fun q => imp_intro_swap <| pure_elim_left fun ⟨p, hp, hq⟩ => ?_
    subst hq
    exact (forall_elim p).trans <| (monPred_impl_force i iprop(⌜Φ p⌝) (MonPred.plainly p)).trans <|
      (pure_imp_elim hp).trans (forall_elim j)
  plainly_impl_plainly {P Q} := entails_at.mpr fun i => by
    refine (monPred_impl_force i (MonPred.plainly P) (MonPred.plainly Q)).trans ?_
    refine forall_intro fun k => ?_
    calc iprop((∀ j, ■ P.monPred_at j) → ∀ j, ■ Q.monPred_at j)
      _ ⊢ (■ (∀ j, P.monPred_at j) → ■ (∀ j, Q.monPred_at j)) :=
          imp_mono (plainly_forall_plain P).mp (plainly_forall_plain Q).mpr
      _ ⊢ ■ (■ (∀ j, P.monPred_at j) → ∀ j, Q.monPred_at j) := plainly_impl_plainly
      _ ⊢ ■ (∀ l, ⌜I.rel.le k l⌝ → (∀ j, ■ P.monPred_at j) → Q.monPred_at l) :=
          plainly_mono <| forall_intro fun l => imp_intro_swap <| pure_elim_left fun _ =>
            (imp_mono (plainly_forall_plain P).mpr (forall_elim l))
  plainly_emp_intro := entails_at.mpr fun _ => forall_intro fun _ => plainly_emp_intro
  plainly_absorb := entails_at.mpr fun _ => forall_intro fun j =>
    (sep_mono_left (forall_elim j)).trans plainly_absorb
  later_plainly := ⟨entails_at.mpr fun _ => later_forall.mp.trans (forall_mono fun _ => later_plainly.mp),
    entails_at.mpr fun _ => (forall_mono fun _ => later_plainly.mpr).trans later_forall.mpr⟩
  persistently_impl_plainly {P Q} := entails_at.mpr fun i => by
    refine (monPred_impl_force i (MonPred.plainly P) iprop(<pers> Q)).trans ?_
    calc iprop((∀ j, ■ P.monPred_at j) → <pers> Q.monPred_at i)
      _ ⊢ (■ (∀ j, P.monPred_at j) → <pers> Q.monPred_at i) :=
          imp_mono_left (plainly_forall_plain P).mp
      _ ⊢ <pers> (■ (∀ j, P.monPred_at j) → Q.monPred_at i) := persistently_impl_plainly
      _ ⊢ <pers> (∀ l, ⌜I.rel.le i l⌝ → (∀ j, ■ P.monPred_at j) → Q.monPred_at l) :=
          persistently_mono <| forall_intro fun l => imp_intro_swap <| pure_elim_left fun hil =>
            imp_mono (plainly_forall_plain P).mpr (Q.monPred_mono hil)
  except0_plainly_2 := entails_at.mpr fun _ =>
    (forall_mono fun _ => BIPlainly.except0_plainly_2).trans except0_forall.mpr

@[rocq_alias monPred_at_plainly]
theorem monPred_at_plainly (i : I.car) (P : MonPred I PROP) :
    iprop(■ P).monPred_at i ⊣⊢ ∀ j, ■ (P.monPred_at j) := .rfl

instance : BiEmbedPlainly PROP (MonPred I PROP) where
  embed_plainly _ := ⟨entails_at.mpr fun _ => forall_intro fun _ => .rfl,
    entails_at.mpr fun _ => forall_elim (default : I.car)⟩

/-- `■` on `MonPred` commutes with existentials when the index has a bottom element. -/
theorem monPred_plainly_exists {bot : I.car} [BiIndexBottom I bot] [BIPlainlyExists PROP] :
    BIPlainlyExists (MonPred I PROP) where
  plainly_sExists_1 {Φ} := entails_at.mpr fun i => by
    refine (forall_elim bot).trans <| BIPlainlyExists.plainly_sExists_1.trans ?_
    refine exists_elim fun q => pure_elim_left fun ⟨p, hp, hq⟩ => ?_
    subst hq
    refine .trans ?_ (monPred_at_exist i (fun p : MonPred I PROP => iprop(⌜Φ p⌝ ∧ ■ p))).mpr
    refine exists_intro_trans p (and_intro (pure_intro hp) ?_)
    exact forall_intro fun k => plainly_mono (p.monPred_mono (BiIndexBottom.bot_le k))

instance [BIUpdate PROP] [BIBUpdatePlainly PROP] : BIBUpdatePlainly (MonPred I PROP) where
  bupd_plainly := entails_at.mpr fun _ => forall_intro fun j =>
    (BIUpdate.mono (forall_elim j)).trans bupd_plainly

instance [BIFUpdate PROP] [BIFUpdatePlainly PROP] : BIFUpdatePlainly (MonPred I PROP) where
  fupd_keep_plainly E2' P R := entails_at.mpr fun i =>
    (and_mono (BIFUpdate.mono (forall_elim i))
      (monPred_wand_force i P iprop(|={_,_}=> R))).trans
      (BIFUpdatePlainly.fupd_keep_plainly E2' (P.monPred_at i) (R.monPred_at i))
  fupd_plainly_later E P := entails_at.mpr fun i =>
    (later_mono (BIFUpdate.mono (forall_elim i))).trans
      (BIFUpdatePlainly.fupd_plainly_later E (P.monPred_at i))
  fupd_plainly_sForall_2 E Φ := entails_at.mpr fun i => by
    refine (monPred_at_forall i
      (fun p : MonPred I PROP => iprop(⌜Φ p⌝ → |={E}=> MonPred.plainly p))).mp.trans ?_
    refine .trans ?_ (BIFUpdatePlainly.fupd_plainly_sForall_2 E _)
    refine forall_intro fun q => imp_intro_swap <| pure_elim_left fun ⟨p, hp, hq⟩ => ?_
    subst hq
    exact (forall_elim p).trans <|
      (monPred_impl_force i iprop(⌜Φ p⌝) iprop(|={E}=> MonPred.plainly p)).trans <|
      (pure_imp_elim hp).trans (BIFUpdate.mono (forall_elim i))

/-! ### Objective and plain instances -/

@[rocq_alias plainly_objective]
instance plainly_objective (P : MonPred I PROP) : Objective iprop(■ P) where
  objective_at _ _ := .rfl

@[rocq_alias plainly_if_objective]
instance plainly_if_objective (p : Bool) (P : MonPred I PROP) [Objective P] :
    Objective iprop(■?p P) := by
  cases p
  · assumption
  · exact plainly_objective P

@[rocq_alias monPred_at_plain]
instance monPred_at_plain (P : MonPred I PROP) [Plain P] (i : I.car) :
    Plain (P.monPred_at i) where
  plain := calc
    _ ⊢ iprop(■ P).monPred_at i := entails_at.mp Plain.plain i
    _ ⊢ ∀ j, ■ P.monPred_at j   := (monPred_at_plainly i P).mp
    _ ⊢ ■ P.monPred_at i        := forall_elim i

@[rocq_alias monPred_objectively_plain]
instance monPred_objectively_plain (P : MonPred I PROP) [Plain P] :
    Plain iprop(<obj> P) where
  plain := entails_at.mpr fun i => calc
    _ ⊢ ■ ∀ j, P.monPred_at j         := Plain.plain
    _ ⊢ ∀ _, ■ ∀ j, P.monPred_at j    := forall_intro fun _ => .rfl
    _ ⊢ iprop(■ <obj> P).monPred_at i := (monPred_at_plainly i iprop(<obj> P)).mpr

@[rocq_alias monPred_subjectively_plain]
instance monPred_subjectively_plain (P : MonPred I PROP) [Plain P] :
    Plain iprop(<subj> P) where
  plain := entails_at.mpr fun i => calc
    _ ⊢ ■ ∃ j, P.monPred_at j          := Plain.plain
    _ ⊢ ∀ _, ■ ∃ j, P.monPred_at j     := forall_intro fun _ => .rfl
    _ ⊢ iprop(■ <subj> P).monPred_at i := (monPred_at_plainly i iprop(<subj> P)).mpr

end Plainly

/-! ### Step-indexed (SBI) structure on `MonPred` -/

section Sbi
variable {I : BiIndex} {PROP : Type _} [BI PROP] [BIStepIndexed SI PROP] [Sbi SI PROP]
  [SIdxFinite SI]

@[rocq_alias monPred_defs.monPred_si_pure]
instance : SiPure SI (MonPred I PROP) where
  siPure Pi := embed (SiPure.siPure Pi)

#rocq_ignore monPred_defs.monPred_si_pure_def "Rocq unsealed definition body; use SiPure.siPure."
#rocq_ignore monPred_defs.monPred_si_pure_aux "Rocq sealing auxiliary definition."
#rocq_ignore monPred_defs.monPred_si_pure_unseal "Rocq unsealing lemma."
#rocq_ignore monPred_si_pure_unseal "Rocq unsealing lemma."

@[rocq_alias monPred_defs.monPred_si_emp_valid]
instance : SiEmpValid SI (MonPred I PROP) where
  siEmpValid P := SiEmpValid.siEmpValid iprop(∀ i, P.monPred_at i)

#rocq_ignore monPred_defs.monPred_si_emp_valid_def
  "Rocq unsealed definition body; use SiEmpValid.siEmpValid."
#rocq_ignore monPred_defs.monPred_si_emp_valid_aux "Rocq sealing auxiliary definition."
#rocq_ignore monPred_defs.monPred_si_emp_valid_unseal "Rocq unsealing lemma."
#rocq_ignore monPred_si_emp_valid_unseal "Rocq unsealing lemma."

omit [SIdxFinite SI] in
@[rocq_alias monPred_si_pure_unfold]
theorem monPred_siPure_unfold :
    (SiPure.siPure : SiProp SI → MonPred I PROP) =
      fun Pi => iprop(⎡(<si_pure> Pi : PROP)⎤) := rfl

omit [SIdxFinite SI] in
@[rocq_alias monPred_si_emp_valid_unfold]
theorem monPred_siEmpValid_unfold :
    (SiEmpValid.siEmpValid : MonPred I PROP → SiProp SI) =
      fun P => SiEmpValid.siEmpValid iprop(∀ i, P.monPred_at i) := rfl

@[rocq_alias monPred_sbi]
instance instSbiMonPred : Sbi SI (MonPred I PROP) where
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
    refine (monPred_at_forall i (fun q : SiProp SI => iprop(⌜Ψi q⌝ → <si_pure> q))).mp.trans ?_
    exact forall_mono fun q =>
      monPred_impl_force i iprop(⌜Ψi q⌝) (SiPure.siPure q : MonPred I PROP)
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
    have hstep : SiEmpValid.siEmpValid iprop(∀ i, (iprop(P ∗-∗ Q) : MonPred I PROP).monPred_at i)
        ⊢@{SiProp SI} ∀ i, P.monPred_at i ≡[SI] Q.monPred_at i :=
      siEmpValid_forall.mp.trans <| forall_mono fun i =>
        (siEmpValid_mono (hforce i)).trans (BI.prop_ext_siEmpValid_mpr _ _)
    refine hstep.trans ?_
    refine (BI.discreteFun_equivI (PROP := SiProp SI) P.monPred_at Q.monPred_at).mpr.trans ?_
    refine (BI.sig_equivI (PROP := SiProp SI) _ (toSig (SI := SI) P) (toSig (SI := SI) Q)).mp.trans ?_
    exact BI.internalEq.of_internalEquiv_ne (PROP := SiProp SI) (ofSig (SI := SI))

#rocq_ignore monPred_sbi_mixin "Rocq mixin record; subsumed by the Sbi instance."
#rocq_ignore monPred_sbi_prop_ext_mixin "Rocq mixin record; subsumed by the Sbi instance."

/-! ### Internal equality and the plainly modality on `MonPred` -/

@[rocq_alias monPred_internal_eq_unfold]
theorem monPred_internal_eq_unfold {A : Type _} [OFE SI A] :
    (internalEq (SI := SI) : A → A → MonPred I PROP) =
      fun x y => iprop(⎡(x ≡[SI] y : PROP)⎤) := rfl

@[rocq_alias monPred_at_internal_eq]
theorem monPred_at_internal_eq {A : Type _} [OFE SI A] (i : I.car) (a b : A) :
    (iprop(a ≡[SI] b) : MonPred I PROP).monPred_at i ⊣⊢ a ≡[SI] b :=
  .rfl

instance [BIPlainly PROP] [BIPlainlySbi SI PROP] : BIPlainlySbi SI (MonPred I PROP) where
  plainly_siPure_siEmpValid {P} := by
    refine ⟨entails_at.mpr fun _ => ?_, entails_at.mpr fun _ => ?_⟩
    · change iprop(∀ j, ■ (P.monPred_at j)) ⊢
        <si_pure> (SiEmpValid.siEmpValid (SI := SI) iprop(∀ j, P.monPred_at j))
      exact (forall_mono fun _ => BIPlainlySbi.plainly_siPure_siEmpValid.mp).trans <|
        siPure_forall.mpr.trans (siPure_mono siEmpValid_forall.mpr)
    · change iprop(<si_pure> (SiEmpValid.siEmpValid (SI := SI) iprop(∀ j, P.monPred_at j))) ⊢
        ∀ j, ■ (P.monPred_at j)
      exact (siPure_mono siEmpValid_forall.mp).trans <| siPure_forall.mp.trans <|
        forall_mono fun _ => BIPlainlySbi.plainly_siPure_siEmpValid.mpr

omit [Sbi SI PROP] [SIdxFinite SI] in
@[rocq_alias monPred_equivI]
theorem monPred_equivI {PROP' : Type _} [BI PROP'] [BIStepIndexed SI PROP'] [Sbi SI PROP']
    (P Q : MonPred I PROP) :
    (P ≡[SI] Q : PROP') ⊣⊢ iprop(∀ i, P.monPred_at i ≡[SI] Q.monPred_at i) := by
  refine ⟨?_, ?_⟩
  · refine forall_intro fun i => ?_
    letI _ := monPred_at_ne (SI := SI) (PROP := PROP) i
    exact BI.internalEq.of_internalEquiv_ne (PROP := PROP')
      (fun R : MonPred I PROP => R.monPred_at i)
  · refine (BI.discreteFun_equivI (PROP := PROP') P.monPred_at Q.monPred_at).mpr.trans ?_
    refine (BI.sig_equivI (PROP := PROP') _ (toSig (SI := SI) P) (toSig (SI := SI) Q)).mp.trans ?_
    exact BI.internalEq.of_internalEquiv_ne (PROP := PROP') (ofSig (SI := SI))

/-! ### Objective and plain instances -/

@[rocq_alias si_pure_objective]
instance siPure_objective (Pi : SiProp SI) : Objective (iprop(<si_pure> Pi) : MonPred I PROP) where
  objective_at _ _ := .rfl

@[rocq_alias internal_eq_objective]
instance internal_eq_objective {A : Type _} [OFE SI A] (x y : A) :
    Objective (iprop(x ≡[SI] y) : MonPred I PROP) where
  objective_at _ _ := .rfl

/-! ### `SbiEmpValidExist` for `MonPred` -/

omit [SIdxFinite SI] in
@[rocq_alias monPred_sbi_emp_valid_exist]
theorem monPred_sbi_emp_valid_exist {bot : I.car} [BiIndexBottom I bot] [SbiEmpValidExist SI PROP] :
    SbiEmpValidExist SI (MonPred I PROP) where
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
instance monPred_bi_embed_sbi : BiEmbedSbi SI PROP (MonPred I PROP) where
  embed_siEmpValid _P :=
    ⟨siEmpValid_mono (forall_elim (default : I.car)),
     siEmpValid_mono (forall_intro fun _ => .rfl)⟩
  embed_siPure_1 _ := .rfl

@[rocq_alias monPred_bi_bupd_sbi]
instance monPred_bi_bupd_sbi [BIUpdate PROP] [BIBUpdateSbi SI PROP] :
    BIBUpdateSbi SI (MonPred I PROP) where
  bupd_siPure Pi := entails_at.mpr fun _ => BIBUpdateSbi.bupd_siPure Pi

@[rocq_alias monPred_bi_fupd_sbi]
instance monPred_bi_fupd_sbi [BIFUpdate PROP] [BIFUpdateSbi SI PROP] :
    BIFUpdateSbi SI (MonPred I PROP) where
  fupd_keep_siPure E' Pi R := entails_at.mpr fun i => by
    refine (and_mono_right
      (monPred_wand_force i (SiPure.siPure Pi) iprop(|={_}=> R))).trans ?_
    exact BIFUpdateSbi.fupd_keep_siPure E' Pi (R.monPred_at i)
  fupd_siPure_later E P := entails_at.mpr fun i => BIFUpdateSbi.fupd_siPure_later E P
  fupd_siPure_sForall_2 E Φ := entails_at.mpr fun i => by
    refine .trans ?_ (BIFUpdateSbi.fupd_siPure_sForall_2 (PROP := PROP) E Φ)
    refine (monPred_at_forall i
      (fun q : SiProp SI => iprop(⌜Φ q⌝ → |={E}=> <si_pure> q))).mp.trans ?_
    exact forall_mono fun q =>
      monPred_impl_force i iprop(⌜Φ q⌝) iprop(|={E}=> <si_pure> q)

end Sbi

end MonPred

end Iris.BI
