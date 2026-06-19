/-
Copyright (c) 2026 Haokun Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haokun Li
-/
module

public import Iris.BI.BI
public import Iris.BI.BIBase
public import Iris.BI.DerivedLaws
public import Iris.Algebra.OFE
public import Iris.Std.Classes

@[expose] public section

/-
Port of `iris.bi.monpred`: monotone predicates over a `BiIndex` (the "monPred" /
Kripke construction of a BI from a base BI). Signatures are 1:1 with Coq
`monpred.v`; fully proven (0 sorry). The OFE/COFE structure, connective
monotonicity, the `monPred_at_*` unfold lemmas, and the `BI` mixin are discharged
via the `entails_at`/`equiv_at`/`dist_at` helpers (each `Iff.rfl`, the iris-lean
analog of Coq `split=> i`).

iris-lean specifics (vs Coq):
- The base BI `PROP` uses iris-lean's `BIBase`/`BI` classes.
- `BI extends COFE`, so a `COFE (MonPred I PROP)` instance is required; provided
  pointwise (fully proven).
- iris-lean uses predicate-style `sForall`/`sExists : (PROP → Prop) → PROP` rather
  than Coq's index-family `∀ x, Φ x`; the MonPred lifting collects the per-index
  projections of the witnesses (mirrors the UPred / Classical instances).
- There is no `BiEmbed` typeclass in this iris-lean snapshot, so `⎡·⎤` is provided
  as a plain `def MonPred.embed` (not a class instance).
-/

namespace Iris.BI
open Iris Iris.Std OFE

/-- A `BiIndex` is an inhabited type equipped with a preorder `⊑`. Monotone
predicates are functions out of a `BiIndex` that are monotone w.r.t. this order. -/
@[rocq_alias biIndex]
structure BiIndex where
  /-- The carrier type of indices. -/
  car : Type _
  /-- The index type is inhabited (Coq `bi_index_inhabited`). -/
  [inhabited : Inhabited car]
  /-- The order on indices (Coq `bi_index_rel`). -/
  rel : car → car → Prop
  /-- The order is a preorder (Coq `bi_index_rel_preorder`). -/
  [preorder : Std.Preorder rel]

attribute [instance] BiIndex.inhabited BiIndex.preorder

instance : CoeSort BiIndex (Type _) := ⟨BiIndex.car⟩

/-- Notation for the `BiIndex` order, written `i ⊑ j` in Coq. -/
scoped infix:40 " ⊑ᵢ " => BiIndex.rel _

/-- A monotone predicate over `BiIndex` `I` valued in the base BI `PROP`: a function
`monPred_at : I → PROP` monotone w.r.t. the index order. -/
@[rocq_alias monPred]
structure MonPred (I : BiIndex) (PROP : Type _) [BIBase PROP] where
  /-- The underlying index-indexed family (Coq `monPred_at`). -/
  monPred_at : I.car → PROP
  /-- Monotonicity in the index (Coq `monPred_mono`: `Proper ((⊑) ==> (⊢))`). -/
  monPred_mono : ∀ {i j : I.car}, I.rel i j → (monPred_at i ⊢ monPred_at j)

namespace MonPred

variable {I : BiIndex} {PROP : Type _} [BIBase PROP]

/-- Extensionality for `MonPred`: two monotone predicates are equal when their
`monPred_at` projections agree (proof-irrelevant on `monPred_mono`).
Lean addition (not in Coq): Coq has no `=` on `monPred`; the analog is the `⊣⊢`
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
  fun i => iprop(∀ j, ⌜I.rel i j⌝ → Φ j)

end MonPred

section OFE
variable {I : BiIndex} {PROP : Type _} [BI PROP]

/-- Pointwise OFE: `P ≡ Q := ∀ i, P i ≡ Q i`, `P ≡{n}≡ Q := ∀ i, P i ≡{n}≡ Q i`
(Coq `monPredO`). -/
@[rocq_alias monPredO]
noncomputable instance : OFE (MonPred I PROP) where
  Equiv P Q := ∀ i, P.monPred_at i ≡ Q.monPred_at i
  Dist n P Q := ∀ i, P.monPred_at i ≡{n}≡ Q.monPred_at i
  dist_eqv :=
    { refl _ _ := dist_eqv.refl _
      symm h i := dist_eqv.symm (h i)
      trans h1 h2 i := dist_eqv.trans (h1 i) (h2 i) }
  equiv_dist {_ _} := by simp only [equiv_dist]; exact forall_comm
  dist_lt h1 h2 i := dist_lt (h1 i) h2

/-- Project a `MonPred` to its underlying `I.car → PROP` family as an OFE morphism;
non-expansive because `Dist` on `MonPred` is definitionally pointwise. Used to take
the COFE limit index-wise. Deviation: Coq `monPred_sig` projects into the subtype
`{ f | Proper … }`; here it is a plain morphism. -/
@[rocq_alias monPred_sig]
def atHom : MonPred I PROP -n> (I.car → PROP) where
  f P := P.monPred_at
  ne.1 _ _ _ h := h

/-- Pointwise COFE on monotone predicates (Coq `monPred_cofe`): limit taken
index-wise in the base BI. -/
@[rocq_alias monPred_cofe]
noncomputable instance : IsCOFE (MonPred I PROP) where
  compl c :=
    { monPred_at := fun i => COFE.compl (c.map atHom) i
      monPred_mono := fun {i j} h =>
        LimitPreserving.entails (applyHom i) (applyHom j) (c.map atHom)
          (fun n => (c n).monPred_mono h) }
  conv_compl {n c} := IsCOFE.conv_compl (c := c.map atHom) (n := n)

end OFE

namespace MonPred
variable {I : BiIndex} {PROP : Type _}

-- The connectives that don't use the Kripke closure only need `BIBase PROP`, but
-- `impl`/`wand`/`upclosed` need a full `BI PROP` (for the `∀`/`⌜·⌝` BI ops). We
-- phrase the whole `BIBase (MonPred I PROP)` instance under `[BI PROP]`, matching
-- Coq (where the base is always a `bi`).
variable [BI PROP]

/-- Entailment of monotone predicates: pointwise base entailment. -/
@[rocq_alias monPred_defs.monPred_entails]
def Entails (P Q : MonPred I PROP) : Prop := ∀ i, P.monPred_at i ⊢ Q.monPred_at i

/-- Unit of separation, pointwise. -/
@[rocq_alias monPred_defs.monPred_emp_def]
def emp : MonPred I PROP where
  monPred_at _ := iprop(emp)
  monPred_mono _ := .rfl

/-- Pure embedding, index-independent. -/
@[rocq_alias monPred_defs.monPred_pure_def]
def pure (φ : Prop) : MonPred I PROP where
  monPred_at _ := iprop(⌜φ⌝)
  monPred_mono _ := .rfl

/-- Conjunction, pointwise. -/
@[rocq_alias monPred_defs.monPred_and_def]
def and (P Q : MonPred I PROP) : MonPred I PROP where
  monPred_at i := iprop(P.monPred_at i ∧ Q.monPred_at i)
  monPred_mono h := and_mono (P.monPred_mono h) (Q.monPred_mono h)

/-- Disjunction, pointwise. -/
@[rocq_alias monPred_defs.monPred_or_def]
def or (P Q : MonPred I PROP) : MonPred I PROP where
  monPred_at i := iprop(P.monPred_at i ∨ Q.monPred_at i)
  monPred_mono h := or_mono (P.monPred_mono h) (Q.monPred_mono h)

/-- Implication (Kripke): up-closed so the result stays monotone. -/
@[rocq_alias monPred_defs.monPred_impl_def]
def imp (P Q : MonPred I PROP) : MonPred I PROP where
  monPred_at := MonPred.upclosed (fun i => iprop(P.monPred_at i → Q.monPred_at i))
  monPred_mono h :=
    forall_intro fun k => (forall_elim k).trans
      (imp_mono_left (pure_mono fun hjk => Transitive.trans h hjk))

/-- Universal quantification over `PROP`-valued predicates, lifted pointwise. For
iris-lean's predicate-form `sForall (Ψ : MonPred I PROP → Prop)`, the index `i`
projection ranges over the `monPred_at i` of all witnesses of `Ψ`. -/
@[rocq_alias monPred_defs.monPred_forall_def]
def sForall (Ψ : MonPred I PROP → Prop) : MonPred I PROP where
  monPred_at i := BIBase.sForall (fun p => ∃ q : MonPred I PROP, Ψ q ∧ q.monPred_at i = p)
  monPred_mono h :=
    sForall_intro fun _p ⟨q, hq, hp⟩ => (sForall_elim ⟨q, hq, rfl⟩).trans (hp ▸ q.monPred_mono h)

/-- Existential quantification over `PROP`-valued predicates, lifted pointwise. -/
@[rocq_alias monPred_defs.monPred_exist_def]
def sExists (Ψ : MonPred I PROP → Prop) : MonPred I PROP where
  monPred_at i := BIBase.sExists (fun p => ∃ q : MonPred I PROP, Ψ q ∧ q.monPred_at i = p)
  monPred_mono h :=
    sExists_elim fun _p ⟨q, hq, hp⟩ => (hp ▸ q.monPred_mono h).trans (sExists_intro ⟨q, hq, rfl⟩)

/- Lean addition (not in Coq): predicate-form collection bridge.

iris-lean lifts `sForall`/`sExists` over the predicate-style witness collection
`atColl Ψ i := fun p => ∃ q, Ψ q ∧ q.monPred_at i = p` (the per-index projections
of all witnesses of `Ψ`). Coq's index-family `monPred` does not have this re-indexing
plumbing; in the predicate-style port it recurs across `sForall_ne`/`sExists_ne`, the
`sForall`/`sExists` intro/elim mixin fields, the `persistently`/`later` exist/forall
mixin fields, and the `monPred_at_forall`/`monPred_at_exist` unfold lemmas. The
following intro/elim/liftRel bridges factor it out once. -/

/-- The witness collection underlying `MonPred.sForall`/`MonPred.sExists` at index `i`:
the set of `monPred_at i` projections of the witnesses of `Ψ`. -/
def atColl (Ψ : MonPred I PROP → Prop) (i : I.car) : PROP → Prop :=
  fun p => ∃ q : MonPred I PROP, Ψ q ∧ q.monPred_at i = p

/-- A witness `q` of `Ψ` lands in the collection at `q.monPred_at i`. -/
theorem atColl_mem {Ψ : MonPred I PROP → Prop} {q : MonPred I PROP} (hq : Ψ q) (i : I.car) :
    atColl Ψ i (q.monPred_at i) := ⟨q, hq, rfl⟩

/-- Elim bridge for `MonPred.sForall`: instantiate at any witness `q` of `Ψ`. -/
theorem sForall_at_elim {Ψ : MonPred I PROP → Prop} {q : MonPred I PROP} (i : I.car) (hq : Ψ q) :
    (MonPred.sForall Ψ).monPred_at i ⊢ q.monPred_at i :=
  sForall_elim (atColl_mem hq i)

/-- Intro bridge for `MonPred.sForall`: prove `R ⊢ (sForall Ψ).at i` witness-wise. -/
theorem sForall_at_intro {Ψ : MonPred I PROP → Prop} {R : PROP} (i : I.car)
    (h : ∀ q, Ψ q → R ⊢ q.monPred_at i) : R ⊢ (MonPred.sForall Ψ).monPred_at i :=
  sForall_intro fun _ ⟨q, hq, hp⟩ => hp ▸ h q hq

/-- Intro bridge for `MonPred.sExists`: a witness `q` of `Ψ` injects into the existential. -/
theorem sExists_at_intro {Ψ : MonPred I PROP → Prop} {q : MonPred I PROP} (i : I.car) (hq : Ψ q) :
    q.monPred_at i ⊢ (MonPred.sExists Ψ).monPred_at i :=
  sExists_intro (atColl_mem hq i)

/-- Elim bridge for `MonPred.sExists`: prove `(sExists Ψ).at i ⊢ R` witness-wise. -/
theorem sExists_at_elim {Ψ : MonPred I PROP → Prop} {R : PROP} (i : I.car)
    (h : ∀ q, Ψ q → q.monPred_at i ⊢ R) : (MonPred.sExists Ψ).monPred_at i ⊢ R :=
  sExists_elim fun _ ⟨q, hq, hp⟩ => hp ▸ h q hq

/-- `liftRel` transport bridge: a `liftRel R` between `Ψ₁`/`Ψ₂` (on `MonPred`, with `R`
relating witnesses index-wise) lifts to `liftRel R'` between the two collections at `i`,
where `R'` relates the projected `PROP` points. Used by `sForall_ne`/`sExists_ne`. -/
theorem atColl_liftRel {R' : PROP → PROP → Prop} {Ψ₁ Ψ₂ : MonPred I PROP → Prop} (i : I.car)
    (h₁ : ∀ q, Ψ₁ q → ∃ q', Ψ₂ q' ∧ R' (q.monPred_at i) (q'.monPred_at i))
    (h₂ : ∀ q, Ψ₂ q → ∃ q', Ψ₁ q' ∧ R' (q'.monPred_at i) (q.monPred_at i)) :
    liftRel R' (atColl Ψ₁ i) (atColl Ψ₂ i) :=
  ⟨fun _ ⟨q, hq, hp⟩ => let ⟨q', hq', hr⟩ := h₁ q hq; ⟨_, ⟨q', hq', rfl⟩, hp ▸ hr⟩,
   fun _ ⟨q, hq, hp⟩ => let ⟨q', hq', hr⟩ := h₂ q hq; ⟨_, ⟨q', hq', rfl⟩, hp ▸ hr⟩⟩

/-- Separating conjunction, pointwise. -/
@[rocq_alias monPred_defs.monPred_sep_def]
def sep (P Q : MonPred I PROP) : MonPred I PROP where
  monPred_at i := iprop(P.monPred_at i ∗ Q.monPred_at i)
  monPred_mono h := sep_mono (P.monPred_mono h) (Q.monPred_mono h)

/-- Separating implication (Kripke): up-closed. -/
@[rocq_alias monPred_defs.monPred_wand_def]
def wand (P Q : MonPred I PROP) : MonPred I PROP where
  monPred_at := MonPred.upclosed (fun i => iprop(P.monPred_at i -∗ Q.monPred_at i))
  monPred_mono h :=
    forall_intro fun k => (forall_elim k).trans
      (imp_mono_left (pure_mono fun hjk => Transitive.trans h hjk))

/-- Persistency modality, pointwise. -/
@[rocq_alias monPred_defs.monPred_persistently_def]
def persistently (P : MonPred I PROP) : MonPred I PROP where
  monPred_at i := iprop(<pers> (P.monPred_at i))
  monPred_mono h := persistently_mono (P.monPred_mono h)

/-- Later modality, pointwise. -/
@[rocq_alias monPred_defs.monPred_later_def]
def later (P : MonPred I PROP) : MonPred I PROP where
  monPred_at i := iprop(▷ (P.monPred_at i))
  monPred_mono h := later_mono (P.monPred_mono h)

/-- `monPred_in j` holds at index `i` iff `j ⊑ i`. The canonical "I am at least at
index `j`" assertion. -/
@[rocq_alias monPred_defs.monPred_in_def]
def monPred_in (j : I.car) : MonPred I PROP where
  monPred_at i := iprop(⌜I.rel j i⌝)
  monPred_mono h := pure_mono fun hji => Transitive.trans hji h

/-- Embedding of a base proposition as an index-independent monotone predicate (Coq
`monPred_embed` / `⎡·⎤`). No `BiEmbed` class in this snapshot, so a plain def. -/
@[rocq_alias monPred_defs.monPred_embed_def]
def embed (P : PROP) : MonPred I PROP where
  monPred_at _ := P
  monPred_mono _ := .rfl

/-- The "objectively" modality: `<obj> P` forces `P` at *every* index, so the result
is index-independent. -/
@[rocq_alias monPred_defs.monPred_objectively_def]
def objectively (P : MonPred I PROP) : MonPred I PROP where
  monPred_at _ := iprop(∀ i, P.monPred_at i)
  monPred_mono _ := .rfl

/-- The "subjectively" modality: `<subj> P` holds if `P` holds at *some* index; the
result is index-independent. -/
@[rocq_alias monPred_defs.monPred_subjectively_def]
def subjectively (P : MonPred I PROP) : MonPred I PROP where
  monPred_at _ := iprop(∃ i, P.monPred_at i)
  monPred_mono _ := .rfl

end MonPred

section Instances
variable {I : BiIndex} {PROP : Type _} [BI PROP]

instance : BIBase (MonPred I PROP) where
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

/-- MonPred entailment is *definitionally* pointwise base entailment. This `Iff.rfl`
helper exposes that for BI-mixin proofs — the iris-lean analog of Coq `split=> i`. -/
@[rocq_alias monPred_at_entails]
theorem entails_at {P Q : MonPred I PROP} :
    (P ⊢ Q) ↔ ∀ i, P.monPred_at i ⊢ Q.monPred_at i := Iff.rfl

/-- MonPred OFE equivalence is *definitionally* pointwise. -/
@[rocq_alias monPred_at_equiv]
theorem equiv_at {P Q : MonPred I PROP} :
    (P ≡ Q) ↔ ∀ i, P.monPred_at i ≡ Q.monPred_at i := Iff.rfl

/-- MonPred OFE distance is *definitionally* pointwise. -/
@[rocq_alias monPred_at_dist]
theorem dist_at {n : Nat} {P Q : MonPred I PROP} :
    (P ≡{n}≡ Q) ↔ ∀ i, P.monPred_at i ≡{n}≡ Q.monPred_at i := Iff.rfl

/-- BI mixin on monotone predicates (Coq `monPred_bi_mixin` + persistently/later
mixins, packaged into `monPredI : bi`). Fully proven via `entails_at`/`equiv_at`/
`dist_at`. -/
@[rocq_alias monPredI]
noncomputable instance : BI (MonPred I PROP) where
  entails_preorder :=
    { refl := entails_at.mpr fun _ => BIBase.Entails.rfl
      trans := fun h h' => entails_at.mpr fun i => (entails_at.mp h i).trans (entails_at.mp h' i) }
  equiv_iff := fun {P Q} =>
    ⟨fun h => ⟨entails_at.mpr fun i => (equiv_iff.mp (equiv_at.mp h i)).mp,
              entails_at.mpr fun i => (equiv_iff.mp (equiv_at.mp h i)).mpr⟩,
     fun h => equiv_at.mpr fun i => equiv_iff.mpr ⟨entails_at.mp h.1 i, entails_at.mp h.2 i⟩⟩
  and_ne := ⟨fun _ _ _ h _ _ h' => dist_at.mpr fun i => and_ne.ne (dist_at.mp h i) (dist_at.mp h' i)⟩
  or_ne := ⟨fun _ _ _ h _ _ h' => dist_at.mpr fun i => or_ne.ne (dist_at.mp h i) (dist_at.mp h' i)⟩
  imp_ne := ⟨fun _ _ _ h _ _ h' => dist_at.mpr fun i =>
    forall_ne fun j => imp_ne.ne Dist.rfl (imp_ne.ne (dist_at.mp h j) (dist_at.mp h' j))⟩
  sForall_ne := fun {n Ψ₁ Ψ₂} h => dist_at.mpr fun i =>
    Iris.BI.sForall_ne <| MonPred.atColl_liftRel i
      (fun q hq => let ⟨q', hq', hqq'⟩ := h.1 q hq; ⟨q', hq', dist_at.mp hqq' i⟩)
      (fun q hq => let ⟨q', hq', hqq'⟩ := h.2 q hq; ⟨q', hq', dist_at.mp hqq' i⟩)
  sExists_ne := fun {n Ψ₁ Ψ₂} h => dist_at.mpr fun i =>
    Iris.BI.sExists_ne <| MonPred.atColl_liftRel i
      (fun q hq => let ⟨q', hq', hqq'⟩ := h.1 q hq; ⟨q', hq', dist_at.mp hqq' i⟩)
      (fun q hq => let ⟨q', hq', hqq'⟩ := h.2 q hq; ⟨q', hq', dist_at.mp hqq' i⟩)
  sep_ne := ⟨fun _ _ _ h _ _ h' => dist_at.mpr fun i => sep_ne.ne (dist_at.mp h i) (dist_at.mp h' i)⟩
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
    forall_intro fun j => imp_intro <| pure_elim_right fun (hij : I.rel i j) =>
      (P.monPred_mono hij).trans <| imp_intro (entails_at.mp h j)
  imp_elim {P Q R} h := entails_at.mpr fun i =>
    imp_elim <| (entails_at.mp h i).trans <|
      (forall_elim i).trans <| pure_imp_elim (Reflexive.refl : I.rel i i)
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
    refine pure_elim_right fun (hij : I.rel i j) => ?_
    refine wand_intro (sep_symm.trans ?_)
    exact (sep_mono_right (P.monPred_mono hij)).trans (sep_symm.trans (entails_at.mp h j))
  wand_elim {P Q R} h := entails_at.mpr fun i =>
    (sep_mono_left ((entails_at.mp h i).trans
      ((forall_elim i).trans (pure_imp_elim (Reflexive.refl : I.rel i i))))).trans wand_elim_left
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
    exact (pure_imp_elim (Reflexive.refl : I.rel i i)).trans (pure_imp_elim hΦ)
  later_sExists_false := fun {Φ} => entails_at.mpr fun i => by
    refine later_sExists_false.trans (or_mono BIBase.Entails.rfl ?_)
    refine exists_elim fun p => pure_elim_left fun ⟨q, hΦ, hq⟩ => ?_
    subst hq
    exact (and_intro (pure_intro hΦ) BIBase.Entails.rfl).trans
      (MonPred.sExists_at_intro (q := iprop(⌜Φ q⌝ ∧ ▷ q)) i ⟨q, rfl⟩)
  later_sep := ⟨entails_at.mpr fun i => later_sep.mp, entails_at.mpr fun i => later_sep.mpr⟩
  later_persistently := ⟨entails_at.mpr fun i => later_persistently.mp, entails_at.mpr fun i => later_persistently.mpr⟩
  later_false_em {P} := entails_at.mpr fun i => by
    refine later_false_em.trans (or_mono_right ?_)
    refine forall_intro fun j => imp_intro ?_
    refine pure_elim_right fun (hij : I.rel i j) => ?_
    exact imp_mono BIBase.Entails.rfl (P.monPred_mono hij)

end Instances

/-- A monotone predicate `P` is *objective* if its value does not depend on the
index: `P i ⊢ P j` for all `i j`. Equivalently `P ⊣⊢ <obj> P`. -/
@[rocq_alias Objective]
class Objective {I : BiIndex} {PROP : Type _} [BI PROP] (P : MonPred I PROP) : Prop where
  objective_at : ∀ i j : I.car, P.monPred_at i ⊢ P.monPred_at j

namespace MonPred
variable {I : BiIndex} {PROP : Type _} [BI PROP]

-- `monPred_at_*` unfold lemmas (signatures 1:1 with Coq; fully proven, `of_eq rfl`).

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
      iprop(∀ j, ⌜I.rel i j⌝ → (P.monPred_at j → Q.monPred_at j)) :=
  BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_forall]
theorem monPred_at_forall {α : Sort _} (i : I.car) (Φ : α → MonPred I PROP) :
    (iprop(∀ x, Φ x)).monPred_at i ⊣⊢ iprop(∀ x, (Φ x).monPred_at i) :=
  ⟨forall_intro fun x => MonPred.sForall_at_elim i ⟨x, rfl⟩,
   MonPred.sForall_at_intro i fun _ ⟨x, hx⟩ => hx ▸ forall_elim x⟩

@[rocq_alias monPred_at_exist]
theorem monPred_at_exist {α : Sort _} (i : I.car) (Φ : α → MonPred I PROP) :
    (iprop(∃ x, Φ x)).monPred_at i ⊣⊢ iprop(∃ x, (Φ x).monPred_at i) :=
  ⟨MonPred.sExists_at_elim i fun _ ⟨x, hx⟩ => hx ▸ exists_intro (Ψ := fun y => (Φ y).monPred_at i) x,
   exists_elim fun x => MonPred.sExists_at_intro i ⟨x, rfl⟩⟩

@[rocq_alias monPred_at_sep]
theorem monPred_at_sep (i : I.car) (P Q : MonPred I PROP) :
    (iprop(P ∗ Q)).monPred_at i ⊣⊢ iprop(P.monPred_at i ∗ Q.monPred_at i) :=
  BIBase.BiEntails.of_eq rfl

@[rocq_alias monPred_at_wand]
theorem monPred_at_wand (i : I.car) (P Q : MonPred I PROP) :
    (iprop(P -∗ Q)).monPred_at i ⊣⊢
      iprop(∀ j, ⌜I.rel i j⌝ → (P.monPred_at j -∗ Q.monPred_at j)) :=
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
    (MonPred.monPred_in j : MonPred I PROP).monPred_at i ⊣⊢ iprop(⌜I.rel j i⌝) :=
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

end MonPred

end Iris.BI
