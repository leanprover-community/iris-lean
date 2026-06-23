/-
Copyright (c) 2026 Haokun Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haokun Li
-/
module

public import Iris.BI.BI
public import Iris.BI.BIBase
public import Iris.BI.DerivedLaws
public import Iris.BI.DerivedLawsLater
public import Iris.BI.Classes
public import Iris.BI.Notation
public import Iris.BI.Updates
public import Iris.BI.Plainly
public import Iris.BI.Sbi
public import Iris.BI.InternalEq
public import Iris.BI.BigOp
public import Iris.Algebra.OFE
public import Iris.Algebra.Monoid

@[expose] public section

namespace Iris.BI
open Iris Iris.Std OFE Iris.Algebra Iris.Algebra.BigOpL Iris.Algebra.BigOpM

/-! ## The `Embed` operation `⎡·⎤` -/

/-- The embedding operation `⎡·⎤ : A → B` (Coq `Embed`). `B` is intentionally *not*
an `outParam`: the target logic is fixed by the expected type, not chosen by the
instance (Coq hint mode `! -`). -/
@[rocq_alias Embed]
class Embed (A B : Type _) where
  embed : A → B
export Embed (embed)

syntax "⎡" term "⎤" : term
macro_rules | `(iprop(⎡$P⎤)) => ``(Embed.embed iprop($P))

delab_rule Embed.embed
  | `($_ $P) => ``(iprop(⎡$P⎤))

/-! ## The `BiEmbed` class -/

variable {PROP1 PROP2 : Type _} [BI PROP1] [BI PROP2]

/-- The image under `⎡·⎤` of a base predicate `Ψ : PROP1 → Prop`, as a predicate on
`PROP2`. The predicate-form analogue of Coq's index family `Φ : A → PROP1`; used to
state the `sForall`/`sExists` embedding laws without quantifying over the index type
`A` inside a structure field (cf. MonPred `atColl`). -/
def embedColl [Embed PROP1 PROP2] (Ψ : PROP1 → Prop) : PROP2 → Prop :=
  fun q => ∃ p, Ψ p ∧ q = embed p

omit [BI PROP1] [BI PROP2] in
/-- A witness `p` of `Ψ` lands in `embedColl Ψ` at `⎡p⎤` (Lean addition). -/
theorem embedColl_mem [Embed PROP1 PROP2] {Ψ : PROP1 → Prop} {p : PROP1} (hp : Ψ p) :
    embedColl Ψ (embed p : PROP2) := ⟨p, hp, rfl⟩

/-- The laws an embedding `⎡·⎤ : PROP1 → PROP2` must satisfy (Coq `BiEmbedMixin`). The
`forall_2`/`exist_1` fields use the predicate-form (`embedColl`) rather than Coq's
index family, to stay universe-monomorphic as a structure field. -/
@[rocq_alias BiEmbedMixin]
structure BiEmbedMixin (PROP1 PROP2 : Type _) [BI PROP1] [BI PROP2]
    [Embed PROP1 PROP2] where
  ne            : OFE.NonExpansive (embed (A := PROP1) (B := PROP2))
  mono          : ∀ {P Q : PROP1}, (P ⊢ Q) → ((⎡P⎤ : PROP2) ⊢ ⎡Q⎤)
  emp_valid_inj : ∀ (P : PROP1), (⊢ (⎡P⎤ : PROP2)) → (⊢ P)
  emp_2         : (emp : PROP2) ⊢ ⎡(emp : PROP1)⎤
  impl_2        : ∀ (P Q : PROP1), iprop(⎡P⎤ → ⎡Q⎤) ⊢ (⎡iprop(P → Q)⎤ : PROP2)
  forall_2      : ∀ (Ψ : PROP1 → Prop), iprop(BIBase.sForall (embedColl Ψ)) ⊢ (⎡BIBase.sForall Ψ⎤ : PROP2)
  exist_1       : ∀ (Ψ : PROP1 → Prop), (⎡BIBase.sExists Ψ⎤ : PROP2) ⊢ iprop(BIBase.sExists (embedColl Ψ))
  sep           : ∀ (P Q : PROP1), (⎡iprop(P ∗ Q)⎤ : PROP2) ⊣⊢ ⎡P⎤ ∗ ⎡Q⎤
  wand_2        : ∀ (P Q : PROP1), iprop(⎡P⎤ -∗ ⎡Q⎤) ⊢ (⎡iprop(P -∗ Q)⎤ : PROP2)
  persistently  : ∀ (P : PROP1), (⎡iprop(<pers> P)⎤ : PROP2) ⊣⊢ <pers> ⎡P⎤

/-- An embedding `⎡·⎤ : PROP1 → PROP2` satisfying `BiEmbedMixin` (Coq `BiEmbed`). -/
@[rocq_alias BiEmbed]
class BiEmbed (PROP1 PROP2 : Type _) [BI PROP1] [BI PROP2] extends Embed PROP1 PROP2 where
  embed_mixin : BiEmbedMixin PROP1 PROP2

/-- `⎡emp⎤ ⊣⊢ emp` (Coq `BiEmbedEmp`). -/
@[rocq_alias BiEmbedEmp]
class BiEmbedEmp (PROP1 PROP2 : Type _) [BI PROP1] [BI PROP2] [BiEmbed PROP1 PROP2] where
  embed_emp_1 : (⎡(emp : PROP1)⎤ : PROP2) ⊢ emp

/-- `⎡▷ P⎤ ⊣⊢ ▷ ⎡P⎤` (Coq `BiEmbedLater`). -/
@[rocq_alias BiEmbedLater]
class BiEmbedLater (PROP1 PROP2 : Type _) [BI PROP1] [BI PROP2] [BiEmbed PROP1 PROP2] where
  embed_later : ∀ (P : PROP1), (⎡iprop(▷ P)⎤ : PROP2) ⊣⊢ ▷ ⎡P⎤

/-- `⎡|==> P⎤ ⊣⊢ |==> ⎡P⎤` (Coq `BiEmbedBUpd`). -/
@[rocq_alias BiEmbedBUpd]
class BiEmbedBUpd (PROP1 PROP2 : Type _) [BI PROP1] [BI PROP2] [BiEmbed PROP1 PROP2]
    [BIUpdate PROP1] [BIUpdate PROP2] where
  embed_bupd : ∀ (P : PROP1), (⎡iprop(|==> P)⎤ : PROP2) ⊣⊢ |==> ⎡P⎤

/-- `⎡|={E1,E2}=> P⎤ ⊣⊢ |={E1,E2}=> ⎡P⎤` (Coq `BiEmbedFUpd`). -/
@[rocq_alias BiEmbedFUpd]
class BiEmbedFUpd (PROP1 PROP2 : Type _) [BI PROP1] [BI PROP2] [BiEmbed PROP1 PROP2]
    [BIFUpdate PROP1] [BIFUpdate PROP2] where
  embed_fupd : ∀ (E1 E2 : CoPset) (P : PROP1), (⎡iprop(|={E1,E2}=> P)⎤ : PROP2) ⊣⊢ |={E1,E2}=> ⎡P⎤

/-- The `Sbi` (internal-equality / plainly) embedding laws (Coq `BiEmbedSbi`). -/
@[rocq_alias BiEmbedSbi]
class BiEmbedSbi (PROP1 PROP2 : Type _) [BI PROP1] [BI PROP2] [BiEmbed PROP1 PROP2]
    [Sbi PROP1] [Sbi PROP2] where
  embed_si_emp_valid : ∀ (P : PROP1),
    SiEmpValid.siEmpValid (embed P : PROP2) ⊣⊢ SiEmpValid.siEmpValid P
  embed_si_pure_1 : ∀ (Pi : SiProp),
    (embed (SiPure.siPure Pi : PROP1) : PROP2) ⊢ (SiPure.siPure Pi : PROP2)

/-! ## Projections of the mixin (Coq `Section embed_laws`) -/

section
variable [BiEmbed PROP1 PROP2]

/-- `⎡·⎤` is non-expansive. -/
@[rocq_alias embed_ne]
theorem embed_ne : OFE.NonExpansive (embed (A := PROP1) (B := PROP2)) := BiEmbed.embed_mixin.ne

/-- `⎡·⎤` is monotone. -/
@[rocq_alias embed_mono]
theorem embed_mono {P Q : PROP1} (h : P ⊢ Q) : (⎡P⎤ : PROP2) ⊢ ⎡Q⎤ := BiEmbed.embed_mixin.mono h

/-- `⎡·⎤` respects `⊣⊢`. The iris-lean stand-in for Coq's `embed_proper` /
`embed_flip_mono` setoid `Proper` instances (which iris-lean does not use). -/
theorem embed_congr {P Q : PROP1} (h : P ⊣⊢ Q) : (⎡P⎤ : PROP2) ⊣⊢ ⎡Q⎤ :=
  ⟨embed_mono h.mp, embed_mono h.mpr⟩

#rocq_ignore embed_proper "iris-lean has no setoid `Proper` instances; `embed_congr` is the `≡`-respecting lemma."
#rocq_ignore embed_flip_mono "iris-lean has no setoid `Proper` instances; covered by `embed_mono`."

@[rocq_alias embed_emp_valid_inj]
theorem embed_emp_valid_inj {P : PROP1} (h : ⊢ (⎡P⎤ : PROP2)) : ⊢ P :=
  BiEmbed.embed_mixin.emp_valid_inj P h

@[rocq_alias embed_emp_2]
theorem embed_emp_2 : (emp : PROP2) ⊢ ⎡(emp : PROP1)⎤ := BiEmbed.embed_mixin.emp_2

@[rocq_alias embed_impl_2]
theorem embed_impl_2 (P Q : PROP1) : iprop(⎡P⎤ → ⎡Q⎤) ⊢ (⎡iprop(P → Q)⎤ : PROP2) :=
  BiEmbed.embed_mixin.impl_2 P Q

/-- Coq `embed_forall_2`, in predicate form (`embedColl`). -/
@[rocq_alias embed_forall_2]
theorem embed_sForall_2 (Ψ : PROP1 → Prop) :
    iprop(BIBase.sForall (embedColl Ψ)) ⊢ (⎡BIBase.sForall Ψ⎤ : PROP2) :=
  BiEmbed.embed_mixin.forall_2 Ψ

/-- Coq `embed_exist_1`, in predicate form (`embedColl`). -/
@[rocq_alias embed_exist_1]
theorem embed_sExists_1 (Ψ : PROP1 → Prop) :
    (⎡BIBase.sExists Ψ⎤ : PROP2) ⊢ iprop(BIBase.sExists (embedColl Ψ)) :=
  BiEmbed.embed_mixin.exist_1 Ψ

@[rocq_alias embed_sep]
theorem embed_sep (P Q : PROP1) : (⎡iprop(P ∗ Q)⎤ : PROP2) ⊣⊢ ⎡P⎤ ∗ ⎡Q⎤ :=
  BiEmbed.embed_mixin.sep P Q

@[rocq_alias embed_wand_2]
theorem embed_wand_2 (P Q : PROP1) : iprop(⎡P⎤ -∗ ⎡Q⎤) ⊢ (⎡iprop(P -∗ Q)⎤ : PROP2) :=
  BiEmbed.embed_mixin.wand_2 P Q

@[rocq_alias embed_persistently]
theorem embed_persistently (P : PROP1) : (⎡iprop(<pers> P)⎤ : PROP2) ⊣⊢ <pers> ⎡P⎤ :=
  BiEmbed.embed_mixin.persistently P

/-! ## Derived laws (Coq `Section embed`) -/

/-- `⎡sForall Ψ⎤` entails the embedding of any member `⎡p⎤` (forward bridge). -/
theorem embed_sForall_elim {Ψ : PROP1 → Prop} {p : PROP1} (hp : Ψ p) :
    (⎡BIBase.sForall Ψ⎤ : PROP2) ⊢ ⎡p⎤ := embed_mono (sForall_elim hp)

/-- Witness-wise introduction for `⎡sForall Ψ⎤` (backward bridge, uses `forall_2`). -/
theorem embed_sForall_intro {Ψ : PROP1 → Prop} {R : PROP2}
    (h : ∀ p, Ψ p → R ⊢ ⎡p⎤) : R ⊢ (⎡BIBase.sForall Ψ⎤ : PROP2) :=
  (sForall_intro fun _ ⟨p, hp, hq⟩ => hq ▸ h p hp).trans (embed_sForall_2 Ψ)

/-- Witness `⎡p⎤` injects into `⎡sExists Ψ⎤` (backward bridge). -/
theorem embed_sExists_intro {Ψ : PROP1 → Prop} {p : PROP1} (hp : Ψ p) :
    (⎡p⎤ : PROP2) ⊢ ⎡BIBase.sExists Ψ⎤ := embed_mono (sExists_intro hp)

/-- Witness-wise elimination for `⎡sExists Ψ⎤` (forward bridge, uses `exist_1`). -/
theorem embed_sExists_elim {Ψ : PROP1 → Prop} {R : PROP2}
    (h : ∀ p, Ψ p → (⎡p⎤ : PROP2) ⊢ R) : (⎡BIBase.sExists Ψ⎤ : PROP2) ⊢ R :=
  (embed_sExists_1 Ψ).trans (sExists_elim fun _ ⟨p, hp, hq⟩ => hq ▸ h p hp)

@[rocq_alias embed_forall]
theorem embed_forall {A : Sort _} (Φ : A → PROP1) : (⎡∀ x, Φ x⎤ : PROP2) ⊣⊢ ∀ x, ⎡Φ x⎤ :=
  ⟨forall_intro fun x => embed_sForall_elim ⟨x, rfl⟩,
   embed_sForall_intro fun _ ⟨x, hx⟩ => hx ▸ forall_elim x⟩

@[rocq_alias embed_exist]
theorem embed_exist {A : Sort _} (Φ : A → PROP1) : (⎡∃ x, Φ x⎤ : PROP2) ⊣⊢ ∃ x, ⎡Φ x⎤ :=
  ⟨embed_sExists_elim fun _ ⟨x, hx⟩ => hx ▸ exists_intro (Ψ := fun y => (embed (Φ y) : PROP2)) x,
   exists_elim fun x => embed_sExists_intro ⟨x, rfl⟩⟩

@[rocq_alias embed_and]
theorem embed_and (P Q : PROP1) : (⎡iprop(P ∧ Q)⎤ : PROP2) ⊣⊢ ⎡P⎤ ∧ ⎡Q⎤ :=
  (embed_congr and_forall_ite).trans <| (embed_forall _).trans <|
    (forall_congr fun b => by cases b <;> exact .rfl).trans and_forall_ite.symm

@[rocq_alias embed_or]
theorem embed_or (P Q : PROP1) : (⎡iprop(P ∨ Q)⎤ : PROP2) ⊣⊢ ⎡P⎤ ∨ ⎡Q⎤ :=
  (embed_congr or_exists_ite).trans <| (embed_exist _).trans <|
    (exists_congr fun b => by cases b <;> exact .rfl).trans or_exists_ite.symm

@[rocq_alias embed_impl]
theorem embed_impl (P Q : PROP1) : (⎡iprop(P → Q)⎤ : PROP2) ⊣⊢ iprop(⎡P⎤ → ⎡Q⎤) :=
  ⟨imp_intro ((embed_and (iprop(P → Q)) P).mpr.trans (embed_mono (imp_elim .rfl))),
   embed_impl_2 P Q⟩

@[rocq_alias embed_wand]
theorem embed_wand (P Q : PROP1) : (⎡iprop(P -∗ Q)⎤ : PROP2) ⊣⊢ iprop(⎡P⎤ -∗ ⎡Q⎤) :=
  ⟨wand_intro ((embed_sep (iprop(P -∗ Q)) P).mpr.trans (embed_mono wand_elim_left)),
   embed_wand_2 P Q⟩

@[rocq_alias embed_emp_valid]
theorem embed_emp_valid (P : PROP1) : (⊢ (⎡P⎤ : PROP2)) ↔ (⊢ P) :=
  ⟨fun h => embed_emp_valid_inj h, fun h => embed_emp_2.trans (embed_mono h)⟩

/-- `⎡·⎤` reflects entailment (Coq's `Inj (⊢) (⊢) embed`; iris-lean has no `Inj`
class, so this is a plain lemma). -/
@[rocq_alias embed_entails_inj]
theorem embed_entails_inj {P Q : PROP1} (h : (⎡P⎤ : PROP2) ⊢ ⎡Q⎤) : P ⊢ Q :=
  wand_entails (embed_emp_valid_inj ((entails_wand h).trans (embed_wand_2 P Q)))

/-- `⎡·⎤` reflects equivalence (Coq's `Inj (≡) (≡) embed`; plain lemma). -/
@[rocq_alias embed_inj]
theorem embed_inj {P Q : PROP1} (h : (embed P : PROP2) ≡ embed Q) : P ≡ Q :=
  BI.equiv_iff.mpr ⟨embed_entails_inj (BI.equiv_iff.mp h).mp,
                    embed_entails_inj (BI.equiv_iff.mp h).mpr⟩

@[rocq_alias embed_emp]
theorem embed_emp [BiEmbedEmp PROP1 PROP2] : (⎡(emp : PROP1)⎤ : PROP2) ⊣⊢ emp :=
  ⟨BiEmbedEmp.embed_emp_1, embed_emp_2⟩

/-- `⌜φ⌝ ⊣⊢ ∃ _ : φ, True` (Coq `bi.pure_alt`; absent in iris-lean, proved here). -/
private theorem pure_alt {PROP : Type _} [BI PROP] (φ : Prop) :
    (⌜φ⌝ : PROP) ⊣⊢ ∃ _ : φ, True :=
  (pure_congr ⟨fun h => ⟨h, trivial⟩, fun ⟨h, _⟩ => h⟩).trans pure_exists.symm

/-- `⎡True⎤ ⊣⊢ True` (Lean helper for `embed_pure` / the unit of the `and` homomorphism). -/
private theorem embed_pure_True : (⎡(True : PROP1)⎤ : PROP2) ⊣⊢ True :=
  ⟨true_intro,
   (imp_intro and_elim_r).trans <| (embed_impl_2 emp emp).trans (embed_mono true_intro)⟩

@[rocq_alias embed_pure]
theorem embed_pure (φ : Prop) : (⎡(⌜φ⌝ : PROP1)⎤ : PROP2) ⊣⊢ ⌜φ⌝ :=
  (embed_congr (pure_alt φ)).trans <| (embed_exist _).trans <|
    (exists_congr fun _ => embed_pure_True).trans (pure_alt φ).symm

@[rocq_alias embed_iff]
theorem embed_iff (P Q : PROP1) : (⎡iprop(P ↔ Q)⎤ : PROP2) ⊣⊢ iprop(⎡P⎤ ↔ ⎡Q⎤) :=
  (embed_and _ _).trans (and_congr (embed_impl P Q) (embed_impl Q P))

@[rocq_alias embed_wand_iff]
theorem embed_wand_iff (P Q : PROP1) : (⎡iprop(P ∗-∗ Q)⎤ : PROP2) ⊣⊢ iprop(⎡P⎤ ∗-∗ ⎡Q⎤) :=
  (embed_and _ _).trans (and_congr (embed_wand P Q) (embed_wand Q P))

/-! ### Affinely / absorbingly / intuitionistically (Coq `Section embed`) -/

@[rocq_alias embed_affinely_2]
theorem embed_affinely_2 (P : PROP1) : iprop(<affine> ⎡P⎤) ⊢ (⎡iprop(<affine> P)⎤ : PROP2) :=
  (and_intro (and_elim_l.trans embed_emp_2) and_elim_r).trans (embed_and emp P).mpr

@[rocq_alias embed_affinely]
theorem embed_affinely [BiEmbedEmp PROP1 PROP2] (P : PROP1) :
    (⎡iprop(<affine> P)⎤ : PROP2) ⊣⊢ iprop(<affine> ⎡P⎤) :=
  (embed_and emp P).trans (and_congr embed_emp .rfl)

@[rocq_alias embed_absorbingly]
theorem embed_absorbingly (P : PROP1) :
    (⎡iprop(<absorb> P)⎤ : PROP2) ⊣⊢ iprop(<absorb> ⎡P⎤) :=
  (embed_sep _ P).trans (sep_congr embed_pure_True .rfl)

@[rocq_alias embed_intuitionistically_2]
theorem embed_intuitionistically_2 (P : PROP1) : iprop(□ ⎡P⎤) ⊢ (⎡iprop(□ P)⎤ : PROP2) :=
  (affinely_mono (embed_persistently P).mpr).trans (embed_affinely_2 _)

@[rocq_alias embed_intuitionistically]
theorem embed_intuitionistically [BiEmbedEmp PROP1 PROP2] (P : PROP1) :
    (⎡iprop(□ P)⎤ : PROP2) ⊣⊢ iprop(□ ⎡P⎤) :=
  (embed_affinely _).trans (affinely_congr (embed_persistently P))

@[rocq_alias embed_persistently_if]
theorem embed_persistently_if (P : PROP1) (b : Bool) :
    (⎡iprop(<pers>?b P)⎤ : PROP2) ⊣⊢ iprop(<pers>?b ⎡P⎤) := by cases b <;> first | exact .rfl | exact embed_persistently P

@[rocq_alias embed_affinely_if_2]
theorem embed_affinely_if_2 (P : PROP1) (b : Bool) :
    iprop(<affine>?b ⎡P⎤) ⊢ (⎡iprop(<affine>?b P)⎤ : PROP2) := by cases b <;> first | exact .rfl | exact embed_affinely_2 P

@[rocq_alias embed_affinely_if]
theorem embed_affinely_if [BiEmbedEmp PROP1 PROP2] (P : PROP1) (b : Bool) :
    (⎡iprop(<affine>?b P)⎤ : PROP2) ⊣⊢ iprop(<affine>?b ⎡P⎤) := by cases b <;> first | exact .rfl | exact embed_affinely P

@[rocq_alias embed_absorbingly_if]
theorem embed_absorbingly_if (b : Bool) (P : PROP1) :
    (⎡iprop(<absorb>?b P)⎤ : PROP2) ⊣⊢ iprop(<absorb>?b ⎡P⎤) := by cases b <;> first | exact .rfl | exact embed_absorbingly P

@[rocq_alias embed_intuitionistically_if_2]
theorem embed_intuitionistically_if_2 (P : PROP1) (b : Bool) :
    iprop(□?b ⎡P⎤) ⊢ (⎡iprop(□?b P)⎤ : PROP2) := by cases b <;> first | exact .rfl | exact embed_intuitionistically_2 P

@[rocq_alias embed_intuitionistically_if]
theorem embed_intuitionistically_if [BiEmbedEmp PROP1 PROP2] (P : PROP1) (b : Bool) :
    (⎡iprop(□?b P)⎤ : PROP2) ⊣⊢ iprop(□?b ⎡P⎤) := by cases b <;> first | exact .rfl | exact embed_intuitionistically P

/-! ### Persistence / affinity / absorbing (instances) -/

@[rocq_alias embed_persistent]
instance embed_persistent (P : PROP1) [Persistent P] : Persistent (embed P : PROP2) where
  persistent := (embed_mono persistent).trans (embed_persistently P).mp

@[rocq_alias embed_affine]
instance embed_affine [BiEmbedEmp PROP1 PROP2] (P : PROP1) [Affine P] : Affine (embed P : PROP2) where
  affine := (embed_mono affine).trans embed_emp.mp

@[rocq_alias embed_absorbing]
instance embed_absorbing (P : PROP1) [Absorbing P] : Absorbing (embed P : PROP2) where
  absorbing := (embed_absorbingly P).mpr.trans (embed_mono absorbing)

/-! ### Later (Coq `Section later`, needs `BiEmbedLater`) -/

@[rocq_alias embed_laterN]
theorem embed_laterN [BiEmbedLater PROP1 PROP2] (n : Nat) (P : PROP1) :
    (⎡iprop(▷^[n] P)⎤ : PROP2) ⊣⊢ iprop(▷^[n] ⎡P⎤) := by
  induction n with
  | zero => exact .rfl
  | succ n ih => exact (BiEmbedLater.embed_later _).trans (later_congr ih)

@[rocq_alias embed_except_0]
theorem embed_except_0 [BiEmbedLater PROP1 PROP2] (P : PROP1) :
    (⎡iprop(◇ P)⎤ : PROP2) ⊣⊢ iprop(◇ ⎡P⎤) :=
  (embed_or _ P).trans
    (or_congr ((BiEmbedLater.embed_later _).trans (later_congr (embed_pure False))) .rfl)

@[rocq_alias embed_timeless]
instance embed_timeless [BiEmbedLater PROP1 PROP2] (P : PROP1) [Timeless P] :
    Timeless (embed P : PROP2) where
  timeless :=
    ((BiEmbedLater.embed_later P).mpr.trans (embed_mono Timeless.timeless)).trans
      (embed_except_0 P).mp

/-! ### Monoid homomorphisms (Coq `Section embed` instances) -/

/-- Cross-type `MonoidHomomorphism` for `⎡·⎤` w.r.t. OFE equivalence (mirrors
`MonoidHomomorphism.ofEquiv`, which is single-type). -/
@[reducible] private def monHomCT {op₁ : PROP1 → PROP1 → PROP1} {op₂ : PROP2 → PROP2 → PROP2}
    {u₁ : PROP1} {u₂ : PROP2} [MonoidOps op₁ u₁] [MonoidOps op₂ u₂]
    (hop : ∀ {x y}, (embed (op₁ x y) : PROP2) ≡ op₂ (embed x) (embed y))
    (hunit : (embed u₁ : PROP2) ≡ u₂) :
    MonoidHomomorphism op₁ op₂ u₁ u₂ (· ≡ ·) (embed (A := PROP1) (B := PROP2)) where
  rel_refl := .rfl
  rel_trans := .trans
  rel_proper ha hb := ⟨fun h => ha.symm.trans (h.trans hb), fun h => ha.trans (h.trans hb.symm)⟩
  op_proper ha hb := MonoidOps.op_proper ha hb
  map_ne := embed_ne
  map_op := hop
  map_unit := hunit

@[rocq_alias embed_and_homomorphism]
instance embed_and_homomorphism :
    MonoidHomomorphism (and (PROP := PROP1)) (and (PROP := PROP2)) iprop(True) iprop(True)
      (· ≡ ·) (embed (A := PROP1) (B := PROP2)) :=
  monHomCT (fun {x y} => equiv_iff.mpr (embed_and x y)) (equiv_iff.mpr embed_pure_True)

@[rocq_alias embed_or_homomorphism]
instance embed_or_homomorphism :
    MonoidHomomorphism (or (PROP := PROP1)) (or (PROP := PROP2)) iprop(False) iprop(False)
      (· ≡ ·) (embed (A := PROP1) (B := PROP2)) :=
  monHomCT (fun {x y} => equiv_iff.mpr (embed_or x y)) (equiv_iff.mpr (embed_pure False))

@[rocq_alias embed_sep_entails_homomorphism]
instance embed_sep_entails_homomorphism :
    MonoidHomomorphism (sep (PROP := PROP1)) (sep (PROP := PROP2)) emp emp
      (flip Entails) (embed (A := PROP1) (B := PROP2)) where
  rel_refl := .rfl
  rel_trans := flip .trans
  rel_proper H G := ⟨fun J => (equiv_iff.1 G).mpr.trans (J.trans (equiv_iff.1 H).mp),
                     fun J => (equiv_iff.1 G).mp.trans (J.trans (equiv_iff.1 H).mpr)⟩
  op_proper := sep_mono
  map_ne := embed_ne
  map_op := fun {x y} => (embed_sep x y).mpr
  map_unit := embed_emp_2

@[rocq_alias embed_sep_homomorphism]
instance embed_sep_homomorphism [BiEmbedEmp PROP1 PROP2] :
    MonoidHomomorphism (sep (PROP := PROP1)) (sep (PROP := PROP2)) emp emp
      (· ≡ ·) (embed (A := PROP1) (B := PROP2)) :=
  monHomCT (fun {x y} => equiv_iff.mpr (embed_sep x y)) (equiv_iff.mpr embed_emp)

/-! ### Big separating conjunction (Coq `Section big_ops` / `big_ops_emp`)

Each is one application of the corresponding `big_op*_commute` to the `sep` monoid
homomorphism, mirroring Coq. `embed_big_sepMS` (gmultiset) is omitted entirely —
gmultiset big-ops are not yet ported in iris-lean. -/

@[rocq_alias embed_big_sepL_2]
theorem embed_big_sepL_2 {A : Type _} (Φ : Nat → A → PROP1) (l : List A) :
    ([∗list] k ↦ x ∈ l, (⎡Φ k x⎤ : PROP2)) ⊢ ⎡[∗list] k ↦ x ∈ l, Φ k x⎤ :=
  bigOpL_hom (H := embed_sep_entails_homomorphism) Φ l

@[rocq_alias embed_big_sepL]
theorem embed_big_sepL [BiEmbedEmp PROP1 PROP2] {A : Type _} (Φ : Nat → A → PROP1) (l : List A) :
    (⎡[∗list] k ↦ x ∈ l, Φ k x⎤ : PROP2) ⊣⊢ [∗list] k ↦ x ∈ l, ⎡Φ k x⎤ :=
  equiv_iff.mp (bigOpL_hom (H := embed_sep_homomorphism) Φ l)

variable {K V : Type _} {M : Type _ → Type _} [LawfulFiniteMap M K]

@[rocq_alias embed_big_sepM_2]
theorem embed_big_sepM_2 (Φ : K → V → PROP1) (m : M V) :
    ([∗map] k ↦ x ∈ m, (⎡Φ k x⎤ : PROP2)) ⊢ ⎡[∗map] k ↦ x ∈ m, Φ k x⎤ :=
  bigOpM_hom (ι := embed_sep_entails_homomorphism) Φ m

@[rocq_alias embed_big_sepM]
theorem embed_big_sepM [BiEmbedEmp PROP1 PROP2] (Φ : K → V → PROP1) (m : M V) :
    (⎡[∗map] k ↦ x ∈ m, Φ k x⎤ : PROP2) ⊣⊢ [∗map] k ↦ x ∈ m, ⎡Φ k x⎤ :=
  equiv_iff.mp (bigOpM_hom (ι := embed_sep_homomorphism) Φ m)

@[rocq_alias embed_big_sepS_2]
theorem embed_big_sepS_2 {S A : Type _} [LawfulFiniteSet S A] (Φ : A → PROP1) (X : S) :
    ([∗set] x ∈ X, (⎡Φ x⎤ : PROP2)) ⊢ ⎡[∗set] x ∈ X, Φ x⎤ :=
  Iris.Algebra.BigOpS.hom embed_sep_entails_homomorphism Φ X

@[rocq_alias embed_big_sepS]
theorem embed_big_sepS [BiEmbedEmp PROP1 PROP2] {S A : Type _} [LawfulFiniteSet S A]
    (Φ : A → PROP1) (X : S) :
    (⎡[∗set] x ∈ X, Φ x⎤ : PROP2) ⊣⊢ [∗set] x ∈ X, ⎡Φ x⎤ :=
  equiv_iff.mp (Iris.Algebra.BigOpS.hom embed_sep_homomorphism Φ X)

#rocq_ignore embed_big_sepMS "gmultiset big-ops are not yet ported in iris-lean (no BigSepMSet)."
#rocq_ignore embed_big_sepMS_2 "gmultiset big-ops are not yet ported in iris-lean (no BigSepMSet)."

end

/-! ## Internal equality & plainly (Coq `Section sbi`)

`si_pure` / `internal_eq` / `internal_inj` / `plainly` / `plainly_if` / `plain`. For an
`Sbi`, `■ P` is by definition `<si_pure> <si_emp_valid> P` (instance `instPlainlySbi`),
so the `plainly` laws reduce to `embed_si_pure` + `embed_si_emp_valid`. Uses fresh
`P1`/`P2`/`P3` so each `BI` instance comes solely from `Sbi` (no diamond with `[BI _]`). -/
section
variable {P1 P2 : Type _} [Sbi P1] [Sbi P2] [BiEmbed P1 P2] [BiEmbedSbi P1 P2]

@[rocq_alias embed_si_pure]
theorem embed_si_pure (Pi : SiProp) :
    (embed (SiPure.siPure Pi : P1) : P2) ⊣⊢ SiPure.siPure Pi :=
  ⟨BiEmbedSbi.embed_si_pure_1 Pi,
   (siPure_mono ((BiEmbedSbi.embed_si_emp_valid _).trans siEmpValid_siPure).mpr).trans
     siPure_siEmpValid_elim⟩

@[rocq_alias embed_internal_eq]
theorem embed_internal_eq {A : Type _} [OFE A] (x y : A) :
    (embed (internalEq x y : P1) : P2) ⊣⊢ internalEq x y :=
  embed_si_pure (SiProp.internalEq x y)

@[rocq_alias embed_plainly]
theorem embed_plainly (P : P1) : (⎡iprop(■ P)⎤ : P2) ⊣⊢ iprop(■ ⎡P⎤) := by
  show (embed (SiPure.siPure (SiEmpValid.siEmpValid P)) : P2)
      ⊣⊢ SiPure.siPure (SiEmpValid.siEmpValid (embed P))
  exact (embed_si_pure _).trans
    ⟨siPure_mono (BiEmbedSbi.embed_si_emp_valid P).mpr,
     siPure_mono (BiEmbedSbi.embed_si_emp_valid P).mp⟩

@[rocq_alias embed_plainly_if]
theorem embed_plainly_if (p : Bool) (P : P1) :
    (⎡iprop(■? p P)⎤ : P2) ⊣⊢ iprop(■? p ⎡P⎤) := by cases p <;> first | exact .rfl | exact embed_plainly P

/-- `⎡·⎤` preserves `Plain` (Coq `embed_plain`). Coq registers this via a `Hint Extern`
rather than a plain `Instance` (its `class_apply` would shelve the `BiEmbedSbi` premise);
Lean's instance resolver has no such shelving, so a direct `instance` is safe here. -/
@[rocq_alias embed_plain]
instance embed_plain (P : P1) [Plain P] : Plain (embed P : P2) where
  plain := (embed_mono Plain.plain).trans (embed_plainly P).mp

/-- `⎡·⎤` reflects internal equality (Coq `embed_internal_inj`). -/
@[rocq_alias embed_internal_inj]
theorem embed_internal_inj {P3 : Type _} [Sbi P3] (P Q : P1) :
    (internalEq (embed P : P2) (embed Q) : P3) ⊢ internalEq P Q := by
  have comp : ∀ (X Y : P1),
      iprop(<si_emp_valid> ((embed X : P2) -∗ embed Y)) ⊣⊢@{SiProp} iprop(<si_emp_valid> (X -∗ Y)) :=
    fun X Y =>
      (show iprop(<si_emp_valid> ((embed X : P2) -∗ embed Y)) ⊣⊢@{SiProp}
            iprop(<si_emp_valid> (embed (iprop(X -∗ Y)) : P2)) from
        ⟨siEmpValid_mono (embed_wand X Y).symm.mp, siEmpValid_mono (embed_wand X Y).symm.mpr⟩).trans
      (BiEmbedSbi.embed_si_emp_valid (iprop(X -∗ Y)))
  refine siPure_mono ?_
  refine (prop_ext_siEmpValid_equiv (embed P) (embed Q)).mp.trans ?_
  refine (siEmpValid_and.mp.trans ?_).trans (prop_ext_siEmpValid_equiv P Q).mpr
  exact (and_mono (comp P Q).mp (comp Q P).mp).trans siEmpValid_and.mpr

end

/-! ## Transitive embedding (Coq `Section embed_embed`)

Two embeddings `PA → PB → PC` compose to an embedding `PA → PC`. In Coq these are
`Local Instance`s; here `embedEmbed` is a plain `def` (a global instance would loop). -/
section
variable {PA PC : Type _} [BI PA] [BI PC]

/-- The composed embedding `⎡⎡·⎤⎤ : PA → PC` (Coq `embed_embed`). The intermediate
`PB` is an explicit parameter (it is not determined by `Embed PA PC`, so this cannot
be a global instance — Coq makes it a `Local Instance`). -/
@[reducible, rocq_alias embed_embed]
def embedEmbed (PB : Type _) [BI PB] [BiEmbed PA PB] [BiEmbed PB PC] : Embed PA PC :=
  ⟨fun P => embed (embed P : PB)⟩

@[rocq_alias embed_embed_alt]
theorem embed_embed_alt (PB : Type _) [BI PB] [BiEmbed PA PB] [BiEmbed PB PC] (P : PA) :
    (embedEmbed PB).embed P ⊣⊢ (embed (embed P : PB) : PC) := .rfl

variable (PB : Type _) [BI PB] [BiEmbed PA PB] [BiEmbed PB PC]

/-- The composed embedding satisfies `BiEmbedMixin` (Coq `embed_embedding_mixin`). -/
@[rocq_alias embed_embedding_mixin]
def embed_embedding_mixin : @BiEmbedMixin PA PC _ _ (embedEmbed PB) :=
  letI : Embed PA PC := embedEmbed PB
  { ne := (embed_ne (PROP1 := PB) (PROP2 := PC)).comp (embed_ne (PROP1 := PA) (PROP2 := PB))
    mono := fun h => embed_mono (embed_mono h)
    emp_valid_inj := fun _ h => embed_emp_valid_inj (embed_emp_valid_inj h)
    emp_2 := embed_emp_2.trans (embed_mono embed_emp_2)
    impl_2 := fun P Q => (embed_impl_2 (embed P) (embed Q)).trans (embed_mono (embed_impl_2 P Q))
    forall_2 := fun Ψ =>
      (embed_sForall_intro fun _q ⟨p, hp, hq⟩ => hq ▸ sForall_elim ⟨p, hp, rfl⟩).trans
        (embed_mono (embed_sForall_2 Ψ))
    exist_1 := fun Ψ =>
      (embed_mono (embed_sExists_1 Ψ)).trans
        (embed_sExists_elim fun _q ⟨p, hp, hq⟩ => hq ▸ sExists_intro ⟨p, hp, rfl⟩)
    sep := fun P Q => (embed_congr (embed_sep P Q)).trans (embed_sep _ _)
    wand_2 := fun P Q => (embed_wand_2 (embed P) (embed Q)).trans (embed_mono (embed_wand_2 P Q))
    persistently := fun P => (embed_congr (embed_persistently P)).trans (embed_persistently _) }

/-- The composed `BiEmbed PA PC` (Coq `embed_bi_embed`). -/
@[reducible, rocq_alias embed_bi_embed]
def embedBiEmbed : BiEmbed PA PC where
  toEmbed := embedEmbed PB
  embed_mixin := embed_embedding_mixin PB

/-- `BiEmbedEmp` transfers along composition (Coq `embed_embed_emp`). -/
@[reducible, rocq_alias embed_embed_emp]
def embed_embed_emp [BiEmbedEmp PA PB] [BiEmbedEmp PB PC] :
    @BiEmbedEmp PA PC _ _ (embedBiEmbed PB) :=
  letI : BiEmbed PA PC := embedBiEmbed PB
  { embed_emp_1 := (embed_mono (PROP1 := PB) (PROP2 := PC)
      (BiEmbedEmp.embed_emp_1 (PROP1 := PA) (PROP2 := PB))).trans
      (BiEmbedEmp.embed_emp_1 (PROP1 := PB) (PROP2 := PC)) }

/-- `BiEmbedLater` transfers along composition (Coq `embed_embed_later`). -/
@[reducible, rocq_alias embed_embed_later]
def embed_embed_later [BiEmbedLater PA PB] [BiEmbedLater PB PC] :
    @BiEmbedLater PA PC _ _ (embedBiEmbed PB) :=
  letI : BiEmbed PA PC := embedBiEmbed PB
  { embed_later := fun P => (embed_congr (PROP1 := PB) (PROP2 := PC)
      (BiEmbedLater.embed_later (PROP1 := PA) (PROP2 := PB) P)).trans
      (BiEmbedLater.embed_later (PROP1 := PB) (PROP2 := PC) (embed (A := PA) (B := PB) P)) }

/-- `BiEmbedBUpd` transfers along composition (Coq `embed_embed_bupd`). -/
@[reducible, rocq_alias embed_embed_bupd]
def embed_embed_bupd [BIUpdate PA] [BIUpdate PB] [BIUpdate PC]
    [BiEmbedBUpd PA PB] [BiEmbedBUpd PB PC] :
    @BiEmbedBUpd PA PC _ _ (embedBiEmbed PB) _ _ :=
  letI : BiEmbed PA PC := embedBiEmbed PB
  { embed_bupd := fun P => (embed_congr (PROP1 := PB) (PROP2 := PC)
      (BiEmbedBUpd.embed_bupd (PROP1 := PA) (PROP2 := PB) P)).trans
      (BiEmbedBUpd.embed_bupd (PROP1 := PB) (PROP2 := PC) (embed (A := PA) (B := PB) P)) }

/-- `BiEmbedFUpd` transfers along composition (Coq `embed_embed_fupd`). -/
@[reducible, rocq_alias embed_embed_fupd]
def embed_embed_fupd [BIFUpdate PA] [BIFUpdate PB] [BIFUpdate PC]
    [BiEmbedFUpd PA PB] [BiEmbedFUpd PB PC] :
    @BiEmbedFUpd PA PC _ _ (embedBiEmbed PB) _ _ :=
  letI : BiEmbed PA PC := embedBiEmbed PB
  { embed_fupd := fun E1 E2 P => (embed_congr (PROP1 := PB) (PROP2 := PC)
      (BiEmbedFUpd.embed_fupd (PROP1 := PA) (PROP2 := PB) E1 E2 P)).trans
      (BiEmbedFUpd.embed_fupd (PROP1 := PB) (PROP2 := PC) E1 E2 (embed (A := PA) (B := PB) P)) }

end

/- `BiEmbedSbi` transfers along composition (Coq `embed_embed_sbi`). Fresh `Sbi` type
names so each `BI` instance comes from `Sbi` (no diamond with the `[BI _]` above). -/
section
variable {QA QB QC : Type _} [Sbi QA] [Sbi QB] [Sbi QC]
  [BiEmbed QA QB] [BiEmbed QB QC] [BiEmbedSbi QA QB] [BiEmbedSbi QB QC]

@[reducible, rocq_alias embed_embed_sbi]
def embed_embed_sbi : @BiEmbedSbi QA QC _ _ (embedBiEmbed QB) _ _ :=
  letI : BiEmbed QA QC := embedBiEmbed QB
  { embed_si_emp_valid := fun P =>
      (BiEmbedSbi.embed_si_emp_valid (PROP1 := QB) (PROP2 := QC) (embed (A := QA) (B := QB) P)).trans
        (BiEmbedSbi.embed_si_emp_valid (PROP1 := QA) (PROP2 := QB) P)
    embed_si_pure_1 := fun Pi =>
      (embed_mono (PROP1 := QB) (PROP2 := QC)
          (BiEmbedSbi.embed_si_pure_1 (PROP1 := QA) (PROP2 := QB) Pi)).trans
        (BiEmbedSbi.embed_si_pure_1 (PROP1 := QB) (PROP2 := QC) Pi) }

end

end Iris.BI
