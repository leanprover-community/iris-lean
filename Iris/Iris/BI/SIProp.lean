/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.BI.BI
public import Iris.BI.Extensions
public import Iris.BI.Classes
public import Iris.BI.DerivedLaws
public import Iris.Algebra.CMRA

@[expose] public section

/-!
# Step-Indexed Propositions (siProp)

The type `SiProp` defines "plain" step-indexed propositions, on which we define the
usual connectives of higher-order logic and prove that these satisfy the axioms of BI.
-/

namespace Iris
open OFE BI

variable {SI : Type _} [instSI : SIdx SI]
local stepindex SI

/-- Step-indexed proposition, downward closed in the step index. -/
@[rocq_alias siProp]
structure SiProp (SI : Type _) [SIdx SI] where
  holds : SI → Prop
  closed : holds n₁ → n₂ ≤ n₁ → holds n₂

namespace SiProp

/-! ## Connective definitions -/

@[rocq_alias siProp_pure]
def pure (φ : Prop) : SiProp SI where
  holds _ := φ
  closed h _ := h

#rocq_ignore siProp_pure_def "Not needed in Lean."
#rocq_ignore siProp_pure_aux "Not needed in Lean."
#rocq_ignore siProp_pure_unseal "Not needed in Lean."

@[rocq_alias siProp_and]
def and (P Q : SiProp SI) : SiProp SI where
  holds n := P.holds n ∧ Q.holds n
  closed h hle := ⟨P.closed h.1 hle, Q.closed h.2 hle⟩

#rocq_ignore siProp_and_def "Not needed in Lean."
#rocq_ignore siProp_and_aux "Not needed in Lean."
#rocq_ignore siProp_and_unseal "Not needed in Lean."

@[rocq_alias siProp_or]
def or (P Q : SiProp SI) : SiProp SI where
  holds n := P.holds n ∨ Q.holds n
  closed h hle := h.imp (P.closed · hle) (Q.closed · hle)

#rocq_ignore siProp_or_def "Not needed in Lean."
#rocq_ignore siProp_or_aux "Not needed in Lean."
#rocq_ignore siProp_or_unseal "Not needed in Lean."

@[rocq_alias SiProp_downclose]
def downClose (Pi : SI → Prop) : SiProp SI where
  holds n := ∀ n', n' ≤ n → Pi n'
  closed h hle n' hn' := h n' (SIdx.le_trans hn' hle)

@[rocq_alias siProp_impl]
def imp (P Q : SiProp SI) : SiProp SI :=
  downClose fun n => P.holds n → Q.holds n

#rocq_ignore siProp_impl_def "Not needed in Lean."
#rocq_ignore siProp_impl_aux "Not needed in Lean."
#rocq_ignore siProp_impl_unseal "Not needed in Lean."

@[rocq_alias siProp_forall]
def all (Φ : SiProp SI → Prop) : SiProp SI where
  holds n := ∀ P, Φ P → P.holds n
  closed h hle P hP := P.closed (h P hP) hle

#rocq_ignore siProp_forall_def "Not needed in Lean."
#rocq_ignore siProp_forall_aux "Not needed in Lean."
#rocq_ignore siProp_forall_unseal "Not needed in Lean."

@[rocq_alias siProp_exist]
def exist (Φ : SiProp SI → Prop) : SiProp SI where
  holds n := ∃ P, Φ P ∧ P.holds n
  closed := fun ⟨P, hP, hh⟩ hle => ⟨P, hP, P.closed hh hle⟩

#rocq_ignore siProp_exist_def "Not needed in Lean."
#rocq_ignore siProp_exist_aux "Not needed in Lean."
#rocq_ignore siProp_exist_unseal "Not needed in Lean."

/-- `▷ P` holds at `n` if `P` holds at all smaller indices (Transfinite Iris). -/
@[rocq_alias siProp_later]
def later (P : SiProp SI) : SiProp SI where
  holds n := ∀ m, m < n → P.holds m
  closed {_ _} h hle m hm := h m (SIdx.lt_le_trans hm hle)

#rocq_ignore siProp_later_def "Not needed in Lean."
#rocq_ignore siProp_later_aux "Not needed in Lean."
#rocq_ignore siProp_later_unseal "Not needed in Lean."

/-! ## OFE / COFE / BIBase instances -/

@[rocq_alias siProp_entails]
def entails (P Q : SiProp SI) : Prop := ∀ n, P.holds n → Q.holds n

@[rocq_alias siPropO]
instance : OFE (SiProp SI) where
  Dist n P Q := ∀ {m}, m ≤ n → (P.holds m ↔ Q.holds m)
  dist_eqv.refl _ _ _ := Iff.rfl
  dist_eqv.symm h _ hle := (h hle).symm
  dist_eqv.trans h₁ h₂ _ hle := (h₁ hle).trans (h₂ hle)
  eq_dist' {P Q} := by
    refine ⟨?_, fun h => ?_⟩
    · rintro rfl _ _ _; exact Iff.rfl
    · obtain ⟨ph, hp⟩ := P; obtain ⟨qh, _⟩ := Q
      have : ph = qh := funext fun n => propext (h n SIdx.le_refl)
      subst this; rfl
  dist_lt h hlt _ hle := h (SIdx.le_trans hle (SIdx.lt_le_incl hlt))

#rocq_ignore siProp_equiv' "OFE is Leibniz; use equality."
#rocq_ignore siProp_equiv "OFE is Leibniz; use equality."
#rocq_ignore siProp_dist' "Inlined in the `OFE` construction."
#rocq_ignore siProp_dist "Inlined in the `OFE` construction."
#rocq_ignore siProp_ofe_mixin "Not needed in Lean."

/-- The completion of a bounded chain of `SiProp`s (cf. `UPred.bcompl`). -/
def bcompl (n : SI) (c : BChain (SiProp SI) n) : SiProp SI where
  holds k := ∀ m (hm : m < n), m ≤ k → (c.bchain m hm).holds m
  closed h hle m hm hmk := h m hm (SIdx.le_trans hmk hle)

@[rocq_alias siProp_cofe]
instance : IsCOFE (SiProp SI) where
  compl c := {
    holds n := (c n).holds n
    closed {n₁ _} h hle := (c.cauchy hle SIdx.le_refl).mp (c n₁ |>.closed h hle)
  }
  conv_compl {_ c} _ hle := c.cauchy hle SIdx.le_refl |>.symm
  lbcompl {n} _ c := bcompl n c
  conv_lbcompl {n} _ c m hm i him := by
    have hi : i < n := SIdx.le_lt_trans him hm
    refine ⟨fun h => ?_, fun h j hj hji => ?_⟩
    · exact (c.bcauchy hi hm him SIdx.le_refl).mpr (h i hi SIdx.le_refl)
    · exact (c.bcauchy hj hm (SIdx.le_trans hji him) SIdx.le_refl).mp
        ((c.bchain m hm).closed h hji)
  lbcompl_ne {n} _ c1 c2 k hc i hik :=
    ⟨fun h j hj hji => (hc j hj (SIdx.le_trans hji hik)).mp (h j hj hji),
     fun h j hj hji => (hc j hj (SIdx.le_trans hji hik)).mpr (h j hj hji)⟩

#rocq_ignore siProp_compl "Included in IsCOFE instance."

instance : BIBase (SiProp SI) where
  Entails := SiProp.entails
  emp := SiProp.pure True
  pure := SiProp.pure
  and := SiProp.and
  or := SiProp.or
  imp := SiProp.imp
  sForall := SiProp.all
  sExists := SiProp.exist
  sep := SiProp.and
  wand := SiProp.imp
  persistently P := P
  later := SiProp.later

#rocq_ignore siProp_emp "Included in BIBase instance."
#rocq_ignore siProp_sep "Included in BIBase instance."
#rocq_ignore siProp_wand "Included in BIBase instance."
#rocq_ignore siProp_persistently "Included in BIBase instance."

@[rocq_alias siProp_primitive.entails_po]
instance siPropPreorder : Std.IsPreorder (SiProp SI) where
  le_refl _ _ := id
  le_trans _ _ _ h₁ h₂ n h := h₂ n (h₁ n h)

/-! ## BI instance -/

@[rocq_alias siPropI]
instance instBI : BI (SiProp SI) where
  entails_refl := siPropPreorder.le_refl _
  entails_trans := siPropPreorder.le_trans _ _ _
  equiv_iff := OFE.eq_dist.trans
    ⟨fun heq => ⟨fun n hP => (heq n SIdx.le_refl).mp hP, fun n hQ => (heq n SIdx.le_refl).mpr hQ⟩,
     fun H _ _ _ => ⟨H.1 _, H.2 _⟩⟩
  and_ne.ne _ _ _ h₁ _ _ h₂ m h := ⟨.imp (h₁ h).mp (h₂ h).mp, .imp (h₁ h).mpr (h₂ h).mpr⟩
  or_ne.ne _ _ _ h₁ _ _ h₂ m h := ⟨.imp (h₁ h).mp (h₂ h).mp, .imp (h₁ h).mpr (h₂ h).mpr⟩
  imp_ne.ne _ _ _ h₁ _ _ h₂ m hle := {
    mp hpq n' hn' hP :=
      h₂ (SIdx.le_trans hn' hle) |>.mp <| hpq n' hn' <| (h₁ (SIdx.le_trans hn' hle)).mpr hP
    mpr hpq n' hn' hP :=
      h₂ (SIdx.le_trans hn' hle) |>.mpr <| hpq n' hn' <| (h₁ (SIdx.le_trans hn' hle)).mp hP
  }
  sForall_ne {_ _ _} H _ hle := by
    refine ⟨fun h Q hQ => ?_, fun h P hP => ?_⟩
    · obtain ⟨P, hP, hPQ⟩ := H.2 _ hQ
      exact (hPQ hle).mp (h _ hP)
    · obtain ⟨Q, hQ, hPQ⟩ := H.1 P hP
      exact (hPQ hle).mpr (h _ hQ)
  sExists_ne {_ _ _} H m hle := by
    refine ⟨?_, ?_⟩
    · rintro ⟨P, hP, hPm⟩
      obtain ⟨Q, hQ, hPQ⟩ := H.1 P hP
      exact ⟨Q, hQ, (hPQ hle).mp hPm⟩
    · rintro ⟨Q, hQ, hQm⟩
      obtain ⟨P, hP, hPQ⟩ := H.2 Q hQ
      exact ⟨P, hP, (hPQ hle).mpr hQm⟩
  sep_ne.ne _ _ _ h₁ _ _ h₂ m hle := ⟨.imp (h₁ hle).mp (h₂ hle).mp, .imp (h₁ hle).mpr (h₂ hle).mpr⟩
  wand_ne.ne _ _ _ h₁ _ _ h₂ m hle := {
    mp hpq n' hn' hP :=
      h₂ (SIdx.le_trans hn' hle) |>.mp <| hpq n' hn' <| (h₁ (SIdx.le_trans hn' hle)).mpr hP
    mpr hpq n' hn' hP :=
      h₂ (SIdx.le_trans hn' hle) |>.mpr <| hpq n' hn' <| (h₁ (SIdx.le_trans hn' hle)).mp hP
  }
  persistently_ne.ne _ _ _ h m hle := h hle
  later_ne.ne _ _ _ h m hle :=
    ⟨fun hP k hk => (h (SIdx.le_trans (SIdx.lt_le_incl hk) hle)).mp (hP k hk),
     fun hP k hk => (h (SIdx.le_trans (SIdx.lt_le_incl hk) hle)).mpr (hP k hk)⟩
  pure_intro h _ _ := h
  pure_elim' h _ hφ := h hφ _ trivial
  and_elim_l _ h := h.1
  and_elim_r _ h := h.2
  and_intro h₁ h₂ _ h := ⟨h₁ _ h, h₂ _ h⟩
  or_intro_l _ h := .inl h
  or_intro_r _ h := .inr h
  or_elim h₁ h₂ _ h := h.elim (h₁ _) (h₂ _)
  imp_intro {P _ _} h n hP n' hle hQ := h n' ⟨P.closed hP hle, hQ⟩
  imp_elim h n hPQ := h n hPQ.1 n SIdx.le_refl hPQ.2
  sForall_intro h _ hP P hΨ := h P hΨ _ hP
  sForall_elim h _ hF := hF _ h
  sExists_intro h _ hP := ⟨_, h, hP⟩
  sExists_elim h := fun _ ⟨_, hΨ, hP⟩ => h _ hΨ _ hP
  sep_mono h₁ h₂ _ hPQ := ⟨h₁ _ hPQ.1, h₂ _ hPQ.2⟩
  emp_sep := ⟨fun _ hPQ => hPQ.2, fun _ hP => ⟨trivial, hP⟩⟩
  sep_symm _ hPQ := ⟨hPQ.2, hPQ.1⟩
  sep_assoc_l _ hPQR := ⟨hPQR.1.1, hPQR.1.2, hPQR.2⟩
  wand_intro := fun {P _ _} h n hP n' hle hQ => h n' ⟨P.closed hP hle, hQ⟩
  wand_elim h n hPQ := h n hPQ.1 n SIdx.le_refl hPQ.2
  persistently_mono h := h
  persistently_idem_2 _ h := h
  persistently_emp_2 _ h := h
  persistently_and_2 _ h := h
  persistently_absorb_l _ h := h.1
  persistently_and_l _ h := h
  later_mono h _ hlP m hm := h m (hlP m hm)
  later_intro {P} _ hP _ hm := P.closed hP (SIdx.lt_le_incl hm)
  later_sForall_2 _ h m hm P hΦ := h _ ⟨P, rfl⟩ _ SIdx.le_refl hΦ m hm
  later_sExists_false := by
    intro _ Φ n h
    rcases SIdxFinite.finite_index n with rfl | ⟨k, rfl⟩
    · exact .inl fun m hm => absurd hm (SIdx.not_lt_zero m)
    · obtain ⟨P, hΦP, hPk⟩ := h k (SIdx.lt_succ_self k)
      exact .inr ⟨_, ⟨P, rfl⟩, hΦP, fun m hm => P.closed hPk (SIdx.lt_succ_r.mp hm)⟩
  later_sep_1 _ h := ⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2⟩
  later_sep_2 _ h m hm := ⟨h.1 m hm, h.2 m hm⟩
  later_or_1 {P Q} _ h := SIdx.forall_lt_or (fun hle h => P.closed h hle) (fun hle h => Q.closed h hle) h
  later_persistently := ⟨fun _ => id, fun _ => id⟩
  later_false_em {P} n hP := by
    by_cases hn : n = 0
    · subst hn; exact .inl fun m hm => absurd hm (SIdx.not_lt_zero m)
    · refine .inr fun n' hle hF => ?_
      by_cases hn' : n' = 0
      · subst hn'; exact hP 0 (SIdx.neq_0_lt_0.mp hn)
      · exact absurd (hF 0 (SIdx.neq_0_lt_0.mp hn')) id

/-! ## Step-indexed characterisation of the connectives

`BI`'s quantifiers range over *sets* of `SiProp`s, so `∃`/`∀` do not reduce to their
meta-level counterparts by `rfl`; the remaining connectives do. -/

theorem biEntails_of_iff {P Q : SiProp SI} (h : ∀ n, P.holds n ↔ Q.holds n) : P ⊣⊢ Q :=
  ⟨fun n => (h n).mp, fun n => (h n).mpr⟩

@[simp] theorem pure_holds {φ : Prop} {n} : (iprop(⌜φ⌝) : SiProp SI).holds n ↔ φ := .rfl

@[simp] theorem and_holds {P Q : SiProp SI} {n} :
    (iprop(P ∧ Q) : SiProp SI).holds n ↔ P.holds n ∧ Q.holds n := .rfl

@[simp] theorem sep_holds {P Q : SiProp SI} {n} :
    (iprop(P ∗ Q) : SiProp SI).holds n ↔ P.holds n ∧ Q.holds n := .rfl

@[simp] theorem or_holds {P Q : SiProp SI} {n} :
    (iprop(P ∨ Q) : SiProp SI).holds n ↔ P.holds n ∨ Q.holds n := .rfl

@[simp] theorem later_holds {P : SiProp SI} {n} :
    (iprop(▷ P) : SiProp SI).holds n ↔ ∀ m, m < n → P.holds m := .rfl

@[simp] theorem exists_holds {α : Sort _} {Φ : α → SiProp SI} {n} :
    (iprop(∃ x, Φ x) : SiProp SI).holds n ↔ ∃ x, (Φ x).holds n :=
  ⟨fun ⟨_, ⟨x, rfl⟩, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨Φ x, ⟨x, rfl⟩, h⟩⟩

@[simp] theorem forall_holds {α : Sort _} {Φ : α → SiProp SI} {n} :
    (iprop(∀ x, Φ x) : SiProp SI).holds n ↔ ∀ x, (Φ x).holds n := by
  refine ⟨fun h x => h (Φ x) ⟨x, rfl⟩, fun h P hP => ?_⟩
  obtain ⟨x, rfl⟩ := hP
  exact h x

@[rocq_alias siProp_primitive.pure_ne]
theorem pure_dist_of_iff {Φ Ψ : Prop} (H : Φ ↔ Ψ) : pure Φ ≡{n}≡ pure Ψ := fun _ => iff_comm.mp H.symm

/-! The primitive laws of `siProp` are the fields of the `siPropI` instance above; each one
is named in Lean by the corresponding `BI` field, so the Rocq names alias those. -/

attribute [rocq_alias siProp_primitive.equiv_entails,
           rocq_alias siProp_primitive.entails_anti_symm] BI.equiv_iff

attribute [rocq_alias siProp_primitive.pure_intro] BI.pure_intro
attribute [rocq_alias siProp_primitive.pure_elim'] BI.pure_elim'

attribute [rocq_alias siProp_primitive.and_ne] BI.and_ne
attribute [rocq_alias siProp_primitive.and_elim_l] BI.and_elim_l
attribute [rocq_alias siProp_primitive.and_elim_r] BI.and_elim_r
attribute [rocq_alias siProp_primitive.and_intro] BI.and_intro

attribute [rocq_alias siProp_primitive.or_ne] BI.or_ne
attribute [rocq_alias siProp_primitive.or_intro_l] BI.or_intro_l
attribute [rocq_alias siProp_primitive.or_intro_r] BI.or_intro_r
attribute [rocq_alias siProp_primitive.or_elim] BI.or_elim

attribute [rocq_alias siProp_primitive.impl_ne] BI.imp_ne
attribute [rocq_alias siProp_primitive.impl_intro_r] BI.imp_intro
attribute [rocq_alias siProp_primitive.impl_elim_l'] BI.imp_elim

attribute [rocq_alias siProp_primitive.forall_ne] BI.sForall_ne
attribute [rocq_alias siProp_primitive.forall_intro] BI.sForall_intro
attribute [rocq_alias siProp_primitive.forall_elim] BI.sForall_elim

attribute [rocq_alias siProp_primitive.exist_ne] BI.sExists_ne
attribute [rocq_alias siProp_primitive.exist_intro] BI.sExists_intro
attribute [rocq_alias siProp_primitive.exist_elim] BI.sExists_elim

attribute [rocq_alias siProp_primitive.later_mono] BI.later_mono
attribute [rocq_alias siProp_primitive.later_intro] BI.later_intro
attribute [rocq_alias siProp_primitive.later_forall_2] BI.later_sForall_2
attribute [rocq_alias siProp_primitive.later_exist_false] BI.later_sExists_false
attribute [rocq_alias siProp_primitive.later_false_em] BI.later_false_em

#rocq_ignore siProp_pure_forall "Not necessary due to classical logic, see BiPureForall."
#rocq_ignore siProp_primitive.pure_forall_2 "Not necessary due to classical logic, see BiPureForall."

#rocq_ignore siProp_bi_later_mixin "Not needed in Lean."
#rocq_ignore siProp_bi_mixin "Not needed in Lean."
#rocq_ignore siProp_bi_persistently_mixin "Not needed in Lean."

#rocq_ignore siProp.siProp_and_unseal "Not needed in Lean."
#rocq_ignore siProp.siProp_cmra_valid_unseal "Not needed in Lean."
#rocq_ignore siProp.siProp_emp_unseal "Not needed in Lean."
#rocq_ignore siProp.siProp_exist_unseal "Not needed in Lean."
#rocq_ignore siProp.siProp_forall_unseal "Not needed in Lean."
#rocq_ignore siProp.siProp_impl_unseal "Not needed in Lean."
#rocq_ignore siProp.siProp_internal_eq_unseal "Not needed in Lean."
#rocq_ignore siProp.siProp_later_unseal "Not needed in Lean."
#rocq_ignore siProp.siProp_or_unseal "Not needed in Lean."
#rocq_ignore siProp.siProp_persistently_unseal "Not needed in Lean."
#rocq_ignore siProp.siProp_pure_unseal "Not needed in Lean."
#rocq_ignore siProp.siProp_sep_unseal "Not needed in Lean."
#rocq_ignore siProp.siProp_unseal "Not needed in Lean."
#rocq_ignore siProp.siProp_wand_unseal "Not needed in Lean."

/-! ## Extra BI instances -/

@[rocq_alias siProp_affine]
instance instBIAffine : BIAffine (SiProp SI) where
  affine _ := { affine := fun (_ : SI) _ => trivial }

@[rocq_alias siProp_later_contractive, rocq_alias siProp_primitive.later_contractive]
instance instBILaterContractive : BILaterContractive (SiProp SI) where
  distLater_dist h m hle :=
    ⟨fun hP k hk => (h k (SIdx.lt_le_trans hk hle) SIdx.le_refl).mp (hP k hk),
     fun hP k hk => (h k (SIdx.lt_le_trans hk hle) SIdx.le_refl).mpr (hP k hk)⟩

@[rocq_alias siProp_persistent]
instance instPersistent (P : SiProp SI) : Persistent P where
  persistent _ := id

@[rocq_alias siProp_persistently_forall]
instance instPersistentlyForall : BIPersistentlyForall (SiProp SI) where
  persistently_sForall_2 _ n h P hΨ := h _ ⟨P, rfl⟩ n SIdx.le_refl hΨ

@[rocq_alias siProp_persistently_exist]
instance instPersistentlyExist : BIPersistentlyExist (SiProp SI) where
  persistently_sExists_1 _ _ := fun ⟨P, hΨ, hP⟩ => ⟨_, ⟨P, rfl⟩, hΨ, hP⟩

#rocq_ignore siProp_primitive.siProp_unseal "Not needed in Lean."

/-! ## Internal equality -/

@[rocq_alias siProp_internal_eq]
def internalEq [OFE A] (a₁ a₂ : A) : SiProp SI where
  holds n := a₁ ≡{n}≡ a₂
  closed h hle := Dist.le h hle

@[simp] theorem internalEq_holds [OFE A] {a b : A} {n} :
    (internalEq a b).holds n ↔ a ≡{n}≡ b := .rfl

#rocq_ignore siProp_internal_eq_def "Not needed in Lean."
#rocq_ignore siProp_internal_eq_aux "Not needed in Lean."
#rocq_ignore siProp_internal_eq_unseal "Not needed in Lean."

@[rocq_alias siProp_primitive.internal_eq_ne]
instance instNonExpansive₂InternalEq [OFE A] : NonExpansive₂ (internalEq (A := A)) where
  ne _ _ _ h₁ _ _ h₂ _ hle :=
    ⟨fun heq => (Dist.le h₁ hle).symm.trans (heq.trans (Dist.le h₂ hle)),
     fun heq => (Dist.le h₁ hle).trans (heq.trans (Dist.le h₂ hle).symm)⟩

@[rocq_alias siProp_primitive.internal_eq_refl]
theorem internalEq_refl [OFE A] (P : SiProp SI) (a : A) : P ⊢ internalEq a a :=
  fun _ _ => Dist.rfl

@[rocq_alias siProp_primitive.internal_eq_rewrite]
theorem internalEq_rewrite [OFE A] (a b : A) (Ψ : A → SiProp SI) [HΨ : NonExpansive Ψ] :
    internalEq a b ⊢ Ψ a → Ψ b :=
  fun _ hab _ hle => (HΨ.ne (.le hab hle) SIdx.le_refl).mp

@[rocq_alias siProp_primitive.prop_ext_2]
theorem prop_ext (P Q : SiProp SI) : (P → Q) ∧ (Q → P) ⊢ internalEq P Q :=
  fun _ ⟨hPQ, hQP⟩ n' hle => ⟨hPQ n' hle, hQP n' hle⟩

@[rocq_alias siProp_primitive.internal_eq_entails]
theorem internalEq_entails [OFE A] [OFE B] (a₁ a₂ : A) (b₁ b₂ : B) :
    (internalEq a₁ a₂ ⊢ internalEq b₁ b₂) ↔ (∀ n, a₁ ≡{n}≡ a₂ → b₁ ≡{n}≡ b₂) :=
  Iff.rfl

@[rocq_alias siProp_primitive.fun_extI]
theorem fun_ext_internalEq [OFEFun (B : A → _)] (g₁ g₂ : (x : A) → B x) :
    (∀ (i : A), internalEq (g₁ i) (g₂ i)) ⊢ internalEq g₁ g₂ :=
  fun _ h x => h _ ⟨x, rfl⟩

@[rocq_alias siProp_primitive.sig_equivI_1]
theorem sig_equiv_internalEq [OFE A] (P : A → Prop) (x y : { a : A // P a }) :
    internalEq x.val y.val ⊢ internalEq x y :=
  fun _ => id

@[rocq_alias siProp_primitive.discrete_eq_1]
theorem discrete_eq_internalEq [OFE A] (a b : A) [Idisc : Std.TCOr (DiscreteE a) (DiscreteE b)] :
    internalEq a b ⊢ ⌜a = b⌝ := by
  cases Idisc with
  | l => exact fun _ hab => DiscreteE.discrete (hab.le SIdx.le_0_l)
  | r => exact fun _ hab => (DiscreteE.discrete (hab.le SIdx.le_0_l).symm).symm

@[rocq_alias siProp_primitive.later_equivI_1]
theorem later_equiv_internalEq_mp [OFE A] (x y : A) :
    internalEq (Later.next x) (Later.next y) ⊢ ▷ internalEq x y :=
  fun _ h m hm => h m hm

@[rocq_alias siProp_primitive.later_equivI_2]
theorem later_equiv_internalEq_mpr [OFE A] (x y : A) :
    ▷ internalEq x y ⊢ internalEq (Later.next x) (Later.next y) :=
  fun _ hP m hlt => hP m hlt

/-! ## CMRA validity -/

@[rocq_alias siProp_cmra_valid]
def cmraValid [CMRA A] (a : A) : SiProp SI where
  holds n := ✓{n} a
  closed h hle := CMRA.validN_of_le hle h

@[simp] theorem cmraValid_holds [CMRA A] {a : A} {n} :
    (cmraValid a).holds n ↔ ✓{n} a := .rfl

#rocq_ignore siProp_cmra_valid_def "Not needed in Lean."
#rocq_ignore siProp_cmra_valid_aux "Not needed in Lean."
#rocq_ignore siProp_cmra_valid_unseal "Not needed in Lean."

@[rocq_alias siProp_primitive.cmra_valid_ne]
instance instNonExpansiveCmraValid [CMRA A] : NonExpansive (cmraValid (A := A)) where
  ne _ _ _ h _ hle := ⟨CMRA.validN_ne (Dist.le h hle), CMRA.validN_ne (Dist.le h hle).symm⟩

@[rocq_alias siProp_primitive.cmra_valid_intro]
theorem cmraValid_intro [CMRA A] {P : SiProp SI} {a : A} (h : CMRA.Valid a) :
    P ⊢ cmraValid a :=
  fun n _ => (CMRA.valid_iff_validN.mp h) n

@[rocq_alias siProp_primitive.cmra_valid_elim]
theorem cmraValid_elim [CMRA A] {a : A} : cmraValid a ⊢ ⌜✓{0} a⌝ :=
  fun _ => CMRA.validN_of_le SIdx.le_0_l

@[rocq_alias siProp_primitive.cmra_valid_weaken]
theorem cmraValid_weaken [CMRA A] {a b : A} : cmraValid (a • b) ⊢ cmraValid a :=
  fun _ => CMRA.validN_op_left

@[rocq_alias siProp_primitive.valid_entails]
theorem cmraValid_entails_iff [CMRA A] [CMRA B] {a : A} {b : B} :
    (cmraValid a ⊢ cmraValid b) ↔ ∀ n, ✓{n} a → ✓{n} b :=
  .rfl

instance cmraValid_timeless [CMRA A] [CMRA.Discrete A] {a : A} :
    Timeless (cmraValid a : SiProp SI) where
  timeless := fun n h => by
    by_cases hn : n = 0
    · subst hn; left; exact fun m hm => absurd hm (SIdx.not_lt_zero m)
    · right
      exact (CMRA.discrete_valid (h 0 (SIdx.neq_0_lt_0.mp hn))).validN

/-! ## Soundness lemmas -/

@[rocq_alias siProp_primitive.pure_soundness]
theorem pure_soundness {φ : Prop} (h : True ⊢@{SiProp SI} ⌜φ⌝) : φ := h 0 trivial

@[rocq_alias siProp_primitive.internal_eq_soundness]
theorem internalEq_soundness [OFE A] {x y : A} (h : True ⊢@{SiProp SI} internalEq x y) : x = y :=
  OFE.eq_dist_2 fun n => h n trivial

@[rocq_alias siProp_primitive.later_soundness]
theorem later_soundness {P : SiProp SI} (h : True ⊢ ▷ P) : True ⊢ P :=
  fun n _ => h (succᵢ n) trivial n (SIdx.lt_succ_self n)

end SiProp
end Iris
