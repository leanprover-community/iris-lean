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


variable {SI : Iris.stepindex (Type _)} [Iris.SIdx SI]
local stepindex SI

/-!
# Step-Indexed Propositions (siProp)

The type `SiProp` defines "plain" step-indexed propositions, on which we define the
usual connectives of higher-order logic and prove that these satisfy the axioms of BI.
-/

namespace Iris
open OFE BI

/-- Step-indexed proposition, downward closed in the step index. -/
@[indexed, rocq_alias siProp]
structure SiProp {SI : stepindex (Type _)} [SIdx SI] where
  holds : SI → Prop
  closed {n₁ n₂ : SI} : holds n₁ → n₂ ≤ n₁ → holds n₂

namespace SiProp
open ORA

/-! ## Connective definitions -/

@[indexed, rocq_alias siProp_pure]
def pure (φ : Prop) : SiProp where
  holds _ := φ
  closed h _ := h

#rocq_ignore siProp_pure_def "Not needed in Lean."
#rocq_ignore siProp_pure_aux "Not needed in Lean."
#rocq_ignore siProp_pure_unseal "Not needed in Lean."

@[rocq_alias siProp_and]
def and (P Q : SiProp) : SiProp where
  holds n := P.holds n ∧ Q.holds n
  closed h hle := ⟨P.closed h.1 hle, Q.closed h.2 hle⟩

#rocq_ignore siProp_and_def "Not needed in Lean."
#rocq_ignore siProp_and_aux "Not needed in Lean."
#rocq_ignore siProp_and_unseal "Not needed in Lean."

@[rocq_alias siProp_or]
def or (P Q : SiProp) : SiProp where
  holds n := P.holds n ∨ Q.holds n
  closed h hle := h.imp (P.closed · hle) (Q.closed · hle)

#rocq_ignore siProp_or_def "Not needed in Lean."
#rocq_ignore siProp_or_aux "Not needed in Lean."
#rocq_ignore siProp_or_unseal "Not needed in Lean."

@[rocq_alias SiProp_downclose]
def downClose (Pi : SI → Prop) : SiProp where
  holds n := ∀ (n' : SI), n' ≤ n → Pi n'
  closed h hle n' hn' := h n' (SIdx.le_trans hn' hle)

@[rocq_alias siProp_impl]
def imp (P Q : SiProp) : SiProp :=
  downClose fun n => P.holds n → Q.holds n

#rocq_ignore siProp_impl_def "Not needed in Lean."
#rocq_ignore siProp_impl_aux "Not needed in Lean."
#rocq_ignore siProp_impl_unseal "Not needed in Lean."

@[rocq_alias siProp_forall]
def all (Φ : SiProp → Prop) : SiProp where
  holds n := ∀ P, Φ P → P.holds n
  closed h hle P hP := P.closed (h P hP) hle

#rocq_ignore siProp_forall_def "Not needed in Lean."
#rocq_ignore siProp_forall_aux "Not needed in Lean."
#rocq_ignore siProp_forall_unseal "Not needed in Lean."

@[rocq_alias siProp_exist]
def exist (Φ : SiProp → Prop) : SiProp where
  holds n := ∃ P, Φ P ∧ P.holds n
  closed := fun ⟨P, hP, hh⟩ hle => ⟨P, hP, P.closed hh hle⟩

#rocq_ignore siProp_exist_def "Not needed in Lean."
#rocq_ignore siProp_exist_aux "Not needed in Lean."
#rocq_ignore siProp_exist_unseal "Not needed in Lean."

@[rocq_alias siProp_later]
def later (P : SiProp) : SiProp where
  holds n := ∀ (m : SI), m < n → P.holds m
  closed h hle m hm := h m (SIdx.lt_le_trans hm hle)

#rocq_ignore siProp_later_def "Not needed in Lean."
#rocq_ignore siProp_later_aux "Not needed in Lean."
#rocq_ignore siProp_later_unseal "Not needed in Lean."

/-! ## OFE / COFE / BIBase instances -/

@[rocq_alias siProp_entails]
def entails (P Q : SiProp) : Prop := ∀ (n : SI), P.holds n → Q.holds n

@[rocq_alias siPropO]
instance : OFE (SiProp) where
  dist n P Q := ∀ {m : SI}, m ≤ n → (P.holds m ↔ Q.holds m)
  dist_eqv.refl _ _ _ := Iff.rfl
  dist_eqv.symm h _ hle := (h hle).symm
  dist_eqv.trans h₁ h₂ _ hle := (h₁ hle).trans (h₂ hle)
  eq_dist' {P Q} := by
    refine ⟨?_, fun h => ?_⟩
    · rintro rfl _ _ _; exact Iff.rfl
    · obtain ⟨ph, hp⟩ := P; obtain ⟨qh, _⟩ := Q
      have : ph = qh := funext fun n => propext (h n SIdx.le_refl)
      subst this; rfl
  dist_lt h hlt _ hle := h (SIdx.lt_le_incl (SIdx.le_lt_trans hle hlt))

#rocq_ignore siProp_equiv' "OFE is Leibniz; use equality."
#rocq_ignore siProp_equiv "OFE is Leibniz; use equality."
#rocq_ignore siProp_dist' "Inlined in the `OFE` construction."
#rocq_ignore siProp_dist "Inlined in the `OFE` construction."
#rocq_ignore siProp_ofe_mixin "Not needed in Lean."

@[rocq_alias siProp_cofe]
instance : IsCOFE (SiProp) where
  compl c := {
    holds n := (c n).holds n
    closed {n₁ _} h hle := (c.cauchy hle SIdx.le_refl).mp (c n₁ |>.closed h hle)
  }
  conv_compl {_ c} _ hle := c.cauchy hle SIdx.le_refl |>.symm
  lbcompl {n} _ c := {
    holds n' := ∀ (n'' : SI) (hn'' : n'' < n), n'' ≤ n' → (c.bchain n'' hn'').holds n''
    closed h hle n'' hn'' hle' := h n'' hn'' (SIdx.le_trans hle' hle)
  }
  conv_lbcompl {n} _ c {m} hm n' hn' := by
    refine ⟨fun h => ?_, fun h n'' hn'' hle => ?_⟩
    · have hn'n := SIdx.le_lt_trans hn' hm
      exact (c.bcauchy hn'n hm hn' SIdx.le_refl).mpr (h n' hn'n SIdx.le_refl)
    · exact (c.bcauchy hn'' hm (SIdx.le_trans hle hn') SIdx.le_refl).mp
        ((c.bchain m hm).closed h hle)
  lbcompl_ne {_} _ c1 c2 {m} H n' hn' :=
    ⟨fun h n'' hn'' hle => (H n'' hn'' (SIdx.le_trans hle hn')).mp (h n'' hn'' hle),
     fun h n'' hn'' hle => (H n'' hn'' (SIdx.le_trans hle hn')).mpr (h n'' hn'' hle)⟩

#rocq_ignore siProp_compl "Included in IsCOFE instance."
#rocq_ignore siProp_lbcompl "Included in IsCOFE instance."

section BIInstance

/-- The connectives of `SiProp`. Not a global instance: outside this section `BIBase (SiProp)`
is only reachable through `BI.toBIBase instBI`, so generic `[BI PROP]` lemmas unify at
`SiProp` without pinning `SI`. -/
@[reducible] def instBIBase : BIBase (SiProp) where
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

attribute [local instance] instBIBase

#rocq_ignore siProp_emp "Included in BIBase instance."
#rocq_ignore siProp_sep "Included in BIBase instance."
#rocq_ignore siProp_wand "Included in BIBase instance."
#rocq_ignore siProp_persistently "Included in BIBase instance."

@[rocq_alias siProp_primitive.entails_po]
instance siPropPreorder : Std.IsPreorder (SiProp) where
  le_refl _ _ := id
  le_trans _ _ _ h₁ h₂ n h := h₂ n (h₁ n h)

/-! ## BI instance -/

@[rocq_alias siPropI]
instance instBI : BI (SiProp) where
  toBIBase := instBIBase
  entails_refl := siPropPreorder.le_refl _
  entails_trans := siPropPreorder.le_trans _ _ _
  equiv_iff := OFE.eq_dist.trans
    ⟨fun heq => ⟨fun n hP => (heq n SIdx.le_refl).mp hP, fun n hQ => (heq n SIdx.le_refl).mpr hQ⟩,
     fun H _ _ _ => ⟨H.1 _, H.2 _⟩⟩
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
  later_mono h _ hlP k hk := h k (hlP k hk)
  later_intro {P} _ hP _ hk := P.closed hP (SIdx.lt_le_incl hk)
  later_sForall_2 n h _ hk P hP := h _ ⟨P, rfl⟩ n SIdx.le_refl hP _ hk
  later_false_sExists {Φ} n h := by
    obtain ⟨P, hΦP, hP0⟩ := h (0 : SI) SIdx.le_0_l fun k hk => absurd hk (SIdx.not_lt_zero k)
    exact ⟨_, ⟨P, rfl⟩, hΦP, fun _ _ hF => P.closed hP0 (SIdx.le_ngt.mpr fun hlt => hF _ hlt)⟩
  later_false_sep _ h := ⟨fun n' hn' hF => (h n' hn' hF).1, fun n' hn' hF => (h n' hn' hF).2⟩
  later_sep_2 _ h k hk := ⟨h.1 k hk, h.2 k hk⟩
  later_persistently := ⟨fun _ => id, fun _ => id⟩
  later_false_em {P} n hP := by
    by_cases hn : n = 0
    · subst hn; exact .inl fun k hk => absurd hk (SIdx.not_lt_zero k)
    · exact .inr fun _ _ hF =>
        P.closed (hP 0 (SIdx.neq_0_lt_0.mp hn)) (SIdx.le_ngt.mpr fun hlt => hF _ hlt)

instance instBIStepIndexed : BIStepIndexed (SiProp) where
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
  later_ne.ne _ _ _ h _ hle :=
    ⟨fun hP k hk => (h (SIdx.le_trans (SIdx.lt_le_incl hk) hle)).mp (hP k hk),
     fun hQ k hk => (h (SIdx.le_trans (SIdx.lt_le_incl hk) hle)).mpr (hQ k hk)⟩

instance instBILaterFinite [SIdxFinite SI] : BILaterFinite (SiProp) where
  later_sExists_false n h := by
    rcases SIdxFinite.finite_index n with rfl | ⟨m, hm⟩
    · exact .inl fun k hk => absurd hk (SIdx.not_lt_zero k)
    · obtain ⟨P, hΦP, hPm⟩ := h m hm.lt
      exact .inr ⟨_, ⟨P, rfl⟩, hΦP, fun _ hk => P.closed hPm (hm.le_of_lt hk)⟩
  later_sep_1 _ h := ⟨fun k hk => (h k hk).1, fun k hk => (h k hk).2⟩

end BIInstance

/-! ## Step-indexed characterisation of the connectives

`BI`'s quantifiers range over *sets* of `SiProp`s, so `∃`/`∀` do not reduce to their
meta-level counterparts by `rfl`; the remaining connectives do. -/

theorem biEntails_of_iff {P Q : SiProp} (h : ∀ (n : SI), P.holds n ↔ Q.holds n) : P ⊣⊢ Q :=
  ⟨fun n => (h n).mp, fun n => (h n).mpr⟩

@[simp] theorem pure_holds {φ : Prop} {n : SI} : (iprop(⌜φ⌝) : SiProp).holds n ↔ φ := .rfl

@[simp] theorem and_holds {P Q : SiProp} {n : SI} :
    (iprop(P ∧ Q) : SiProp).holds n ↔ P.holds n ∧ Q.holds n := .rfl

@[simp] theorem sep_holds {P Q : SiProp} {n : SI} :
    (iprop(P ∗ Q) : SiProp).holds n ↔ P.holds n ∧ Q.holds n := .rfl

@[simp] theorem or_holds {P Q : SiProp} {n : SI} :
    (iprop(P ∨ Q) : SiProp).holds n ↔ P.holds n ∨ Q.holds n := .rfl

theorem later_holds {P : SiProp} {n : SI} :
    (iprop(▷ P) : SiProp).holds n ↔ ∀ (m : SI), m < n → P.holds m := .rfl

@[simp] theorem later_holds_zero {P : SiProp} : (iprop(▷ P) : SiProp).holds (0 : SI) ↔ True :=
  ⟨fun _ => trivial, fun _ k hk => absurd hk (SIdx.not_lt_zero k)⟩

/-- Without step-indexing (`SIdxZero`), `▷ P` always holds: no index lies below `0`. -/
theorem later_holds_of_zero [SIdxZero SI] {P : SiProp} {n : SI} : (iprop(▷ P) : SiProp).holds n :=
  fun m hm => absurd (SIdxZero.all_0 n ▸ hm) (SIdx.not_lt_zero m)

@[simp] theorem later_holds_succ [SIdxSucc SI] {P : SiProp} {n : SI} :
    (iprop(▷ P) : SiProp).holds (SIdx.succ n) ↔ P.holds n :=
  ⟨fun h => h n (SIdx.lt_succ_self n), fun h _ hk => P.closed h (SIdx.lt_succ_r.mp hk)⟩

@[simp] theorem exists_holds {α : Sort _} {Φ : α → SiProp} {n : SI} :
    (iprop(∃ x, Φ x) : SiProp).holds n ↔ ∃ x, (Φ x).holds n :=
  ⟨fun ⟨_, ⟨x, rfl⟩, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨Φ x, ⟨x, rfl⟩, h⟩⟩

@[simp] theorem forall_holds {α : Sort _} {Φ : α → SiProp} {n : SI} :
    (iprop(∀ x, Φ x) : SiProp).holds n ↔ ∀ x, (Φ x).holds n := by
  refine ⟨fun h x => h (Φ x) ⟨x, rfl⟩, fun h P hP => ?_⟩
  obtain ⟨x, rfl⟩ := hP
  exact h x

@[rocq_alias siProp_primitive.pure_ne]
theorem pure_dist_of_iff {n : SI} {Φ Ψ : Prop} (H : Φ ↔ Ψ) : pure Φ ≡{n}≡ pure Ψ := fun _ => iff_comm.mp H.symm

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
instance instBIAffine : BIAffine (SiProp) where
  affine _ := { affine := fun _ _ => trivial }

@[rocq_alias siProp_later_contractive, rocq_alias siProp_primitive.later_contractive]
instance instBILaterContractive : BILaterContractive (SiProp) where
  distLater_dist h _ hle :=
    ⟨fun hP k hk => (h k (SIdx.lt_le_trans hk hle) SIdx.le_refl).mp (hP k hk),
     fun hQ k hk => (h k (SIdx.lt_le_trans hk hle) SIdx.le_refl).mpr (hQ k hk)⟩

@[rocq_alias siProp_persistent]
instance instPersistent (P : SiProp) : Persistent P where
  persistent _ := id

@[rocq_alias siProp_persistently_forall]
instance instPersistentlyForall : BIPersistentlyForall (SiProp) where
  persistently_sForall_2 _ n h P hΨ := h _ ⟨P, rfl⟩ n SIdx.le_refl hΨ

@[rocq_alias siProp_persistently_exist]
instance instPersistentlyExist : BIPersistentlyExist (SiProp) where
  persistently_sExists_1 _ _ := fun ⟨P, hΨ, hP⟩ => ⟨_, ⟨P, rfl⟩, hΨ, hP⟩

#rocq_ignore siProp_primitive.siProp_unseal "Not needed in Lean."

/-! ## Internal equality -/

@[indexed, rocq_alias siProp_internal_eq]
def internalEq [OFE A] (a₁ a₂ : A) : SiProp where
  holds n := a₁ ≡{n}≡ a₂
  closed h hle := Dist.le h hle

@[simp] theorem internalEq_holds [OFE A] {a b : A} {n : SI} :
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
theorem internalEq_refl [OFE A] (P : SiProp) (a : A) : P ⊢ internalEq a a :=
  fun _ _ => Dist.rfl

@[rocq_alias siProp_primitive.internal_eq_rewrite]
theorem internalEq_rewrite [OFE A] (a b : A) (Ψ : A → SiProp) [HΨ : NonExpansive Ψ] :
    internalEq a b ⊢ Ψ a → Ψ b :=
  fun _ hab _ hle => (HΨ.ne (.le hab hle) SIdx.le_refl).mp

@[rocq_alias siProp_primitive.prop_ext_2]
theorem prop_ext (P Q : SiProp) : (P → Q) ∧ (Q → P) ⊢ internalEq P Q :=
  fun _ ⟨hPQ, hQP⟩ n' hle => ⟨hPQ n' hle, hQP n' hle⟩

@[rocq_alias siProp_primitive.internal_eq_entails]
theorem internalEq_entails [OFE A] [OFE B] (a₁ a₂ : A) (b₁ b₂ : B) :
    (internalEq a₁ a₂ ⊢ internalEq b₁ b₂) ↔ (∀ (n : SI), a₁ ≡{n}≡ a₂ → b₁ ≡{n}≡ b₂) :=
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
theorem later_equiv_internalEq_mp [SIdxSucc SI] [OFE A] (x y : A) :
    internalEq (Later.next x) (Later.next y) ⊢ ▷ internalEq x y :=
  fun _ h => h

@[rocq_alias siProp_primitive.later_equivI_2]
theorem later_equiv_internalEq_mpr [SIdxSucc SI] [OFE A] (x y : A) :
    ▷ internalEq x y ⊢ internalEq (Later.next x) (Later.next y) :=
  fun _ h => h

/-! ## ORA validity -/

@[indexed, rocq_alias siProp_cmra_valid]
def cmraValid [RA A] [ORA A] (a : A) : SiProp where
  holds n := ✓{n} a
  closed h hle := validN_of_le hle h

@[simp] theorem cmraValid_holds [RA A] [ORA A] {a : A} {n : SI} :
    (cmraValid a).holds n ↔ ✓{n} a := .rfl

#rocq_ignore siProp_cmra_valid_def "Not needed in Lean."
#rocq_ignore siProp_cmra_valid_aux "Not needed in Lean."
#rocq_ignore siProp_cmra_valid_unseal "Not needed in Lean."

@[rocq_alias siProp_primitive.cmra_valid_ne]
instance instNonExpansiveCmraValid [RA A] [ORA A] : NonExpansive (cmraValid (A := A)) where
  ne _ _ _ h _ hle := ⟨validN_ne (Dist.le h hle), validN_ne (Dist.le h hle).symm⟩

@[rocq_alias siProp_primitive.cmra_valid_intro]
theorem cmraValid_intro [RA A] [ORA A] {P : SiProp} {a : A} (h : ✓ a) :
    P ⊢ cmraValid a :=
  fun n _ => (valid_iff_validN.mp h) n

@[rocq_alias siProp_primitive.cmra_valid_elim]
theorem cmraValid_elim [RA A] [ORA A] {a : A} : cmraValid a ⊢ ⌜✓{(0 : SI)} a⌝ :=
  fun _ => validN_of_le SIdx.le_0_l

@[rocq_alias siProp_primitive.cmra_valid_weaken]
theorem cmraValid_weaken [RA A] [ORA A] {a b : A} : cmraValid (a • b) ⊢ cmraValid a :=
  fun _ => validN_op_left

@[rocq_alias siProp_primitive.valid_entails]
theorem cmraValid_entails_iff [RA A] [ORA A] [RA B] [ORA B] {a : A} {b : B} :
    (cmraValid a ⊢ cmraValid b) ↔ ∀ (n : SI), ✓{n} a → ✓{n} b :=
  .rfl

instance cmraValid_timeless [RA A] [ORA A] [ORA.Discrete A] {a : A} :
    Timeless (cmraValid a : SiProp) where
  timeless := fun _ h =>
    (discrete_valid (h 0 SIdx.le_0_l fun k hk => absurd hk (SIdx.not_lt_zero k))).validN

/-! ## Soundness lemmas -/

@[indexed, rocq_alias siProp_primitive.pure_soundness]
theorem pure_soundness {φ : Prop} (h : True ⊢@{SiProp} ⌜φ⌝) : φ := h (0 : SI) trivial

@[rocq_alias siProp_primitive.exist_soundness]
theorem exist_soundness [SIdxZero SI] {A : Sort _} {Φ : A → SiProp}
    (h : True ⊢@{SiProp} ∃ x, Φ x) : ∃ x, True ⊢@{SiProp} Φ x :=
  have ⟨x, hx⟩ := exists_holds.mp (h (0 : SI) trivial)
  ⟨x, fun n _ => SIdxZero.all_0 n ▸ hx⟩

@[rocq_alias siProp_primitive.internal_eq_soundness]
theorem internalEq_soundness [OFE A] {x y : A} (h : True ⊢@{SiProp} internalEq x y) : x = y :=
  OFE.eq_dist_2 fun n => h n trivial

@[rocq_alias siProp_primitive.later_soundness]
theorem later_soundness [SIdxSucc SI] {P : SiProp} (h : True ⊢ ▷ P) : True ⊢ P :=
  fun n _ => h (SIdx.succ n) trivial n (SIdx.lt_succ_self n)

end SiProp
end Iris
