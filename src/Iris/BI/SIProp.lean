/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.BI.BI
public import Iris.BI.Extensions
public import Iris.BI.Classes
public import Iris.BI.DerivedLaws
public import Iris.Algebra.CMRA
public meta import Iris.Std.RocqAlias

@[expose] public section

/-!
# Step-Indexed Propositions (siProp)

The type `SiProp` defines "plain" step-indexed propositions, on which we define the
usual connectives of higher-order logic and prove that these satisfy the axioms of BI.
-/

namespace Iris
open OFE BI

/-- Step-indexed proposition, downward closed in the step index. -/
@[rocq_alias siProp]
structure SiProp where
  holds : Nat → Prop
  closed : holds n₁ → n₂ ≤ n₁ → holds n₂

namespace SiProp

/-! ## Connective definitions -/

@[rocq_alias siProp_pure]
def pure (φ : Prop) : SiProp where
  holds _ := φ
  closed h _ := h

@[rocq_alias siProp_and]
def and (P Q : SiProp) : SiProp where
  holds n := P.holds n ∧ Q.holds n
  closed h hle := ⟨P.closed h.1 hle, Q.closed h.2 hle⟩

@[rocq_alias siProp_or]
def or (P Q : SiProp) : SiProp where
  holds n := P.holds n ∨ Q.holds n
  closed h hle := h.imp (P.closed · hle) (Q.closed · hle)

@[rocq_alias siProp_downclose]
def downClose (Pi : Nat → Prop) : SiProp where
  holds n := ∀ n', n' ≤ n → Pi n'
  closed h _ n' _ := h n' (by omega)

@[rocq_alias siProp_impl]
def imp (P Q : SiProp) : SiProp :=
  downClose fun n => P.holds n → Q.holds n

@[rocq_alias siProp_forall]
def all (Φ : SiProp → Prop) : SiProp where
  holds n := ∀ P, Φ P → P.holds n
  closed h hle P hP := P.closed (h P hP) hle

@[rocq_alias siProp_exist]
def exist (Φ : SiProp → Prop) : SiProp where
  holds n := ∃ P, Φ P ∧ P.holds n
  closed := fun ⟨P, hP, hh⟩ hle => ⟨P, hP, P.closed hh hle⟩

@[rocq_alias siProp_later]
def later (P : SiProp) : SiProp where
  holds n := match n with | 0 => True | n + 1 => P.holds n
  closed {n₁ n₂} h hle := by
    cases n₂ with
    | zero => trivial
    | succ n₂ => cases n₁ with | zero => omega | succ n₁ => exact P.closed h (by omega)

/-! ## OFE / COFE / BIBase instances -/

@[rocq_alias siProp_entails]
def entails (P Q : SiProp) : Prop := ∀ n, P.holds n → Q.holds n

instance : OFE SiProp where
  Equiv P Q := ∀ {n}, P.holds n ↔ Q.holds n
  Dist n P Q := ∀ {m}, m ≤ n → (P.holds m ↔ Q.holds m)
  dist_eqv.refl _ _ _ := Iff.rfl
  dist_eqv.symm h _ hle := (h hle).symm
  dist_eqv.trans h₁ h₂ _ hle := (h₁ hle).trans (h₂ hle)
  equiv_dist.mp heq _ _ _ := heq
  equiv_dist.mpr h n := h n .refl
  dist_lt h _ _ _ := h (by omega)

instance : IsCOFE SiProp where
  compl c := {
    holds n := (c n).holds n
    closed {n₁ _} h hle := (c.cauchy hle .refl).mp (c n₁ |>.closed h hle)
  }
  conv_compl {_ c} _ hle := c.cauchy hle .refl |>.symm

instance : BIBase SiProp where
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

instance : Std.Preorder (BIBase.Entails (PROP := SiProp)) where
  refl _ h := h
  trans h₁ h₂ n h := h₂ n (h₁ n h)

/-! ## BI instance -/

@[rocq_alias siPropI]
instance instBI : BI SiProp where
  entails_preorder := inferInstance
  equiv_iff.mp heq := ⟨fun _ => heq.mp, fun _ => heq.mpr⟩
  equiv_iff.mpr H n := ⟨H.1 n, H.2 n⟩
  and_ne.ne _ _ _ h₁ _ _ h₂ m h := ⟨.imp (h₁ h).mp (h₂ h).mp, .imp (h₁ h).mpr (h₂ h).mpr⟩
  or_ne.ne _ _ _ h₁ _ _ h₂ m h := ⟨.imp (h₁ h).mp (h₂ h).mp, .imp (h₁ h).mpr (h₂ h).mpr⟩
  imp_ne.ne _ _ _ h₁ _ _ h₂ m hle := {
    mp hpq n' hn' hP := h₂ (by omega) |>.mp <| hpq n' hn' <| (h₁ (by omega)).mpr hP
    mpr hpq n' hn' hP := h₂ (by omega) |>.mpr <| hpq n' hn' <| (h₁ (by omega)).mp hP
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
    mp hpq n' hn' hP := h₂ (by omega) |>.mp <| hpq n' hn' <| (h₁ (by omega)).mpr hP
    mpr hpq n' hn' hP := h₂ (by omega) |>.mpr <| hpq n' hn' <| (h₁ (by omega)).mp hP
  }
  persistently_ne.ne _ _ _ h m hle := h hle
  later_ne.ne _ _ _ h m hle := match m with | .zero => .rfl | .succ _ => h (by omega)
  pure_intro h _ _ := h
  pure_elim' h _ hφ := h hφ _ trivial
  and_elim_l _ h := h.1
  and_elim_r _ h := h.2
  and_intro h₁ h₂ _ h := ⟨h₁ _ h, h₂ _ h⟩
  or_intro_l _ h := .inl h
  or_intro_r _ h := .inr h
  or_elim h₁ h₂ _ h := h.elim (h₁ _) (h₂ _)
  imp_intro {P _ _} h n hP n' hle hQ := h n' ⟨P.closed hP hle, hQ⟩
  imp_elim h n hPQ := h n hPQ.1 n .refl hPQ.2
  sForall_intro h _ hP P hΨ := h P hΨ _ hP
  sForall_elim h _ hF := hF _ h
  sExists_intro h _ hP := ⟨_, h, hP⟩
  sExists_elim h := fun _ ⟨_, hΨ, hP⟩ => h _ hΨ _ hP
  sep_mono h₁ h₂ _ hPQ := ⟨h₁ _ hPQ.1, h₂ _ hPQ.2⟩
  emp_sep := ⟨fun _ hPQ => hPQ.2, fun _ hP => ⟨trivial, hP⟩⟩
  sep_symm _ hPQ := ⟨hPQ.2, hPQ.1⟩
  sep_assoc_l _ hPQR := ⟨hPQR.1.1, hPQR.1.2, hPQR.2⟩
  wand_intro := fun {P _ _} h n hP n' hle hQ => h n' ⟨P.closed hP hle, hQ⟩
  wand_elim h n hPQ := h n hPQ.1 n .refl hPQ.2
  persistently_mono h := h
  persistently_idem_2 _ h := h
  persistently_emp_2 _ h := h
  persistently_and_2 _ h := h
  persistently_sExists_1 := fun _ ⟨P, hΨ, hPn⟩ => ⟨_, ⟨P, rfl⟩, hΨ, hPn⟩
  persistently_absorb_l _ h := h.1
  persistently_and_l _ h := h
  later_mono h n hlP := match n with | .zero => trivial | .succ _ => h _ hlP
  later_intro {P} n hP := match n with | .zero => trivial | .succ _ => P.closed hP (by omega)
  later_sForall_2 n h := match n with | .zero => trivial | .succ _ => (h _ ⟨·, rfl⟩ _ .refl)
  later_sExists_false {Φ} n h := by
    cases n with
    | zero => exact .inl trivial
    | succ n =>
      obtain ⟨P, hΦP, hPn⟩ := h
      exact .inr ⟨_, ⟨P, rfl⟩, hΦP, hPn⟩
  later_sep.mp := fun n h => match n with | .zero => ⟨trivial, trivial⟩ | .succ _ => h
  later_sep.mpr := fun n h => match n with | .zero => trivial | .succ _ => h
  later_persistently := ⟨fun _ => id, fun _ => id⟩
  later_false_em {P} n hP :=
    match n with
    | .zero => .inl trivial
    | .succ n =>
      .inr fun n' hle hF =>
      match n' with
      | .zero => P.closed hP (Nat.zero_le _)
      | .succ _ => absurd hF id

@[rocq_alias pure_ne]
theorem pure_dist_of_iff {Φ Ψ : Prop} (H : Φ ↔ Ψ) : pure Φ ≡{n}≡ pure Ψ := fun _ => iff_comm.mp H.symm


/-! ## Extra BI instances -/

@[rocq_alias siProp_affine]
instance instBIAffine : BIAffine SiProp where
  affine _ := { affine := fun _ _ => trivial }

@[rocq_alias siProp_later_contractive]
instance instBILaterContractive : BILaterContractive SiProp where
  distLater_dist h m hle := match m with | .zero => .rfl | .succ k => h k (by omega) .refl

@[rocq_alias siProp_persistent]
instance instPersistent (P : SiProp) : Persistent P where
  persistent _ := id

/-! ## Internal equality -/

@[rocq_alias siProp_internal_eq]
def internalEq [OFE A] (a₁ a₂ : A) : SiProp where
  holds n := a₁ ≡{n}≡ a₂
  closed h hle := Dist.le h hle

@[rocq_alias internal_eq_ne]
instance instNonExpansive₂InternalEq [OFE A] : NonExpansive₂ (internalEq (A := A)) where
  ne _ _ _ h₁ _ _ h₂ _ hle :=
    ⟨fun heq => (Dist.le h₁ hle).symm.trans (heq.trans (Dist.le h₂ hle)),
     fun heq => (Dist.le h₁ hle).trans (heq.trans (Dist.le h₂ hle).symm)⟩

@[rocq_alias internal_eq_refl]
theorem internalEq_refl [OFE A] (P : SiProp) (a : A) : P ⊢ internalEq a a :=
  fun _ _ => Dist.rfl

@[rocq_alias internal_eq_rewrite]
theorem internalEq_rewrite [OFE A] (a b : A) (Ψ : A → SiProp) [HΨ : NonExpansive Ψ] :
    internalEq a b ⊢ Ψ a → Ψ b :=
  fun _ hab _ hle => (HΨ.ne (.le hab hle) .refl).mp

@[rocq_alias prop_ext_2]
theorem prop_ext (P Q : SiProp) : (P → Q) ∧ (Q → P) ⊢ internalEq P Q :=
  fun _ ⟨hPQ, hQP⟩ n' hle => ⟨hPQ n' hle, hQP n' hle⟩

@[rocq_alias internal_eq_entails]
theorem internalEq_entails [OFE A] [OFE B] (a₁ a₂ : A) (b₁ b₂ : B) :
    (internalEq a₁ a₂ ⊢ internalEq b₁ b₂) ↔ (∀ n, a₁ ≡{n}≡ a₂ → b₁ ≡{n}≡ b₂) :=
  Iff.rfl

@[rocq_alias fun_extI]
theorem fun_ext_internalEq [OFEFun (B : A → _)] (g₁ g₂ : (x : A) → B x) :
    (∀ (i : A), internalEq (g₁ i) (g₂ i)) ⊢ internalEq g₁ g₂ :=
  fun _ h x => h _ ⟨x, rfl⟩

@[rocq_alias sig_equivI_1]
theorem sig_equiv_internalEq [OFE A] (P : A → Prop) (x y : { a : A // P a }) :
    internalEq x.val y.val ⊢ internalEq x y :=
  fun _ => id

@[rocq_alias discrete_eq_1]
theorem discrete_eq_internalEq [OFE A] (a b : A) [Idisc : Std.TCOr (DiscreteE a) (DiscreteE b)] :
    internalEq a b ⊢ ⌜a ≡ b⌝ := by
  cases Idisc with
  | l => exact fun _ hab => DiscreteE.discrete (hab.le (Nat.zero_le _))
  | r => exact fun _ hab => (DiscreteE.discrete (hab.le (Nat.zero_le _)).symm).symm

@[rocq_alias later_equivI_1]
theorem later_equiv_internalEq_mp [OFE A] (x y : A) :
    internalEq (Later.next x) (Later.next y) ⊢ ▷ internalEq x y :=
  fun n h => match n with | .zero => trivial | .succ n => h n n.lt_succ_self

@[rocq_alias later_equivI_2]
theorem later_equiv_internalEq_mpr [OFE A] (x y : A) :
    ▷ internalEq x y ⊢ internalEq (Later.next x) (Later.next y) := by
  intro n hP m hlt
  cases n with
  | zero => omega
  | succ n => exact .le hP (Nat.le_of_lt_succ hlt)

/-! ## CMRA validity -/

@[rocq_alias siProp_cmra_valid]
def cmraValid [CMRA A] (a : A) : SiProp where
  holds n := ✓{n} a
  closed h hle := CMRA.validN_of_le hle h

@[rocq_alias cmra_valid_ne]
instance instNonExpansiveCmraValid [CMRA A] : NonExpansive (cmraValid (A := A)) where
  ne _ _ _ h _ hle := ⟨CMRA.validN_ne (Dist.le h hle), CMRA.validN_ne (Dist.le h hle).symm⟩

@[rocq_alias cmra_valid_intro]
theorem cmraValid_intro [CMRA A] {P : SiProp} {a : A} (h : CMRA.Valid a) :
    P ⊢ cmraValid a :=
  fun n _ => (CMRA.valid_iff_validN.mp h) n

@[rocq_alias cmra_valid_elim]
theorem cmraValid_elim [CMRA A] {a : A} : cmraValid a ⊢ ⌜✓{0} a⌝ :=
  fun _ => CMRA.validN_of_le (Nat.zero_le _)

@[rocq_alias cmra_valid_weaken]
theorem cmraValid_weaken [CMRA A] {a b : A} : cmraValid (a • b) ⊢ cmraValid a :=
  fun _ => CMRA.validN_op_left

@[rocq_alias valid_entails]
theorem cmraValid_entails_iff [CMRA A] [CMRA B] {a : A} {b : B} :
    (cmraValid a ⊢ cmraValid b) ↔ ∀ n, ✓{n} a → ✓{n} b :=
  .rfl

instance cmraValid_timeless [CMRA A] [CMRA.Discrete A] {a : A} :
    Timeless (cmraValid a : SiProp) where
  timeless := fun n h => by
    cases n with
    | zero => left; trivial
    | succ n =>
      right
      exact (CMRA.discrete_valid (CMRA.validN_of_le (Nat.zero_le n) h)).validN

/-! ## Soundness lemmas -/

@[rocq_alias pure_soundness]
theorem pure_soundness {φ : Prop} (h : True ⊢@{SiProp} ⌜φ⌝) : φ := h 0 trivial

@[rocq_alias internal_eq_soundness]
theorem internalEq_soundness [OFE A] {x y : A} (h : True ⊢@{SiProp} internalEq x y) : x ≡ y :=
  equiv_dist.mpr fun n => h n trivial

@[rocq_alias later_soundness]
theorem later_soundness {P : SiProp} (h : True ⊢ ▷ P) : True ⊢ P := fun n _ => h (n + 1) trivial

end SiProp
end Iris
