/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.BI.BI
import Iris.BI.Extensions
import Iris.BI.Classes
import Iris.BI.DerivedLaws
import Iris.Algebra.CMRA
import Iris.Std.RocqAlias

/-!
# Step-Indexed Propositions (siProp)

The type `SiProp` defines "plain" step-indexed propositions, on which we define the
usual connectives of higher-order logic and prove that these satisfy the axioms of BI.

We pick `∗` and `-∗` to coincide with `∧` and `→`, and `<pers>` to be the identity.
This makes `SiProp` an affine BI where every proposition is persistent.
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

private def siPure (φ : Prop) : SiProp where
  holds _ := φ
  closed h _ := h

private def siAnd (P Q : SiProp) : SiProp where
  holds n := P.holds n ∧ Q.holds n
  closed h hle := ⟨P.closed h.1 hle, Q.closed h.2 hle⟩

private def siOr (P Q : SiProp) : SiProp where
  holds n := P.holds n ∨ Q.holds n
  closed h hle := h.imp (P.closed · hle) (Q.closed · hle)

private def downclose (Pi : Nat → Prop) : SiProp where
  holds n := ∀ n', n' ≤ n → Pi n'
  closed h hle n' hn' := h n' (Nat.le_trans hn' hle)

private def siImpl (P Q : SiProp) : SiProp :=
  downclose fun n => P.holds n → Q.holds n

private def siSForall (Φ : SiProp → Prop) : SiProp where
  holds n := ∀ P, Φ P → P.holds n
  closed h hle P hP := P.closed (h P hP) hle

private def siSExists (Φ : SiProp → Prop) : SiProp where
  holds n := ∃ P, Φ P ∧ P.holds n
  closed := fun ⟨P, hP, hh⟩ hle => ⟨P, hP, P.closed hh hle⟩

private def siLater (P : SiProp) : SiProp where
  holds n := match n with | 0 => True | n + 1 => P.holds n
  closed := by
    intro n₁ n₂ h hle
    cases n₂ with
    | zero => trivial
    | succ n₂ =>
      cases n₁ with
      | zero => omega
      | succ n₁ => exact P.closed h (Nat.le_of_succ_le_succ hle)

/-! ## OFE / COFE / BIBase instances -/

@[rocq_alias siProp_entails]
protected def Entails (P Q : SiProp) : Prop := ∀ n, P.holds n → Q.holds n

instance : OFE SiProp where
  Equiv P Q := ∀ n, P.holds n ↔ Q.holds n
  Dist n P Q := ∀ m, m ≤ n → (P.holds m ↔ Q.holds m)
  dist_eqv := ⟨
    fun _ _ _ => Iff.rfl,
    fun h _ hle => (h _ hle).symm,
    fun h₁ h₂ _ hle => (h₁ _ hle).trans (h₂ _ hle)⟩
  equiv_dist := ⟨
    fun heq _ _ _ => heq _,
    fun h n => h n n Nat.le.refl⟩
  dist_lt h hm _ hle := h _ (Nat.le_trans hle (Nat.le_of_lt hm))

instance : IsCOFE SiProp where
  compl c := ⟨fun n => (c n).holds n, fun {n₁ _} h hle =>
    (c.cauchy hle _ Nat.le.refl).mp ((c n₁).closed h hle)⟩
  conv_compl {_ c} _ hle :=
    (c.cauchy hle _ Nat.le.refl).symm

instance : BIBase SiProp where
  Entails := SiProp.Entails
  emp := siPure True
  pure := siPure
  and := siAnd
  or := siOr
  imp := siImpl
  sForall := siSForall
  sExists := siSExists
  sep := siAnd
  wand := siImpl
  persistently P := P
  later := siLater

instance : Std.Preorder (BIBase.Entails (PROP := SiProp)) where
  refl _ h := h
  trans h₁ h₂ n h := h₂ n (h₁ n h)

/-! ## BI instance -/

@[rocq_alias siPropI]
instance instBI : BI SiProp where
  entails_preorder := inferInstance
  equiv_iff := ⟨
    fun heq => ⟨fun n => (heq n).mp, fun n => (heq n).mpr⟩,
    fun ⟨hPQ, hQP⟩ n => ⟨hPQ n, hQP n⟩⟩
  -- NonExpansive
  and_ne.ne _ _ _ h₁ _ _ h₂ m hle :=
    ⟨And.imp (h₁ m hle).mp (h₂ m hle).mp, And.imp (h₁ m hle).mpr (h₂ m hle).mpr⟩
  or_ne.ne _ _ _ h₁ _ _ h₂ m hle :=
    ⟨Or.imp (h₁ m hle).mp (h₂ m hle).mp, Or.imp (h₁ m hle).mpr (h₂ m hle).mpr⟩
  imp_ne.ne _ _ _ h₁ _ _ h₂ m hle :=
    ⟨fun hpq n' hn' hP =>
      (h₂ n' (Nat.le_trans hn' hle)).mp (hpq n' hn' ((h₁ n' (Nat.le_trans hn' hle)).mpr hP)),
     fun hpq n' hn' hP =>
      (h₂ n' (Nat.le_trans hn' hle)).mpr (hpq n' hn' ((h₁ n' (Nat.le_trans hn' hle)).mp hP))⟩
  sForall_ne := by
    intro n P₁ P₂ ⟨hlr₁, hlr₂⟩ m hle
    constructor
    · intro h Q hQ
      obtain ⟨P, hP, hPQ⟩ := hlr₂ Q hQ
      exact (hPQ _ hle).mp (h P hP)
    · intro h P hP
      obtain ⟨Q, hQ, hPQ⟩ := hlr₁ P hP
      exact (hPQ _ hle).mpr (h Q hQ)
  sExists_ne := by
    intro n P₁ P₂ ⟨hlr₁, hlr₂⟩ m hle
    constructor
    · rintro ⟨P, hP, hPm⟩
      obtain ⟨Q, hQ, hPQ⟩ := hlr₁ P hP
      exact ⟨Q, hQ, (hPQ _ hle).mp hPm⟩
    · rintro ⟨Q, hQ, hQm⟩
      obtain ⟨P, hP, hPQ⟩ := hlr₂ Q hQ
      exact ⟨P, hP, (hPQ _ hle).mpr hQm⟩
  sep_ne.ne _ _ _ h₁ _ _ h₂ m hle :=
    ⟨And.imp (h₁ m hle).mp (h₂ m hle).mp, And.imp (h₁ m hle).mpr (h₂ m hle).mpr⟩
  wand_ne.ne _ _ _ h₁ _ _ h₂ m hle :=
    ⟨fun hpq n' hn' hP =>
      (h₂ n' (Nat.le_trans hn' hle)).mp (hpq n' hn' ((h₁ n' (Nat.le_trans hn' hle)).mpr hP)),
     fun hpq n' hn' hP =>
      (h₂ n' (Nat.le_trans hn' hle)).mpr (hpq n' hn' ((h₁ n' (Nat.le_trans hn' hle)).mp hP))⟩
  persistently_ne.ne _ _ _ h m hle := h m hle
  later_ne.ne _ _ _ h m hle := by
    cases m with
    | zero => exact Iff.rfl
    | succ k => exact h k (Nat.le_trans (Nat.le_succ k) hle)
  -- Pure
  pure_intro h _ _ := h
  pure_elim' h _ hφ := h hφ _ trivial
  -- And
  and_elim_l _ h := h.1
  and_elim_r _ h := h.2
  and_intro h₁ h₂ _ h := ⟨h₁ _ h, h₂ _ h⟩
  -- Or
  or_intro_l _ h := Or.inl h
  or_intro_r _ h := Or.inr h
  or_elim h₁ h₂ _ h := h.elim (h₁ _) (h₂ _)
  -- Impl
  imp_intro := fun {P _ _} h n hP n' hle hQ => h n' ⟨P.closed hP hle, hQ⟩
  imp_elim h n hPQ := h n hPQ.1 n Nat.le.refl hPQ.2
  -- Forall / Exists
  sForall_intro h _ hP P hΨ := h P hΨ _ hP
  sForall_elim h _ hF := hF _ h
  sExists_intro h _ hP := ⟨_, h, hP⟩
  sExists_elim h := fun _ ⟨_, hΨ, hP⟩ => h _ hΨ _ hP
  -- Sep / Wand (= And / Impl for siProp)
  sep_mono h₁ h₂ _ hPQ := ⟨h₁ _ hPQ.1, h₂ _ hPQ.2⟩
  emp_sep := ⟨fun _ hPQ => hPQ.2, fun _ hP => ⟨trivial, hP⟩⟩
  sep_symm _ hPQ := ⟨hPQ.2, hPQ.1⟩
  sep_assoc_l _ hPQR := ⟨hPQR.1.1, hPQR.1.2, hPQR.2⟩
  wand_intro := fun {P _ _} h n hP n' hle hQ => h n' ⟨P.closed hP hle, hQ⟩
  wand_elim h n hPQ := h n hPQ.1 n Nat.le.refl hPQ.2
  -- Persistently (identity for siProp)
  persistently_mono h := h
  persistently_idem_2 _ h := h
  persistently_emp_2 _ h := h
  persistently_and_2 _ h := h
  persistently_sExists_1 := fun _ ⟨P, hΨ, hPn⟩ => ⟨_, ⟨P, rfl⟩, hΨ, hPn⟩
  persistently_absorb_l _ h := h.1
  persistently_and_l _ h := h
  -- Later
  later_mono h n hlP := by
    cases n with
    | zero => trivial
    | succ => exact h _ hlP
  later_intro {P} n hP := by
    cases n with
    | zero => trivial
    | succ => exact P.closed hP (Nat.le_succ _)
  later_sForall_2 := by
    intro Φ n h
    cases n with
    | zero => trivial
    | succ n =>
      intro P hΦP
      exact h (siImpl (siPure (Φ P)) (siLater P)) ⟨P, rfl⟩ (n + 1) Nat.le.refl hΦP
  later_sExists_false := by
    intro Φ n h
    cases n with
    | zero => exact Or.inl trivial
    | succ n =>
      obtain ⟨P, hΦP, hPn⟩ := h
      exact Or.inr ⟨_, ⟨P, rfl⟩, hΦP, hPn⟩
  later_sep := by
    intro P Q; constructor
    · rintro (_|n) h
      · exact ⟨trivial, trivial⟩
      · exact h
    · rintro (_|n) ⟨hP, hQ⟩
      · trivial
      · exact ⟨hP, hQ⟩
  later_persistently := ⟨fun _ h => h, fun _ h => h⟩
  later_false_em {P} := by
    intro n hP
    cases n with
    | zero => exact Or.inl trivial
    | succ n =>
      refine Or.inr fun n' hle hF => ?_
      cases n' with
      | zero => exact P.closed hP (Nat.zero_le _)
      | succ => exact absurd hF id

/-! ## Extra BI instances -/

@[rocq_alias siProp_affine]
instance instBIAffine : BIAffine SiProp where
  affine _ := { affine := fun _ _ => trivial }

@[rocq_alias siProp_pure_forall]
instance instBIPureForall : Iris.BI.BIPureForall SiProp where
  pure_forall_2 φ _ h := fun a => h _ ⟨a, rfl⟩

@[rocq_alias siProp_later_contractive]
instance instBILaterContractive : BILaterContractive SiProp where
  distLater_dist {n P Q} h := by
    intro m hle
    show (siLater P).holds m ↔ (siLater Q).holds m
    cases m with
    | zero => exact Iff.rfl
    | succ k =>
      show P.holds k ↔ Q.holds k
      exact h k (Nat.lt_of_succ_le hle) k Nat.le.refl

@[rocq_alias siProp_persistent]
instance instPersistent (P : SiProp) : Persistent P where
  persistent := fun _ h => h

/-! ## Internal equality -/

@[rocq_alias siProp_internal_eq]
def internalEq [OFE A] (a₁ a₂ : A) : SiProp where
  holds n := a₁ ≡{n}≡ a₂
  closed h hle := Dist.le h hle

@[rocq_alias internal_eq_ne]
instance internalEq_ne [OFE A] : NonExpansive₂ (internalEq (A := A)) where
  ne _ _ _ h₁ _ _ h₂ _ hle :=
    ⟨fun heq => (Dist.le h₁ hle).symm.trans (heq.trans (Dist.le h₂ hle)),
     fun heq => (Dist.le h₁ hle).trans (heq.trans (Dist.le h₂ hle).symm)⟩

@[rocq_alias internal_eq_refl]
theorem internalEq_refl [OFE A] (P : SiProp) (a : A) : P ⊢ internalEq a a :=
  fun _ _ => Dist.rfl

@[rocq_alias internal_eq_rewrite]
theorem internalEq_rewrite [OFE A] (a b : A) (Ψ : A → SiProp)
    [NonExpansive Ψ] : internalEq a b ⊢ Ψ a → Ψ b := by
  intro n hab n' hle hΨa
  have h : Ψ a ≡{n'}≡ Ψ b := NonExpansive.ne (Dist.le hab hle)
  exact (h n' Nat.le.refl).mp hΨa

@[rocq_alias prop_ext_2]
theorem prop_ext_2 (P Q : SiProp) : (P → Q) ∧ (Q → P) ⊢ internalEq P Q :=
  fun _ ⟨hPQ, hQP⟩ n' hle => ⟨hPQ n' hle, hQP n' hle⟩

@[rocq_alias internal_eq_entails]
theorem internalEq_entails [OFE A] [OFE B] (a₁ a₂ : A) (b₁ b₂ : B) :
    (internalEq a₁ a₂ ⊢ internalEq b₁ b₂) ↔ (∀ n, a₁ ≡{n}≡ a₂ → b₁ ≡{n}≡ b₂) :=
  Iff.rfl

@[rocq_alias fun_extI]
theorem fun_extI [OFEFun (B : A → _)] (g₁ g₂ : (x : A) → B x) :
    (∀ (i : A), internalEq (g₁ i) (g₂ i)) ⊢ internalEq g₁ g₂ :=
  fun _ h x => h _ ⟨x, rfl⟩

@[rocq_alias sig_equivI_1]
theorem sig_equivI_1 [OFE A] (P : A → Prop) (x y : { a : A // P a }) :
    internalEq x.val y.val ⊢ internalEq x y :=
  fun _ h => h

@[rocq_alias discrete_eq_1]
theorem discrete_eq_1 [OFE A] (a b : A) [Std.TCOr (DiscreteE a) (DiscreteE b)] :
    internalEq a b ⊢ ⌜a ≡ b⌝ := by
  intro n hab
  cases ‹Std.TCOr (DiscreteE a) (DiscreteE b)› with
  | l => exact DiscreteE.discrete (hab.le (Nat.zero_le _))
  | r => exact (DiscreteE.discrete (hab.le (Nat.zero_le _)).symm).symm

@[rocq_alias later_equivI_1]
theorem later_equivI_1 [OFE A] (x y : A) :
    internalEq (Later.next x) (Later.next y) ⊢ ▷ internalEq x y := by
  intro n heq
  cases n with
  | zero => trivial
  | succ n => exact heq n (Nat.lt_succ_self n)

@[rocq_alias later_equivI_2]
theorem later_equivI_2 [OFE A] (x y : A) :
    ▷ internalEq x y ⊢ internalEq (Later.next x) (Later.next y) := by
  intro n hP m hlt
  cases n with
  | zero => omega
  | succ n => exact Dist.le hP (Nat.le_of_lt_succ hlt)

/-! ## CMRA validity -/

@[rocq_alias siProp_cmra_valid]
def cmraValid [CMRA A] (a : A) : SiProp where
  holds n := ✓{n} a
  closed h hle := CMRA.validN_of_le hle h

@[rocq_alias cmra_valid_ne]
instance cmraValid_ne [CMRA A] : NonExpansive (cmraValid (A := A)) where
  ne _ _ _ h _ hle :=
    ⟨fun hv => CMRA.validN_ne (Dist.le h hle) hv,
     fun hv => CMRA.validN_ne (Dist.le h hle).symm hv⟩

@[rocq_alias cmra_valid_intro]
theorem cmraValid_intro [CMRA A] (P : SiProp) (a : A) (h : CMRA.Valid a) :
    P ⊢ cmraValid a :=
  fun n _ => (CMRA.valid_iff_validN.mp h) n

@[rocq_alias cmra_valid_elim]
theorem cmraValid_elim [CMRA A] (a : A) : cmraValid a ⊢ ⌜✓{0} a⌝ :=
  fun _ hv => CMRA.validN_of_le (Nat.zero_le _) hv

@[rocq_alias cmra_valid_weaken]
theorem cmraValid_weaken [CMRA A] (a b : A) : cmraValid (a • b) ⊢ cmraValid a :=
  fun _ hv => CMRA.validN_op_left hv

@[rocq_alias valid_entails]
theorem valid_entails [CMRA A] [CMRA B] (a : A) (b : B) :
    (cmraValid a ⊢ cmraValid b) ↔ ∀ n, ✓{n} a → ✓{n} b :=
  Iff.rfl

/-! ## Soundness lemmas -/

@[rocq_alias pure_soundness]
theorem pure_soundness {φ : Prop} (h : True ⊢@{SiProp} ⌜φ⌝) : φ :=
  h 0 trivial

@[rocq_alias internal_eq_soundness]
theorem internalEq_soundness [OFE A] {x y : A}
    (h : True ⊢@{SiProp} internalEq x y) : x ≡ y :=
  equiv_dist.mpr fun n => h n trivial

@[rocq_alias later_soundness]
theorem later_soundness {P : SiProp} (h : True ⊢ ▷ P) : True ⊢ P := fun n _ => h (n + 1) trivial

end SiProp
end Iris
