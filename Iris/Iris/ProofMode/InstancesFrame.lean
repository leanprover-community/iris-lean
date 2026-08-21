/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Alvin Tang
-/
module

public import Iris.BI
public import Iris.ProofMode.Classes
public import Iris.ProofMode.ClassesMake
public import Iris.ProofMode.Expr
public import Iris.ProofMode.SynthInstance
public import Iris.Std.TC

public meta section

register_option iris.frame.instantiateExists : Bool := {
  defValue := true
  descr := "When set as `true`, `iframe` may instantiate existential \
    quantifiers in the goal while framing. Set to `false` to allow framing \
    below existential quantifiers without instantiating any existentially \
    quantified variables."
}

end

@[expose] public section

namespace Iris.ProofMode
open Qq Iris.BI Iris.Std

/-
When framing [R] against itself, we leave [True] if possible since it is a weaker goal.
Otherwise we leave [emp]. Only if all those options fail, we start decomposing [R].
-/
@[ipm_backtrack, rocq_alias frame_here_absorbing]
instance (priority := high + 10) frame_here_absorbing [BI PROP]
    p (R : PROP) [QuickAbsorbing R] :
    Frame p R R iprop(True) where
  frame := calc
    _ ⊢ True ∗ □?p R := sep_comm.mp
    _ ⊢ True ∗ R     := sep_mono_right intuitionisticallyIf_elim
    _ ⊢ R            := quick_absorbing.absorbing

@[ipm_backtrack, rocq_alias frame_here]
instance (priority := high + 5) frame_here [BI PROP] p (R : PROP) :
    Frame p R R iprop(emp) where
  frame := sep_emp.1.trans intuitionisticallyIf_elim

@[ipm_backtrack, rocq_alias frame_affinely_here_absorbing]
instance (priority := high + 10) frame_affinely_here_absorbing [BI PROP] p (R : PROP)
    [QuickAbsorbing R] : Frame p iprop(<affine> R) R iprop(True) where
  frame := calc
    _ ⊢ True ∗ □?p <affine> R := sep_comm.mp
    _ ⊢ True ∗ R              := sep_mono_right <| intuitionisticallyIf_elim.trans affinely_elim
    _ ⊢ R                     := quick_absorbing.absorbing

@[ipm_backtrack, rocq_alias frame_affinely_here]
instance (priority := high + 10) frame_affinely_here [BI PROP] p (R : PROP) :
    Frame p iprop(<affine> R) R iprop(emp) where
  frame := calc
    _ ⊢ □?p <affine> R := sep_emp.mp
    _ ⊢ <affine> R     := intuitionisticallyIf_elim
    _ ⊢ R              := affinely_elim

@[ipm_backtrack, rocq_alias frame_here_pure_persistent]
instance frame_here_pure_persistent [BI PROP] {a : Bool} {φ : Prop} {Q : PROP}
    [hfp : FromPure a Q .in φ] : Frame true iprop(⌜φ⌝) Q iprop(emp) where
  frame := calc
    _ ⊢ □ ⌜φ⌝               := sep_emp.mp
    _ ⊢@{PROP} <affine> ⌜φ⌝ := affinely_of_intuitionistically
    _ ⊢ <affine>?a ⌜φ⌝      := affinely_affinelyIf
    _ ⊢ Q                   := hfp.1

@[ipm_backtrack, rocq_alias frame_here_pure]
instance frame_here_pure [BI PROP] {a : Bool} {φ : Prop} {Q : PROP}
    [h1 : FromPure a Q .in φ] [hor : TCOr (TCEq a false) (BIAffine PROP)] :
    Frame false iprop(⌜φ⌝) Q iprop(emp) where
  frame :=
    sep_emp.1.trans <|
    match hor with
    | @TCOr.l _ _ heq => by cases heq; exact h1.1
    | TCOr.r =>
      calc
        _ ⊢ <affine> ⌜φ⌝   := affinely_intro .rfl
        _ ⊢ <affine>?a ⌜φ⌝ := affinely_affinelyIf
        _ ⊢ Q              := h1.1

@[ipm_backtrack, rocq_alias frame_wand]
instance frame_wand [BI PROP] p (R P1 P2 Q2 : PROP)
    [h : FrameInstantiateExistDisabled p R P2 Q2] :
    Frame p R iprop(P1 -∗ P2) iprop(P1 -∗ Q2) where
  frame := by
    refine wand_intro ?_
    calc
      _ ⊢ □?p R ∗ (P1 -∗ Q2) ∗ P1 := sep_assoc.mp
      _ ⊢ □?p R ∗ Q2              := sep_mono_right wand_elim_left
      _ ⊢ P2                      := h.frame_instantiatiate_exist_disabled.frame

@[ipm_backtrack, rocq_alias frame_affinely]
instance frame_affinely [BI PROP] p (R P Q Q' : PROP)
    [hor : TCOr (TCEq p true) (QuickAffine R)]
    [h1 : Frame p R P Q] [h2 : MakeAffinely Q Q'] :
    Frame p R iprop(<affine> P) Q' where
  frame :=
    let h_aff : Affine iprop(□?p R) := match hor with
      | @TCOr.l _ _ heq => by cases heq; exact inferInstance
      | @TCOr.r _ _ hq => by have := hq.quick_affine; exact inferInstance
    calc
      _ ⊢ □?p R ∗ <affine> Q          := sep_mono_right h2.make_affinely.mpr
      _ ⊢ <affine> □?p R ∗ <affine> Q := sep_mono_left (affine_affinely _).symm.mp
      _ ⊢ <affine> (□?p R ∗ Q)        := affinely_sep_mpr
      _ ⊢ <affine> P                  := affinely_mono h1.frame

@[ipm_backtrack, rocq_alias frame_intuitionistically]
instance frame_intuitionistically [BI PROP] (R P Q Q' : PROP)
    [h1 : Frame true R P Q] [h2 : MakeIntuitionistically Q Q'] :
    Frame true R iprop(□ P) Q' where
  frame := calc
    _ ⊢ □ R ∗ □ Q   := sep_mono_right h2.make_intuitionistically.mpr
    _ ⊢ □ □ R ∗ □ Q := sep_mono_left intuitionistically_idem.mpr
    _ ⊢ □ (□ R ∗ Q) := intuitionistically_sep_mpr
    _ ⊢ □ P         := intuitionistically_mono h1.frame

@[ipm_backtrack, rocq_alias frame_absorbingly]
instance frame_absorbingly [BI PROP] p (R P Q Q' : PROP)
    [h1 : Frame p R P Q] [h2 : MakeAbsorbingly Q Q'] :
    Frame p R iprop(<absorb> P) Q' where
  frame := calc
    _ ⊢ □?p R ∗ <absorb> Q   := sep_mono_right h2.make_absorbingly.mpr
    _ ⊢ <absorb> (□?p R ∗ Q) := absorbingly_sep_right.mp
    _ ⊢ <absorb> P           := absorbingly_mono h1.frame

@[ipm_backtrack, rocq_alias frame_persistently]
instance frame_persistently [BI PROP] (R P Q Q' : PROP)
    [h1 : Frame true R P Q] [h2 : MakePersistently Q Q'] :
    Frame true R iprop(<pers> P) Q' where
  frame := calc
    _ ⊢ □ R ∗ <pers> Q        := sep_mono_right h2.make_persistently.mpr
    _ ⊢ <pers> □ R ∗ <pers> Q := sep_mono_left persistent
    _ ⊢ <pers> (□ R ∗ Q)      := persistently_sep_mpr
    _ ⊢ <pers> P              := persistently_mono h1.frame

@[ipm_backtrack, rocq_alias frame_forall]
instance frame_forall {α} [BI PROP] p R (Φ Ψ : α → PROP)
    [h : ∀ a, FrameInstantiateExistDisabled p R (Φ a) (Ψ a)] :
    Frame p R iprop(∀ x, Φ x) iprop(∀ x, Ψ x) where
  frame := forall_intro λ a =>
    (sep_mono_right (forall_elim a)).trans (h a).frame_instantiatiate_exist_disabled.frame

@[ipm_backtrack, rocq_alias frame_impl_persistent]
instance frame_impl_persistent [BI PROP] (R P1 P2 Q2 : PROP)
    [h : FrameInstantiateExistDisabled true R P2 Q2] :
    Frame true R iprop(P1 → P2) iprop(P1 → Q2) where
  frame := by
    refine imp_intro ?_
    calc
      _ ⊢ (<pers> R ∧ (P1 → Q2)) ∧ P1 :=
          and_mono_left persistently_and_intuitionistically_sep_left.mpr
      _ ⊢ <pers> R ∧ (P1 → Q2) ∧ P1   := and_assoc.mp
      _ ⊢ <pers> R ∧ Q2               := and_mono_right <| and_comm.mp.trans imp_elim_right
      _ ⊢ □ R ∗ Q2                    := persistently_and_intuitionistically_sep_left.mp
      _ ⊢ P2                          := h.frame_instantiatiate_exist_disabled.frame

/-
You may wonder why this uses [Persistent] and not [QuickPersistent].
The reason is that [QuickPersistent] is not needed anywhere else, and even without
[QuickPersistent],
this instance avoids quadratic complexity: we usually use the [Quick*] classes to not traverse the
same term over and over again, but here [P1] is encountered at most once. It is hence not worth
adding a new typeclass just for this extremely rarely used instance.
-/
@[ipm_backtrack, rocq_alias frame_impl]
instance frame_impl [BI PROP] (R P1 P2 Q2 : PROP)
    [hp : Persistent P1] [ha : QuickAbsorbing P1]
    [h : FrameInstantiateExistDisabled false R P2 Q2] :
    Frame false R iprop(P1 → P2) iprop(P1 → Q2) where
  frame := by
    letI := ha.quick_absorbing
    refine imp_intro ?_
    calc
      _ ⊢ (R ∗ (P1 → Q2)) ∗ <affine> P1 := persistent_and_affinely_sep_right.mp
      _ ⊢ R ∗ (P1 → Q2) ∗ <affine> P1   := sep_assoc.mp
      _ ⊢ R ∗ Q2                        := sep_mono_right ?_
      _ ⊢ P2                            := h.frame_instantiatiate_exist_disabled.frame
    calc
      _ ⊢ <affine> P1 ∗ (P1 → Q2) := sep_comm.mp
      _ ⊢ P1 ∧ (P1 → Q2)          := persistent_and_affinely_sep_left.mpr
      _ ⊢ Q2                      := imp_elim_right

@[ipm_backtrack, rocq_alias frame_later]
instance frame_later [BI PROP] p (R R' P Q Q' : PROP)
    [h1 : IntoLaterN (progress := false) (only_head := true) 1 R' R]
    [h2 : Frame p R P Q] [h3 : MakeLaterN 1 Q Q'] :
    Frame p R' iprop(▷ P) Q' where
  frame := calc
    _ ⊢ □?p R' ∗ ▷^[1]Q                                     := sep_mono_right h3.make_laterN.mpr
    _ ⊢ ▷ □?p Nat.repeat later 0 R ∗ ▷^[1]Q                :=
        sep_mono_left <| (intuitionisticallyIf_mono h1.1).trans later_intuitionisticallyIf_2
    _ ⊢ ▷ (□?p Nat.repeat later 0 R ∗ Nat.repeat later 0 Q) := later_sep.mpr
    _ ⊢ ▷ P                                                 := later_mono h2.frame

@[ipm_backtrack, rocq_alias frame_laterN]
instance frame_laterN [BI PROP] p n (R R' P Q Q' : PROP)
    [h1 : IntoLaterN (progress := false) (only_head := true) n R' R]
    [h2 : Frame p R P Q] [h3 : MakeLaterN n Q Q'] :
    Frame p R' iprop(▷^[n] P) Q' where
  frame := calc
    _ ⊢ □?p R' ∗ ▷^[n]Q      := sep_mono_right h3.make_laterN.mpr
    _ ⊢ ▷^[n]□?p R ∗ ▷^[n]Q :=
        sep_mono_left <| (intuitionisticallyIf_mono h1.1).trans (laterN_intuitionisticallyIf n)
    _ ⊢ ▷^[n](□?p R ∗ Q)     := (laterN_sep n).mpr
    _ ⊢ ▷^[n]P               := laterN_mono n h2.frame

@[ipm_backtrack, rocq_alias frame_bupd]
instance frame_bupd [BI PROP] [BIUpdate PROP] p (R P Q Q' : PROP)
    [h : Frame p R P Q] [h2 : MakeBUpd Q Q'] : Frame p R iprop(|==> P) Q' where
  frame := calc
    _ ⊢ □?p R ∗ |==> Q   := sep_mono_right h2.make_bupd.mpr
    _ ⊢ |==> (□?p R ∗ Q) := bupd_frame_left
    _ ⊢ |==> P           := BIUpdate.mono h.frame

@[ipm_backtrack, rocq_alias frame_fupd]
instance frame_fupd [BI PROP] [BIFUpdate PROP] p (E1 E2 : CoPset) (R P Q Q' : PROP)
    [h : Frame p R P Q] [h2 : MakeFUpd E1 E2 Q Q'] : Frame p R iprop(|={E1,E2}=> P) Q' where
  frame := calc
    _ ⊢ □?p R ∗ |={E1, E2}=> Q := sep_mono_right h2.make_fupd.mpr
    _ ⊢ |={E1, E2}=> □?p R ∗ Q := fupd_frame_left
    _ ⊢ |={E1, E2}=> P         := BIFUpdate.mono h.frame

@[ipm_backtrack, rocq_alias frame_except_0]
instance frame_except_0 [BI PROP] p (R P Q Q' : PROP)
    [h1 : Frame p R P Q] [h2 : MakeExcept0 Q Q'] : Frame p R iprop(◇ P) Q' where
  frame := calc
    _ ⊢ □?p R ∗ ◇ Q    := sep_mono_right h2.make_except0.mpr
    _ ⊢ ◇ □?p R ∗ ◇ Q := sep_mono_left except0_intro
    _ ⊢ ◇ (□?p R ∗ Q)  := except0_sep.mpr
    _ ⊢ ◇ P            := except0_mono h1.frame

theorem frame_embed_core [BI PROP1] [BI PROP2] [BiEmbed PROP1 PROP2]
    {p : Bool} {R P Q : PROP1} {Q' : PROP2}
    (h1 : Frame p R P Q) (h2 : MakeEmbed Q Q') :
    □?p ⎡R⎤ ∗ Q' ⊢ ⎡P⎤ := calc
  _ ⊢ □?p ⎡R⎤ ∗ ⎡Q⎤ := sep_mono_right h2.make_embed.mpr
  _ ⊢ ⎡□?p R⎤ ∗ ⎡Q⎤ := sep_mono_left <| embed_intuitionistically_if_2 R p
  _ ⊢ ⎡□?p R ∗ Q⎤   := (embed_sep _ _).mpr
  _ ⊢ ⎡P⎤           := embed_mono h1.frame

@[ipm_backtrack, rocq_alias frame_embed]
instance frame_embed [BI PROP1] [BI PROP2] [BiEmbed PROP1 PROP2]
    (p : Bool) (R P Q : PROP1) (Q' : PROP2)
    [h1 : Frame p R P Q] [h2 : MakeEmbed Q Q'] :
    Frame p iprop(⎡R⎤) iprop(⎡P⎤) Q' where
  frame := frame_embed_core h1 h2

@[ipm_backtrack, rocq_alias frame_pure_embed]
instance (priority := default - 1) frame_pure_embed
    [BI PROP1] [BI PROP2] [BiEmbed PROP1 PROP2]
    (p : Bool) (φ : Prop) (P Q : PROP1) (Q' : PROP2)
    [h1 : Frame p iprop(⌜φ⌝) P Q] [h2 : MakeEmbed Q Q'] :
    Frame p iprop(⌜φ⌝) iprop(⎡P⎤) Q' where
  frame := (sep_mono_left <| intuitionisticallyIf_mono (embed_pure φ).mpr).trans
    (frame_embed_core h1 h2)

@[ipm_backtrack, rocq_alias frame_eq_embed]
instance (priority := default - 1) frame_eq_embed
    [Sbi P1] [Sbi P2] [BiEmbed P1 P2] [BiEmbedSbi P1 P2]
    (p : Bool) {A : Type _} [OFE A] (a b : A) (P Q : P1) (Q' : P2)
    [h1 : Frame p iprop(a ≡ b) P Q] [h2 : MakeEmbed Q Q'] :
    Frame p iprop(a ≡ b) iprop(⎡P⎤) Q' where
  frame := (sep_mono_left <| intuitionisticallyIf_mono (embed_internal_eq a b).mpr).trans
    (frame_embed_core h1 h2)

@[ipm_backtrack, rocq_alias frame_texist]
instance frame_texist {TT : Tele} [BI PROP] p (R : PROP) (Φ Ψ : TT.Arg → PROP)
    [h : ∀ x, Frame p R (Φ x) (Ψ x)] :
    Frame p R iprop(∃.. x, Φ x) iprop(∃.. x, Ψ x) where
  frame := calc
    _ ⊢ □?p R ∗ ∃ x, Ψ x := sep_mono_right (texist_exist Ψ).mp
    _ ⊢ ∃ x, □?p R ∗ Ψ x := sep_exists_left.mp
    _ ⊢ ∃ x, Φ x         := exists_mono fun x => (h x).frame
    _ ⊢ texist Φ         := (texist_exist Φ).mpr

@[ipm_backtrack, rocq_alias frame_tforall]
instance frame_tforall {TT : Tele} [BI PROP] p (R : PROP) (Φ Ψ : TT.Arg → PROP)
    [h : ∀ x, FrameInstantiateExistDisabled p R (Φ x) (Ψ x)] :
    Frame p R iprop(∀.. x, Φ x) iprop(∀.. x, Ψ x) where
  frame := by
    refine .trans ?_ (tforall_forall Φ).mpr
    refine forall_intro fun x => ?_
    exact (sep_mono_right <| (tforall_forall Ψ).mp.trans <| forall_elim x).trans
      (h x).frame_instantiatiate_exist_disabled.frame

@[ipm_backtrack, rocq_alias frame_big_sepL_cons]
instance frame_bigSepL_cons [BI PROP] {A} p (Φ : Nat → A → PROP)
    (R Q : PROP) (l : List A) (x : A) (l' : List A)
    [hc : IsCons l x l']
    [hf : Frame p R iprop(Φ 0 x ∗ [∗list] k ↦ y ∈ l', Φ (k + 1) y) Q] :
    Frame p R iprop([∗list] k ↦ y ∈ l, Φ k y) Q where
  frame := hc.is_cons ▸ hf.frame.trans BigSepL.bigSepL_cons.mpr

@[ipm_backtrack, rocq_alias frame_big_sepL_app]
instance frame_bigSepL_app [BI PROP] {A} p (Φ : Nat → A → PROP)
    (R Q : PROP) (l l1 l2 : List A)
    [ha : IsApp l l1 l2]
    [hf : Frame p R iprop(([∗list] k ↦ y ∈ l1, Φ k y) ∗
                           [∗list] k ↦ y ∈ l2, Φ (k + l1.length) y) Q] :
    Frame p R iprop([∗list] k ↦ y ∈ l, Φ k y) Q where
  frame := ha.is_app ▸ hf.frame.trans BigSepL.bigSepL_append.mpr

@[ipm_backtrack, rocq_alias frame_big_sepL2_cons]
instance frame_bigSepL2_cons [BI PROP] {A B} p (Φ : Nat → A → B → PROP)
    (R Q : PROP) (l1 : List A) (x1 : A) (l1' : List A)
    (l2 : List B) (x2 : B) (l2' : List B)
    [hc1 : IsCons l1 x1 l1'] [hc2 : IsCons l2 x2 l2']
    [hf : Frame p R iprop(Φ 0 x1 x2 ∗
                          [∗list] k ↦ y1;y2 ∈ l1';l2', Φ (k + 1) y1 y2) Q] :
    Frame p R iprop([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) Q where
  frame := hc1.is_cons ▸ hc2.is_cons ▸ hf.frame.trans BigSepL2.bigSepL2_cons.mpr

@[ipm_backtrack, rocq_alias frame_big_sepL2_app]
instance frame_bigSepL2_app [BI PROP] {A B} p (Φ : Nat → A → B → PROP)
    (R Q : PROP) (l1 l1' l1'' : List A) (l2 l2' l2'' : List B)
    [ha1 : IsApp l1 l1' l1''] [ha2 : IsApp l2 l2' l2'']
    [hf : Frame p R iprop(([∗list] k ↦ y1;y2 ∈ l1';l2', Φ k y1 y2) ∗
                           [∗list] k ↦ y1;y2 ∈ l1'';l2'',
                             Φ (k + l1'.length) y1 y2) Q] :
    Frame p R iprop([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) Q where
  frame := by
    rw [ha1.is_app, ha2.is_app]
    calc
      _ ⊢ ([∗list] k ↦ y1;y2 ∈ l1';l2', Φ k y1 y2) ∗
          [∗list] k ↦ y1;y2 ∈ l1'';l2'', Φ (k + l1'.length) y1 y2 := hf.frame
      _ ⊢ (([∗list] k ↦ y1;y2 ∈ l1'';l2'', Φ (k + l1'.length) y1 y2) ∗
          [∗list] k ↦ y1;y2 ∈ l1';l2', Φ k y1 y2) := sep_symm
      _ ⊢ [∗list] k ↦ x1;x2 ∈ l1' ++ l1'';l2' ++ l2'', Φ k x1 x2 :=
          wand_elim_swap BigSepL2.bigSepL2_app_wand

@[ipm_backtrack, rocq_alias frame_big_sepMS_disj_union]
instance frame_bigSepMS_disjUnion [BI PROP] {MS A}
    [LawfulFiniteMultiSet MS A] p (Φ : A → PROP) (R Q : PROP) (X X1 X2 : MS)
    [hd : IsDisjUnion X X1 X2]
    [hf : Frame p R iprop(([∗mset] y ∈ X1, Φ y) ∗ [∗mset] y ∈ X2, Φ y) Q] :
    Frame p R iprop([∗mset] y ∈ X, Φ y) Q where
  frame := hd.is_disj_union ▸ hf.frame.trans BigSepMS.bigSepMS_disjUnion.mpr

section tactic_theorems

@[rocq_alias maybe_frame_default_persistent]
theorem maybeFrame_default_persistent [BI PROP] (R P : PROP) :
  Frame true R P P where
  frame := sep_elim_right

@[rocq_alias maybe_frame_default]
theorem maybeFrame_default [BI PROP] (R P : PROP)
  [h : TCOr (Affine R) (Absorbing P)]:
  Frame false R P P where
  frame := by simp only [intuitionisticallyIf_false']; exact sep_elim_right

@[rocq_alias frame_sep_persistent_l]
theorem frame_sep_both [BI PROP] (R P1 P2 Q1 Q2 Q' : PROP)
  [h1 : Frame true R P1 Q1] [h2 : Frame true R P2 Q2] [MakeSep Q1 Q2 Q'] :
  Frame true R iprop(P1 ∗ P2) Q' where
  frame := calc
    _ ⊢ □ R ∗ Q1 ∗ Q2         := sep_mono_right make_sep.mpr
    _ ⊢ (□ R ∗ □ R) ∗ Q1 ∗ Q2 := sep_mono_left intuitionistically_sep_idem.mpr
    _ ⊢ (□ R ∗ Q1) ∗ □ R ∗ Q2 := sep_sep_sep_comm.mp
    _ ⊢ P1 ∗ P2               := sep_mono h1.frame h2.frame

@[rocq_alias frame_sep_l]
theorem frame_sep_left [BI PROP] p (R P1 P2 Q Q' : PROP)
    [h1 : Frame p R P1 Q] [h2 : MakeSep Q P2 Q'] :
    Frame p R iprop(P1 ∗ P2) Q' where
  frame := calc
    _ ⊢ □?p R ∗ Q ∗ P2   := sep_mono_right make_sep.mpr
    _ ⊢ (□?p R ∗ Q) ∗ P2 := sep_assoc.mpr
    _ ⊢ P1 ∗ P2          := sep_mono_left h1.frame

@[rocq_alias frame_sep_r]
theorem frame_sep_right [BI PROP] p (R P1 P2 Q Q' : PROP)
    [h1 : Frame p R P2 Q] [h2 : MakeSep P1 Q Q'] :
    Frame p R iprop(P1 ∗ P2) Q' where
  frame := calc
    _ ⊢ □?p R ∗ P1 ∗ Q := sep_mono_right make_sep.mpr
    _ ⊢ P1 ∗ □?p R ∗ Q := sep_left_comm.mp
    _ ⊢ P1 ∗ P2        := sep_mono_right h1.frame

@[rocq_alias frame_and]
theorem frame_and [BI PROP] p (R P1 P2 Q1 Q2 Q' : PROP)
    [h1 : Frame p R P1 Q1] [h2 : Frame p R P2 Q2] [h3 : MakeAnd Q1 Q2 Q'] :
    Frame p R iprop(P1 ∧ P2) Q' where
  frame := and_intro
    ((sep_mono_right (h3.make_and.2.trans and_elim_l)).trans h1.frame)
    ((sep_mono_right (h3.make_and.2.trans and_elim_r)).trans h2.frame)

@[rocq_alias frame_or_spatial, rocq_alias frame_or_persistent]
theorem frame_or [BI PROP] p (R P1 P2 Q1 Q2 Q' : PROP)
    [h1 : Frame p R P1 Q1] [h2 : Frame p R P2 Q2] [h3 : MakeOr Q1 Q2 Q'] :
    Frame p R iprop(P1 ∨ P2) Q' where
  frame := calc
    _ ⊢ □?p R ∗ (Q1 ∨ Q2)       := sep_mono_right h3.make_or.mpr
    _ ⊢ □?p R ∗ Q1 ∨ □?p R ∗ Q2 := sep_or_left.mp
    _ ⊢ P1 ∨ P2                 := or_mono h1.frame h2.frame

@[rocq_alias frame_exist]
theorem frame_exist [BI PROP] {α} (p : Bool) (R : PROP) (Φ : α → PROP)
    (a : α) (Q : PROP) (inst : Frame p R (Φ a) Q) :
    Frame p R iprop(BI.exists Φ) Q where
  frame := inst.frame.trans <| exists_intro a

@[rocq_alias frame_exist_no_instantiate]
theorem frame_exist_no_instantiate [BI PROP] {α} (p : Bool) (R : PROP) (Φ Ψ : α → PROP)
    (inst : ∀ a, Frame p R (Φ a) (Ψ a)) :
    Frame p R iprop(BI.exists Φ) iprop(BI.exists Ψ) where
  frame := sep_exists_left.mp.trans <|
    exists_elim <| fun a => (inst a).frame.trans <| exists_intro a

end tactic_theorems

meta section tactics
open Lean Elab Meta Std

def frameInstantiateExistsEnabled : MetaM Bool := do
  return iris.frame.instantiateExists.get (← getOptions)

def withFrameInstantiateExistsDisabled {α} (x : MetaM α) : MetaM α :=
  withOptions (iris.frame.instantiateExists.set · false) x

theorem frameInstantiateExistsDisabled_of [BI PROP] {p} {R P Q : PROP} (h : Frame p R P Q) :
    FrameInstantiateExistDisabled p R P Q := ⟨h⟩

@[ipm_tactic_instance FrameInstantiateExistDisabled _ _ _ _]
def frameNoInstantiateExist : SynthTactic := λ e => do
  let_expr FrameInstantiateExistDisabled prop bi p R P G := e | return .continue
  have u := e.getAppFn.constLevels![0]!
  have prop : Q(Type u) := prop
  have _bi : Q(BI $prop) := bi
  have p : Q(Bool) := p
  have R : Q($prop) := R
  have P : Q($prop) := P
  have G : Q($prop) := G
  let some inst ← withFrameInstantiateExistsDisabled <|
    synthInstanceRecursiveQ q(Frame $p $R $P $G) | return .continue
  return .success q(frameInstantiateExistsDisabled_of $inst)

/-- corresponds to the MaybeFrame typeclass in Rocq -/
@[rocq_alias MaybeFrame', rocq_alias maybe_frame_frame]
def maybeFrame {prop : Q(Type u)} {bi : Q(BI $prop)} (p : Q(Bool))
    (R P Q : Q($prop)) (f : Option Q(Frame $p $R $P $Q)) :
  MetaM (Option Q(Frame $p $R $P $Q)) := do
  if let some f := f then return some f
  match matchBool p with
  | .inl _ =>
    Q.mvarId!.assign P
    have : $Q =Q $P := ⟨⟩
    return some (q(maybeFrame_default_persistent $R $P))
  | .inr _ =>
    let .some _ ← trySynthInstanceQ q(TCOr (Affine $R) (Absorbing $P))
      | return none
    Q.mvarId!.assign P
    have : $Q =Q $P := ⟨⟩
    return some (q(maybeFrame_default $R $P))

@[ipm_tactic_instance Frame _ _ iprop(_ ∗ _) _]
def frameSep : SynthTactic := λ e => do
  let_expr Frame prop bi p R P _ := e | return .continue
  have u := e.getAppFn.constLevels![0]!
  have prop : Q(Type u) := prop
  have _bi : Q(BI $prop) := bi
  have p : Q(Bool) := p
  have R : Q($prop) := R
  let_expr BI.sep _ _ P1 P2 := P | return .continue
  have P1 : Q($prop) := P1
  have P2 : Q($prop) := P2
  let Q1 : Q($prop) ← mkFreshExprMVarQ q($prop)
  if let .some _ ← synthInstanceRecursiveQ q(Frame $p $R $P1 $Q1) then
    -- if the hyp is persistent, also try to frame it in P2
    if let .inl _ := matchBool p then
      let Q2 : Q($prop) ← mkFreshExprMVarQ q($prop)
      if let .some _ ← synthInstanceRecursiveQ q(Frame $p $R $P2 $Q2) then
        let Q' : Q($prop) ← mkFreshExprMVarQ q($prop)
        let .some _ ← synthInstanceRecursiveQ q(MakeSep $Q1 $Q2 $Q') |
          throwError "MakeSep should always succeed"
        return .success q(frame_sep_both $R $P1 $P2 $Q1 $Q2 $Q')
    let Q' : Q($prop) ← mkFreshExprMVarQ q($prop)
    let .some _ ← synthInstanceRecursiveQ q(MakeSep $Q1 $P2 $Q') |
      throwError "MakeSep should always succeed"
    return .success q(frame_sep_left $p $R $P1 $P2 $Q1 $Q')
  else
    let Q2 : Q($prop) ← mkFreshExprMVarQ q($prop)
    let .some _ ← synthInstanceRecursiveQ q(Frame $p $R $P2 $Q2) |
      return .continue
    let Q' : Q($prop) ← mkFreshExprMVarQ q($prop)
    let .some _ ← synthInstanceRecursiveQ q(MakeSep $P1 $Q2 $Q') |
      throwError "MakeSep should always succeed"
    return .success q(frame_sep_right $p $R $P1 $P2 $Q2 $Q')

@[ipm_tactic_instance Frame _ _ iprop(_ ∧ _) _]
def frameAnd : SynthTactic := λ e => do
  let_expr Frame prop bi p R P _ := e | return .continue
  have u := e.getAppFn.constLevels![0]!
  have prop : Q(Type u) := prop
  have _bi : Q(BI $prop) := bi
  have p : Q(Bool) := p
  have R : Q($prop) := R
  let_expr BI.and _ _ P1 P2 := P | return .continue
  have P1 : Q($prop) := P1
  have P2 : Q($prop) := P2
  let Q1 : Q($prop) ← mkFreshExprMVarQ q($prop)
  let f1 ← synthInstanceRecursiveQ q(Frame $p $R $P1 $Q1)
  let Q2 : Q($prop) ← mkFreshExprMVarQ q($prop)
  let f2 ← synthInstanceRecursiveQ q(Frame $p $R $P2 $Q2)
  if f1.isNone && f2.isNone then return .continue
  let .some _ ← maybeFrame p R P1 Q1 f1 | return .continue
  let .some _ ← maybeFrame p R P2 Q2 f2 | return .continue
  let Q' : Q($prop) ← mkFreshExprMVarQ q($prop)
  let .some _ ← synthInstanceRecursiveQ q(MakeAnd $Q1 $Q2 $Q') |
    throwError "MakeAnd should always succeed"
  return .success q(frame_and $p $R $P1 $P2 $Q1 $Q2 $Q')

def isBITrue (e : Expr) : Bool :=
  let_expr BI.pure _ _ P := e | false
  let_expr True := P | false
  true

@[ipm_tactic_instance Frame _ _ iprop(_ ∨ _) _]
def frameOr : SynthTactic := λ e => do
  let_expr Frame prop bi p R P _ := e | return .continue
  have u := e.getAppFn.constLevels![0]!
  have prop : Q(Type u) := prop
  have _bi : Q(BI $prop) := bi
  have p : Q(Bool) := p
  have R : Q($prop) := R
  let_expr BI.or _ _ P1 P2 := P | return .continue
  have P1 : Q($prop) := P1
  have P2 : Q($prop) := P2
  let Q1 : Q($prop) ← mkFreshExprMVarQ q($prop)
  let f1 ← synthInstanceRecursiveQ q(Frame $p $R $P1 $Q1)
  let Q2 : Q($prop) ← mkFreshExprMVarQ q($prop)
  let f2 ← synthInstanceRecursiveQ q(Frame $p $R $P2 $Q2)
  let Q1 : Q($prop) ← instantiateMVars Q1
  let Q2 : Q($prop) ← instantiateMVars Q2
  -- if no side made progress, framing fails
  if f1.isNone && f2.isNone then return .continue
  -- framing succeeds
  if isTrue p -- if the assumption is persistent (since we can reuse it)
     || (f1.isSome && f2.isSome) -- or if both sides made progress
     || (f1.isSome && isBITrue Q1) -- or if the left side was changed to True
     || (f2.isSome && isBITrue Q2) -- or if the right side was changed to True
  then
    let .some _ ← maybeFrame p R P1 Q1 f1 | return .continue
    let .some _ ← maybeFrame p R P2 Q2 f2 | return .continue
    let Q' : Q($prop) ← mkFreshExprMVarQ q($prop)
    let .some _ ← synthInstanceRecursiveQ q(MakeOr $Q1 $Q2 $Q') |
      throwError "MakeOr should always succeed"
    return .success q(frame_or $p $R $P1 $P2 $Q1 $Q2 $Q')
  return .continue

@[ipm_tactic_instance Frame _ _ iprop(∃ _, _) _]
def frameExist : SynthTactic := λ e => do
  let_expr Frame prop bi p R P _ := e | return .continue
  have u := e.getAppFn.constLevels![0]!
  have prop : Q(Type u) := prop
  have _bi : Q(BI $prop) := bi
  have p : Q(Bool) := p
  have R : Q($prop) := R
  let_expr BI.exists _ _ α Φ := P | return .continue

  let .sort v ← inferType α | return .continue
  have α : Q(Sort v) := α
  have Φ : Q($α → $prop) := Φ

  -- Find the binder name so that it can be reused after framing
  let .lam bn _ _ bi := Φ | throwError "iframe: argument to BI.exists must be a lambda"

  -- Introduce a free variable `c` for the computation within `withLocalDeclDQ`
  let some ⟨a, X, inst⟩ ← withLocalDeclQ bn bi α fun c => do
    let a : Q($α) ← if ← frameInstantiateExistsEnabled then mkFreshExprMVarQ q($α) else pure c
    let G ← mkFreshExprMVarQ q($prop)
    have body : Q($prop) := Expr.headBeta q($Φ $a)
    let some inst ← synthInstanceRecursiveQ q(Frame $p $R $body $G) | return none

    /-
      If `a` is defEq to `c`, the existential quantifier remains. This can be either since the
      framing did not instantiate the existential quantifer or since the instiation of existentials
      was disabled. The `withConfig` is necessary to disable stuck defEq exceptions.
    -/
    if ← withTransparency .none <| withConfig (λ _ => {}) (isDefEq (← instantiateMVars a) c) then
      return some (none, ← mkLambdaFVars #[c] (← instantiateMVars G),
                          ← mkLambdaFVars #[c] (← instantiateMVars inst))
    else
      -- The existential quantifier does not remain as the existential variable is instantiated.
      return some (some <| ← instantiateMVars a, ← instantiateMVars G, ← instantiateMVars inst)
  | return .continue

  match a with
  | none =>
    have Ψ : Q($α → $prop) := X
    let inst : Q(∀ x, Frame $p $R ($Φ x) ($Ψ x)) := inst
    return .success q(frame_exist_no_instantiate $p $R $Φ $Ψ $inst)
  | some a =>
    have a : Q($α) := a
    have G : Q($prop) := X
    let inst : Q(Frame $p $R ($Φ $a) $G) := inst
    return .success q(frame_exist $p $R $Φ $a $G $inst)

#rocq_ignore frame_exist_helper "Logic already handled in the metaprogram frameExist"
#rocq_ignore GatherEvarsEq
  "Rocq-specific telescope infrastructure not needed in the Lean metaprogram"
#rocq_ignore TCCbnTele "Rocq-specific telescope infrastructure not needed in the Lean metaprogram"
