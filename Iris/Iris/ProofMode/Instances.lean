/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler, Alvin Tang
-/
module

public import Iris.BI
public import Iris.ProofMode.Classes
public import Iris.ProofMode.ClassesMake
public import Iris.ProofMode.ModalityInstances
public import Iris.ProofMode.Expr
public import Iris.Std.TC
public import Iris.ProofMode.Tactics
public import Iris.ProofMode.Display

@[expose] public section

namespace Iris.ProofMode
open Iris.BI Iris.Std

/-! ### AsEmpValid -/

@[rocq_alias as_emp_valid_emp_valid]
instance (priority := default + 10) asEmpValidEmpValid
    [bi : BI PROP] d (P : PROP) io : AsEmpValid0 d (⊢ P) io PROP bi P where
  as_emp_valid_0 := ⟨by simp⟩

@[rocq_alias as_emp_valid_entails]
instance asEmpValid_entails [bi : BI PROP] d io (P Q : PROP) :
    AsEmpValid0 d (P ⊢ Q) io PROP bi iprop(P -∗ Q) where
  as_emp_valid_0 := ⟨λ _ => entails_wand, λ _ => wand_entails⟩

instance asEmpValid_bientails [bi : BI PROP] d io (P Q : PROP) :
    AsEmpValid0 d (P ⊣⊢ Q) io PROP bi iprop(P ∗-∗ Q) where
  as_emp_valid_0 := ⟨λ _ => equiv_wandIff, λ _ => wandIff_equiv⟩

@[rocq_alias as_emp_valid_equiv]
instance asEmpValid_equiv [bi : BI PROP] d io (P Q : PROP) :
    AsEmpValid0 d (P = Q) io PROP bi iprop(P ∗-∗ Q) where
  as_emp_valid_0 := ⟨λ _ h => h ▸ wandIff_refl,
    λ _ h => equiv_iff.2 (wandIff_equiv h)⟩

@[rocq_alias as_emp_valid_forall]
instance asEmpValid_forall {α} [bi : BI PROP] (Φ : α → Prop) (P : α → PROP) d io
    [hP : ∀ x, AsEmpValid d (Φ x) io PROP bi iprop(P x)] :
    AsEmpValid d (∀ x, Φ x) io PROP bi iprop(∀ x, P x) where
  as_emp_valid := ⟨λ hd h => forall_intro λ x => (hP x).1.1 hd (h x),
                   λ hd h x => (hP x).1.2 hd $ h.trans (forall_elim x)⟩

@[rocq_alias as_emp_valid_tforall]
instance asEmpValid_tforall {TT : Tele} [bi : BI PROP] (φ : TT.Arg → Prop)
    (P : TT.Arg → PROP) d io [hP : ∀ x, AsEmpValid d (φ x) io PROP bi (P x)] :
    AsEmpValid d (∀.. x, φ x) io PROP bi iprop(∀.. x, P x) where
  as_emp_valid := by
    constructor
    · refine fun hd h => .trans ?_ (tforall_forall P).mpr
      apply forall_intro
      exact fun x => (hP x).as_emp_valid.left hd ((Tele.tforall_forall φ).mp h x)
    · refine fun hd h => (Tele.tforall_forall φ).mpr ?_
      refine fun x => (hP x).as_emp_valid.right hd ?_
      calc
        _ ⊢ tforall P := h
        _ ⊢ ∀ x, P x  := (tforall_forall P).mp
        _ ⊢ P x       := forall_elim x

/-! ### FromImp -/

@[rocq_alias from_impl_impl]
instance fromImp_imp [BI PROP] (P1 P2 : PROP) : FromImp iprop(P1 → P2) P1 P2 := ⟨.rfl⟩

/-! ### FromWand -/

@[rocq_alias from_wand_wand]
instance fromWand_wand [BI PROP] (P1 P2 : PROP) io :
    FromWand iprop(P1 -∗ P2) io P1 P2 :=
  ⟨.rfl⟩

/-! ### FromWandM -/

@[rocq_alias from_wand_wandM]
instance fromWand_wandM [BI PROP] (mP1 : Option PROP) (P2 : PROP) :
    FromWand iprop(mP1 -∗? P2) io (mP1.getD emp) P2 where
  from_wand := wandM_sound.mpr

/-! ### IntoWand -/

/-
These three instances change `IntoWand'` goals to `IntoWand` at priority `100`.
The `WandMode` parameter of `IntoWand` makes the two classes one, so the args
instances match such goals directly and `(priority := low)` orders them last.
-/
#rocq_ignore into_wand_wand' "Subsumed by the `WandMode` parameter of `IntoWand`"
#rocq_ignore into_wand_impl' "Subsumed by the `WandMode` parameter of `IntoWand`"
#rocq_ignore into_wand_wandM' "Subsumed by the `WandMode` parameter of `IntoWand`"

@[rocq_alias into_wand_wand]
instance intoWand_wand (p q : Bool) [BI PROP]
    (P Q P' : PROP) [h : FromAssumption q m.argIO P P'] :
    IntoWand p q iprop(P' -∗ Q) m P Q where
  into_wand := (intuitionisticallyIf_mono <| wand_mono_left h.1).trans intuitionisticallyIf_elim

@[rocq_alias into_wand_impl_false_true]
instance intoWand_impl_false_true [BI PROP] (P Q P' : PROP) (m : WandMode) [Absorbing P']
    [h : FromAssumption true m.argIO P P'] : IntoWand false true iprop(P' → Q) m P Q where
  into_wand := by
    calc
      _ ⊢ <pers> P' → Q           := imp_mono_left persistently_elim
      _ ⊢ <affine> <pers> P' -∗ Q := persistent_impl_wand_affinely.mp
      _ ⊢ □ P -∗ Q                := wand_mono_left <| affinely_intro <| Persistent.persistent.trans <| persistently_mono h.from_assumption

@[rocq_alias into_wand_impl_true_false]
instance intoWand_impl_true_false [BI PROP] (P Q P' P'' : PROP) (m : WandMode)
    [h1 : MakeAffinely P P'] [h2 : FromAssumption false m.argIO P'' P'] :
    IntoWand true false iprop(P → Q) m P'' Q where
  into_wand := by
    apply wand_intro
    calc
      _ ⊢ □ (P → Q) ∗ P'         := sep_mono_right h2.from_assumption
      _ ⊢ □ (P → Q) ∗ <affine> P := sep_mono_right h1.make_affinely.mpr
      _ ⊢ □ (P → Q) ∧ <affine> P := sep_and
      _ ⊢ (P → Q) ∧ <affine> P   := and_mono_left intuitionistically_elim
      _ ⊢ (P → Q) ∧ P            := and_mono_right affinely_elim
      _ ⊢ Q                      := imp_elim_left

@[rocq_alias into_wand_impl_true_true]
instance intoWand_impl_true_true [BI PROP] (P Q P' : PROP) (m : WandMode)
    [h : FromAssumption true m.argIO P P'] : IntoWand true true iprop(P' → Q) m P Q where
  into_wand := by
    apply wand_intro
    calc
      _ ⊢ □ (P' → Q) ∧ □ P := sep_and
      _ ⊢ (P' → Q) ∧ □ P   := and_mono_left intuitionistically_elim
      _ ⊢ (P' → Q) ∧ P'    := and_mono_right h.from_assumption
      _ ⊢ Q                := imp_elim_left

@[rocq_alias into_wand_impl_false_false]
instance intoWand_impl_false_false [BI PROP] (P Q P' P'' : PROP) (m : WandMode)
    [Absorbing P] [inst : TCOr (BIAffine PROP) (Persistent P)] [h1 : MakeAffinely P P']
    [h2 : FromAssumption false m.argIO P'' P'] : IntoWand false false iprop(P → Q) m P'' Q where
  into_wand := by
    apply wand_intro
    match inst with
    | TCOr.l => calc
      _ ⊢ (P → Q) ∗ P'                   := sep_mono_right <| h2.from_assumption
      _ ⊢ (P → Q) ∗ <affine> P           := sep_mono_right <| h1.make_affinely.mpr
      _ ⊢ (<affine> P -∗ Q) ∗ <affine> P := sep_mono_left <| imp_wand_1.trans <| wand_mono_left affinely_elim
      _ ⊢ Q                              := wand_elim_left
    | TCOr.r => calc
      _ ⊢ (P → Q) ∗ P'                   := sep_mono_right <| h2.from_assumption
      _ ⊢ (P → Q) ∗ <affine> P           := sep_mono_right <| h1.make_affinely.mpr
      _ ⊢ (<affine> P -∗ Q) ∗ <affine> P := sep_mono_left persistent_impl_wand_affinely.mp
      _ ⊢ Q                              := wand_elim_left

@[ipm_backtrack, rocq_alias into_wand_and_l]
instance intoWand_and_left (p q : Bool) [BI PROP] (R1 R2 P' Q' : PROP)
    [h : IntoWand p q R1 m P' Q'] : IntoWand p q iprop(R1 ∧ R2) m P' Q' where
  into_wand := (intuitionisticallyIf_mono and_elim_l).trans h.1

@[ipm_backtrack, rocq_alias into_wand_and_r]
instance intoWand_and_right (p q : Bool) [BI PROP] (R1 R2 P' Q' : PROP)
    [h : IntoWand p q R2 m P' Q'] : IntoWand p q iprop(R1 ∧ R2) m P' Q' where
  into_wand := (intuitionisticallyIf_mono and_elim_r).trans h.1

instance intoWand_wandIff (p q : Bool) [BI PROP] (R1 R2 P' Q' : PROP)
    [h : IntoWand p q iprop((R1 -∗ R2) ∧ (R2 -∗ R1)) m P' Q'] :
    IntoWand p q iprop(R1 ∗-∗ R2) m P' Q' := h

@[rocq_alias into_wand_wandM]
instance intoWand_wandM (p q : Bool) [BI PROP] (mP' : Option PROP) (P Q : PROP)
    [h : FromAssumption q m.argIO P (mP'.getD emp)] :
    IntoWand p q iprop(mP' -∗? Q) m P Q where
  into_wand := calc
    _ ⊢ □?p (mP'.getD iprop(emp) -∗ Q) := intuitionisticallyIf_mono wandM_sound.mp
    _ ⊢ □?p (□?q P -∗ Q)               := intuitionisticallyIf_mono <| wand_mono_left h.1
    _ ⊢ □?q P -∗ Q                     := intuitionisticallyIf_elim

@[ipm_backtrack, rocq_alias into_wand_forall_prop_true]
instance (priority := default + 20) intoWand_forall_prop_true (p : Bool) [BI PROP]
    (m : WandMode) (φ : Prop) (P : PROP) :
    IntoWand p true iprop(∀ _ : φ, P) m iprop(⌜φ⌝) P where
  into_wand := by
    refine wand_intro (pure_elim φ ?_ fun hφ => ?_)
    · exact (sep_mono_right intuitionistically_elim).trans sep_elim_right
    · calc
        _ ⊢ □?p ∀ a, P := sep_elim_left
        _ ⊢ ∀ a, P     := intuitionisticallyIf_elim
        _ ⊢ P          := forall_elim hφ

@[ipm_backtrack, rocq_alias into_wand_forall_prop_false]
instance (priority := default + 10) intoWand_forall_prop_false (p : Bool) [BI PROP]
    (m : WandMode) (φ : Prop) (Pφ P' P : PROP)
    [h1 : MakeAffinely iprop(⌜φ⌝) Pφ] [h2 : FromAssumption false m.argIO P' Pφ] :
    IntoWand p false iprop(∀ _ : φ, P) m P' P where
  into_wand := by
    have h := h2.from_assumption.trans h1.make_affinely.mpr
    refine wand_intro (pure_elim φ ?_ fun hφ => ?_)
    · exact (sep_mono_right (h.trans affinely_elim)).trans sep_elim_right
    · calc
        _ ⊢ (□?p ∀ a, P) ∗ <affine> ⌜φ⌝ := sep_mono_right h
        _ ⊢ □?p ∀ a, P                  := sep_elim_left
        _ ⊢ ∀ a, P                      := intuitionisticallyIf_elim
        _ ⊢ P                           := forall_elim hφ

-- The set_option is ok since this is an instance for an IPM class and thus can create mvars.
set_option synthInstance.checkSynthOrder false in
@[rocq_alias into_wand_forall]
instance intoWand_forall (p q : Bool) [BI PROP] (Φ : α → PROP) (P Q : PROP) (x : α)
    [h : IntoWand p q (Φ x) m P Q] : IntoWand p q iprop(∀ x, Φ x) m P Q where
  into_wand := (intuitionisticallyIf_mono <| BI.forall_elim x).trans h.1

@[rocq_alias into_wand_affine]
instance intoWand_affinely (p q : Bool) [BI PROP]
    (R P Q : PROP) [h : IntoWand p q R m P Q] :
    IntoWand p q iprop(<affine> R) m iprop(<affine> P) iprop(<affine> Q) where
  into_wand := by
    refine wand_intro ?_
    calc
      _ ⊢ <affine> □?p R ∗ <affine> □?q P :=
          (sep_congr intuitionisticallyIf_affinely intuitionisticallyIf_affinely).mp
      _ ⊢ <affine> (□?p R ∗ □?q P)        := affinely_sep_mpr
      _ ⊢ <affine> Q                      := affinely_mono <| wand_elim h.into_wand

@[rocq_alias into_wand_affine_args]
instance (priority := low) intoWand_affinely_args (q : Bool) [BI PROP]
    (s : WandMode.Side) (R P Q : PROP) [h : IntoWand true q R (.matching s) P Q] :
    IntoWand true q R (.matching s) iprop(<affine> P) iprop(<affine> Q) where
  into_wand := by
    refine wand_intro ?_
    calc
      _ ⊢ <affine> (□?q P -∗ Q) ∗ □?q <affine> P :=
          sep_mono_left <| (affine_affinely _).mpr.trans <| affinely_mono h.into_wand
      _ ⊢ <affine> (□?q P -∗ Q) ∗ <affine> □?q P :=
          sep_mono_right <| (intuitionisticallyIf_affinely (p := q)).mp
      _ ⊢ <affine> ((□?q P -∗ Q) ∗ □?q P) := affinely_sep_mpr
      _ ⊢ <affine> Q := affinely_mono wand_elim_left

@[rocq_alias into_wand_intuitionistically]
instance intoWand_intuitionistically (p q : Bool) [BI PROP] (R P Q : PROP)
    [h : IntoWand true q R m P Q] : IntoWand p q iprop(□ R) m P Q where
  into_wand := (intuitionisticallyIf_mono h.1).trans intuitionisticallyIf_elim

@[rocq_alias into_wand_persistently_true]
instance intoWand_persistently_true (q : Bool) [BI PROP] (R P Q : PROP)
    [h : IntoWand true q R m P Q] : IntoWand true q iprop(<pers> R) m P Q where
  into_wand := intuitionistically_persistently.1.trans h.1

@[rocq_alias into_wand_persistently_false]
instance intoWand_persistently_false (q : Bool) [BI PROP] (R P Q : PROP) [Absorbing R]
    [h : IntoWand false q R m P Q] : IntoWand false q iprop(<pers> R) m P Q where
  into_wand := persistently_elim.trans h.1

set_option synthInstance.checkSynthOrder false in
/-- The `x` in `Φ x` is handled by the IPM synthesiser as a subgoal. -/
@[rocq_alias into_wand_tforall]
instance intoWand_tforall {TT : Tele} (p q : Bool) [BI PROP] (Φ : TT.Arg → PROP)
    (P Q : PROP) (x : TT.Arg) [h : IntoWand p q (Φ x) m P Q] :
    IntoWand p q (BI.tforall Φ) m P Q where
  into_wand :=
    (intuitionisticallyIf_mono <| (tforall_forall Φ).mp.trans (forall_elim x)).trans h.into_wand

/-! ### FromForall -/

@[rocq_alias from_forall_forall]
instance fromForall_forall [BI PROP] (Φ : α → PROP) :
  FromForall (BIBase.forall Φ) Φ := ⟨.rfl⟩

@[rocq_alias from_forall_pure]
instance fromForall_pure [BI PROP] (Φ : α → Prop) :
    FromForall (PROP := PROP) iprop(⌜∀ a, Φ a⌝) (λ a => iprop(⌜Φ a⌝)) :=
  ⟨pure_forall.2⟩

@[rocq_alias from_forall_pure_not]
instance fromForall_pure_not [BI PROP] (Φ :Prop) :
    FromForall (PROP := PROP) iprop(⌜¬ Φ⌝) (λ _ : Φ => iprop(False)) :=
  ⟨pure_forall.2⟩

@[rocq_alias from_forall_impl_pure]
instance fromForall_imp_pure [BI PROP] (P Q : PROP) φ
    [IntoPure P φ] :
    FromForall iprop(P → Q) (λ _ : φ => Q) where
  from_forall := imp_intro <| (and_mono_right into_pure).trans <| pure_elim_right forall_elim

@[rocq_alias from_forall_wand_pure]
instance fromForall_wand_pure [BI PROP] (P Q : PROP) φ
    [IntoPure P φ] [inst : TCOr (Affine P) (Absorbing Q)] :
    FromForall iprop(P -∗ Q) (λ _ : φ => Q) where
  from_forall := wand_intro <|
    pure_elim _ ((sep_mono_right into_pure).trans sep_elim_right) fun h =>
      match inst with
      | .l (t := _) => sep_elim_left |>.trans (forall_elim h)
      | .r (u := _) => sep_elim_left |>.trans (forall_elim h)

@[rocq_alias from_forall_intuitionistically]
instance fromForall_intuitionistically [BI PROP] [BIAffine PROP] [BIPersistentlyForall PROP] {A} P (Φ : A → PROP)
    [FromForall P Φ] : FromForall iprop(□ P) (λ a => iprop(□ (Φ a))) where
  from_forall := calc
    _ ⊢ ∀ a, <pers> Φ a := forall_mono λ _ => persistently_of_intuitionistically
    _ ⊢ <pers> ∀ a, Φ a := persistently_forall.mpr
    _ ⊢ <pers> P        := persistently_mono from_forall
    _ ⊢ □ P             := intuitionistically_iff_persistently.mpr

@[rocq_alias from_forall_persistently]
instance fromForall_persistently [BI PROP] [BIPersistentlyForall PROP] {A} P (Φ : A → PROP)
    [FromForall P Φ] : FromForall iprop(<pers> P) (λ a => iprop(<pers> (Φ a))) where
  from_forall := persistently_forall.2.trans $ (persistently_mono (from_forall (P := P)))

@[rocq_alias from_forall_tforall]
instance fromForall_tforall {TT : Tele} [BI PROP] (Φ : TT.Arg → PROP) :
    FromForall (BI.tforall Φ) Φ := ⟨(tforall_forall Φ).mpr⟩

@[rocq_alias from_tforall_pure]
instance fromForall_tforall_pure {TT : Tele} [BI PROP] (φ : TT.Arg → Prop) :
    FromForall (PROP := PROP) iprop(⌜Tele.tforall φ⌝) (iprop(⌜φ ·⌝)) where
  from_forall := pure_forall.mpr.trans (pure_mono (Tele.tforall_forall φ).mpr)

/-! ### IntoForall -/

@[rocq_alias into_forall_forall]
instance intoForall_forall [BI PROP] (Φ : α → PROP) :
    IntoForall iprop(∀ a, Φ a) Φ where
  into_forall := .rfl

@[rocq_alias into_forall_affinely]
instance intoForall_affinely [BI PROP] (P : PROP) (Φ : α → PROP) [h : IntoForall P Φ] :
    IntoForall iprop(<affine> P) (fun a => iprop(<affine> (Φ a))) where
  into_forall := (affinely_mono h.1).trans affinely_forall

@[rocq_alias into_forall_intuitionistically]
instance intoForall_intuitionistically [BI PROP] (P : PROP) (Φ : α → PROP)
    [h : IntoForall P Φ] : IntoForall iprop(□ P) (fun a => iprop(□ (Φ a))) where
  into_forall := (intuitionistically_mono h.1).trans intuitionistically_forall

@[rocq_alias into_forall_persistently]
instance intoForall_persistently [BI PROP] [BIPersistentlyForall PROP]
    (P : PROP) (Φ : α → PROP)
    [h : IntoForall P Φ] : IntoForall iprop(<pers> P) (fun a => iprop(<pers> (Φ a))) where
  into_forall := (persistently_mono h.1).trans persistently_forall_mp

@[ipm_backtrack, rocq_alias into_forall_wand_pure]
instance intoForall_wand_pure [BI PROP] (P Q : PROP) Φ
    [h : FromPure a P .out Φ] : IntoForall iprop(P -∗ Q) (fun _ : Φ => Q) where
  into_forall := by
    refine forall_intro λ hΦ => ?_
    calc
      _ ⊢ emp ∗ (P -∗ Q) := emp_sep.mpr
      _ ⊢ P ∗ (P -∗ Q)   := sep_mono_left ?_
      _ ⊢ Q              := wand_elim_right
    calc
      _ ⊢ <affine>?a emp := affinelyIf_emp.mpr
      _ ⊢ <affine>?a ⌜Φ⌝ := affinelyIf_mono <| pure_intro hΦ
      _ ⊢ P              := h.from_pure

@[ipm_backtrack, rocq_alias into_forall_impl_pure]
instance intoForall_imp_pure [BI PROP] (a : Bool) (φ : Prop) (P Q : PROP)
    [h : FromPure a P .out φ] [or : TCOr (TCEq a false) (BIAffine PROP)] :
    IntoForall iprop(P → Q) (fun _ : φ => Q) where
  into_forall := by
    refine forall_intro fun hφ => ?_
    refine (and_intro .rfl ?_).trans imp_elim_left
    refine Entails.trans ?_ h.from_pure
    exact match a, or with
      | false, _ => pure_intro hφ
      | true, TCOr.r => (affine_affinely _).mpr.trans (affinely_mono <| pure_intro hφ)
      | true, TCOr.l (t := heq) => nomatch heq

@[rocq_alias into_forall_wand]
instance (priority := default - 10) intoForall_wand [BI PROP] (P Q : PROP) :
    IntoForall iprop(P -∗ Q) (fun _ : (⊢ P) => Q) where
  into_forall := forall_intro fun h => calc
    _ ⊢ emp ∗ (P -∗ Q) := emp_sep.mpr
    _ ⊢ P ∗ (P -∗ Q)   := sep_mono_left h
    _ ⊢ Q              := wand_elim_right

@[rocq_alias into_forall_impl]
instance (priority := default - 10) intoForall_imp [BI PROP] [BIAffine PROP] (P Q : PROP) :
    IntoForall iprop(P → Q) (fun _ : (⊢ P) => Q) where
  into_forall := forall_intro fun h =>
    (and_intro .rfl (affine.trans h)).trans imp_elim_left

@[rocq_alias into_forall_tforall]
instance (priority := default - 10) intoForall_tforall {TT : Tele} [BI PROP]
    (Φ : TT.Arg → PROP) : IntoForall (BI.tforall Φ) Φ where
  into_forall := (tforall_forall Φ).mp

/-! ### FromExists -/

@[rocq_alias from_exist_exist]
instance (priority := default + 10) fromExists_exists [BI PROP] (Φ : α → PROP) :
    FromExists iprop(∃ a, Φ a) Φ := ⟨.rfl⟩

@[rocq_alias from_exist_pure]
instance fromExists_pure (φ : α → Prop) [BI PROP] :
    FromExists (PROP := PROP) iprop(⌜∃ x, φ x⌝) (fun a => iprop(⌜φ a⌝)) where
  from_exists := pure_exists.1

@[rocq_alias from_exist_affinely]
instance fromExists_affinely [BI PROP] (P : PROP) (Φ : α → PROP) [h : FromExists P Φ] :
    FromExists iprop(<affine> P) (fun a => iprop(<affine> (Φ a))) where
  from_exists := affinely_exists.2.trans <| affinely_mono h.1

@[rocq_alias from_exist_intuitionistically]
instance fromExists_intuitionistically [BI PROP] (P : PROP)
    (Φ : α → PROP) [h : FromExists P Φ] :
    FromExists iprop(□ P) (fun a => iprop(□ (Φ a))) where
  from_exists := intuitionistically_exists.2.trans <| intuitionistically_mono h.1

@[rocq_alias from_exist_absorbingly]
instance fromExists_absorbingly [BI PROP] (P : PROP)
    (Φ : α → PROP) [h : FromExists P Φ] :
    FromExists iprop(<absorb> P) (fun a => iprop(<absorb> (Φ a))) where
  from_exists := absorbingly_exists.2.trans <| absorbingly_mono h.1

@[rocq_alias from_exist_persistently]
instance fromExists_persistently [BI PROP] (P : PROP) (Φ : α → PROP) [h : FromExists P Φ] :
    FromExists iprop(<pers> P) (fun a => iprop(<pers> (Φ a))) where
  from_exists := persistently_exists.2.trans <| persistently_mono h.1

@[rocq_alias from_exist_texist]
instance fromExists_texist {TT : Tele} [BI PROP] (Φ : TT.Arg → PROP) :
    FromExists (texist Φ) Φ where
  from_exists := (texist_exist Φ).mpr

/-! ### IntoExists -/

@[rocq_alias into_exist_exist]
instance intoExists_exists [BI PROP] (Φ : α → PROP) : IntoExists (BI.exists Φ) Φ := ⟨.rfl⟩

@[rocq_alias into_exist_pure]
instance intoExists_pure (φ : α → Prop) [BI PROP] :
    IntoExists (PROP := PROP) iprop(⌜∃ x, φ x⌝) (fun a => iprop(⌜φ a⌝)) where
  into_exists := pure_exists.2

@[rocq_alias into_exist_affinely]
instance intoExists_affinely [BI PROP] (P : PROP) (Φ : α → PROP) [h : IntoExists P Φ] :
    IntoExists iprop(<affine> P) (fun a => iprop(<affine> (Φ a))) where
  into_exists := (affinely_mono h.1).trans affinely_exists.1

@[rocq_alias into_exist_intuitionistically]
instance intoExists_intuitionistically [BI PROP]
    (P : PROP) (Φ : α → PROP) [h : IntoExists P Φ] :
    IntoExists iprop(□ P) (fun a => iprop(□ (Φ a))) where
  into_exists := (intuitionistically_mono h.1).trans intuitionistically_exists.1

@[ipm_backtrack, rocq_alias into_exist_and_pure]
instance (priority := default - 10) intoExist_and_pure [BI PROP] (PQ P Q : PROP) (Φ : Prop)
    [IntoAnd false PQ P Q] [IntoPure P Φ] :
    IntoExists PQ (λ _ : Φ => Q) where
  into_exists := calc
    _ ⊢ P ∧ Q   := into_and (p := false)
    _ ⊢ ⌜Φ⌝ ∧ Q := and_mono_left into_pure
    _ ⊢ ∃ _, Q  := pure_elim_left <| λ h => exists_intro (Ψ := λ _ => Q) h

@[rocq_alias into_exist_sep_pure]
instance intoExist_sep_pure [BI PROP] (P Q : PROP) (Φ : Prop)
    [IntoPure P Φ] [TCOr (Affine P) (Absorbing Q)] :
    IntoExists iprop(P ∗ Q) (λ _ : Φ => Q) where
  into_exists :=
    (pure_elim _ ((sep_mono_left into_pure).trans sep_elim_left) (λ h =>
              sep_elim_right.trans <| exists_intro (Ψ:=λ _ => Q) h))

@[rocq_alias into_exist_absorbingly]
instance intoExists_absorbingly [BI PROP] (P : PROP) (Φ : α → PROP) [h : IntoExists P Φ] :
    IntoExists iprop(<absorb> P) (fun a => iprop(<absorb> (Φ a))) where
  into_exists := (absorbingly_mono h.1).trans absorbingly_exists.1

@[rocq_alias into_exist_persistently]
instance intoExists_persistently [BI PROP] {P : PROP} (Φ : α → PROP) [h : IntoExists P Φ] :
    IntoExists iprop(<pers> P) (fun a => iprop(<pers> (Φ a))) where
  into_exists := (persistently_mono h.1).trans persistently_exists.1

@[rocq_alias into_exist_texist]
instance (priority := default - 10) intoExists_texist {TT : Tele} [BI PROP]
    (Φ : TT.Arg → PROP) : IntoExists (texist Φ) Φ where
  into_exists := (texist_exist Φ).mp

/-! ### FromAnd -/

@[rocq_alias from_and_and]
instance (priority := default - 10) fromAnd_and [BI PROP] (P1 P2 : PROP) :
    FromAnd iprop(P1 ∧ P2) P1 P2 := ⟨.rfl⟩

instance fromAnd_wandIff [BI PROP] (P1 P2 P1' P2' : PROP)
    [h : FromAnd iprop((P1 -∗ P2) ∧ (P2 -∗ P1)) P1' P2'] :
    FromAnd iprop(P1 ∗-∗ P2) P1' P2' := h

instance fromAnd_iff [BI PROP] (P1 P2 P1' P2' : PROP)
    [h : FromAnd iprop((P1 → P2) ∧ (P2 → P1)) P1' P2'] :
    FromAnd iprop(P1 ↔ P2) P1' P2' := h

@[ipm_backtrack, rocq_alias from_and_sep_persistent_l]
instance (priority := default + 30) fromAnd_sep_persistent_left [BI PROP] (P1 P1' P2 : PROP)
    [Persistent P1] [h : IntoAbsorbingly P1' P1] : FromAnd iprop(P1 ∗ P2) P1' P2 where
  from_and := by
    calc
      _ ⊢ <absorb> P1 ∧ P2          := and_mono_left h.into_absorbingly
      _ ⊢ <affine> <absorb> P1 ∗ P2 := persistent_and_affinely_sep_left.mp
      _ ⊢ □ P1 ∗ P2                 := sep_mono_left ?_
      _ ⊢ P1 ∗ P2                   := sep_mono_left intuitionistically_elim
    exact affinely_mono <| (absorbingly_mono persistent).trans absorbingly_persistently.mp

@[ipm_backtrack, rocq_alias from_and_sep_persistent_r]
instance (priority := default + 20) fromAnd_sep_persistent_right [BI PROP] (P1 P2 P2' : PROP)
    [Persistent P2] [h : IntoAbsorbingly P2' P2] : FromAnd iprop(P1 ∗ P2) P1 P2' where
  from_and := by
    calc
      _ ⊢ P1 ∧ <absorb> P2          := and_mono_right h.into_absorbingly
      _ ⊢ P1 ∗ <affine> <absorb> P2 := persistent_and_affinely_sep_right.mp
      _ ⊢ P1 ∗ □ P2                 := sep_mono_right ?_
      _ ⊢ P1 ∗ P2                   := sep_mono_right intuitionistically_elim
    exact affinely_mono <| (absorbingly_mono persistent).trans absorbingly_persistently.mp

@[rocq_alias from_and_pure]
instance (priority := default + 50) fromAnd_pure (φ ψ : Prop) [BI PROP] :
    FromAnd (PROP := PROP) iprop(⌜φ ∧ ψ⌝) iprop(⌜φ⌝) iprop(⌜ψ⌝) where
  from_and := pure_and.1

@[rocq_alias from_and_pure_iff]
instance (priority := default + 50) fromAnd_pure_iff (φ ψ : Prop) [BI PROP] :
    FromAnd (PROP := PROP) iprop(⌜φ ↔ ψ⌝) iprop(⌜φ → ψ⌝) iprop(⌜ψ → φ⌝) where
  from_and := pure_and.mp.trans <| pure_mono fun h => ⟨h.left, h.right⟩

@[rocq_alias from_and_persistently]
instance (priority := default + 40) fromAnd_persistently [BI PROP] (P Q1 Q2 : PROP)
    [h : FromAnd P Q1 Q2] : FromAnd iprop(<pers> P) iprop(<pers> Q1) iprop(<pers> Q2) where
  from_and := persistently_and.2.trans <| persistently_mono h.1

@[rocq_alias from_and_persistently_sep]
instance (priority := default + 10) fromAnd_persistently_sep [BI PROP] (P Q1 Q2 : PROP)
    [h : FromSep P Q1 Q2] : FromAnd iprop(<pers> P) iprop(<pers> Q1) iprop(<pers> Q2) where
  from_and := persistently_and.2.trans <| persistently_and_sep.trans <| persistently_mono h.1

@[ipm_backtrack, rocq_alias from_and_big_sepL_cons_persistent]
instance (priority := default + 38) fromAnd_bigSepL_cons_persistent [BI PROP] {A}
    (Φ : Nat → A → PROP) (l : List A) (x : A) (l' : List A)
    [hl : IsCons l x l'] [Persistent (Φ 0 x)] :
    FromAnd ([∗list] k ↦ y ∈ l, Φ k y) (Φ 0 x) ([∗list] k ↦ y ∈ l', Φ (k + 1) y) where
  from_and := hl.is_cons ▸ persistent_and_sep_mp.trans BigSepL.bigSepL_cons.mpr

@[ipm_backtrack, rocq_alias from_and_big_sepL_app_persistent]
instance (priority := default + 38) fromAnd_bigSepL_app_persistent [BI PROP] {A}
    (Φ : Nat → A → PROP) (l l₁ l₂ : List A)
    [hl : IsApp l l₁ l₂] [∀ k y, Persistent (Φ k y)] :
    FromAnd ([∗list] k ↦ y ∈ l, Φ k y)
      ([∗list] k ↦ y ∈ l₁, Φ k y) ([∗list] k ↦ y ∈ l₂, Φ (k + l₁.length) y) where
  from_and := hl.is_app ▸ persistent_and_sep_mp.trans BigSepL.bigSepL_append.mpr

@[ipm_backtrack, rocq_alias from_and_big_sepL2_cons_persistent]
instance (priority := default + 36) fromAnd_bigSepL2_cons_persistent [BI PROP] {A B}
    (Φ : Nat → A → B → PROP) (l₁ : List A) (x₁ : A) (l₁' : List A)
    (l₂ : List B) (x₂ : B) (l₂' : List B)
    [h₁ : IsCons l₁ x₁ l₁'] [h₂ : IsCons l₂ x₂ l₂'] [Persistent (Φ 0 x₁ x₂)] :
    FromAnd ([∗list] k ↦ y₁;y₂ ∈ l₁;l₂, Φ k y₁ y₂)
      (Φ 0 x₁ x₂) ([∗list] k ↦ y₁;y₂ ∈ l₁';l₂', Φ (k + 1) y₁ y₂) where
  from_and := by
    rw [h₁.is_cons, h₂.is_cons]
    exact persistent_and_sep_mp.trans BigSepL2.bigSepL2_cons.2

@[ipm_backtrack, rocq_alias from_and_big_sepL2_app_persistent]
instance (priority := default + 36) fromAnd_bigSepL2_app_persistent [BI PROP] {A B}
    (Φ : Nat → A → B → PROP) (l₁ l₁' l₁'' : List A) (l₂ l₂' l₂'' : List B)
    [h₁ : IsApp l₁ l₁' l₁''] [h₂ : IsApp l₂ l₂' l₂'']
    [∀ k y₁ y₂, Persistent (Φ k y₁ y₂)] :
    FromAnd ([∗list] k ↦ y₁;y₂ ∈ l₁;l₂, Φ k y₁ y₂)
      ([∗list] k ↦ y₁;y₂ ∈ l₁';l₂', Φ k y₁ y₂)
      ([∗list] k ↦ y₁;y₂ ∈ l₁'';l₂'', Φ (k + l₁'.length) y₁ y₂) where
  from_and := by
    rw [h₁.is_app, h₂.is_app]
    exact persistent_and_sep_mp.trans <| wand_elim BigSepL2.bigSepL2_app_wand

@[rocq_alias from_and_big_sepMS_disj_union_persistent]
instance (priority := default + 40) fromAnd_bigSepMS_disjUnion_persistent [BI PROP]
    {MS A} [LawfulFiniteMultiSet MS A] (Φ : A → PROP) (X₁ X₂ : MS) [∀ y, Persistent (Φ y)] :
    FromAnd ([∗mset] y ∈ X₁ ⊎ X₂, Φ y) ([∗mset] y ∈ X₁, Φ y) ([∗mset] y ∈ X₂, Φ y) where
  from_and := persistent_and_sep_mp.trans BigSepMS.bigSepMS_disjUnion.mpr

/-! ### IntoAnd -/

@[rocq_alias into_and_and]
instance (priority := default - 10) intoAnd_and (p : Bool) [BI PROP] (P Q : PROP) :
    IntoAnd p iprop(P ∧ Q) P Q := ⟨.rfl⟩

instance intoAnd_wandIff [BI PROP] p (P1 P2 P1' P2' : PROP)
    [h : IntoAnd p iprop((P1 -∗ P2) ∧ (P2 -∗ P1)) P1' P2'] :
    IntoAnd p iprop(P1 ∗-∗ P2) P1' P2' := h

instance intoAnd_iff [BI PROP] p (P1 P2 P1' P2' : PROP)
    [h : IntoAnd p iprop((P1 → P2) ∧ (P2 → P1)) P1' P2'] :
    IntoAnd p iprop(P1 ↔ P2) P1' P2' := h

@[ipm_backtrack, rocq_alias into_and_and_affine_l]
instance intoAnd_and_affine_left [BI PROP] (P Q Q' : PROP) [Affine P]
    [h : FromAffinely Q' Q] : IntoAnd false iprop(P ∧ Q) P Q' where
  into_and := calc
    _ ⊢ <affine> P ∧ Q          := and_mono_left (affine_affinely _).mpr
    _ ⊢ <affine> (P ∧ Q)        := affinely_and_left.mp
    _ ⊢ <affine> P ∧ <affine> Q := affinely_and.mp
    _ ⊢ P ∧ Q'                  := and_mono (affine_affinely _).mp h.from_affinely

@[ipm_backtrack, rocq_alias into_and_and_affine_r]
instance intoAnd_and_affine_right [BI PROP] (P P' Q : PROP) [Affine Q]
    [h : FromAffinely P' P] : IntoAnd false iprop(P ∧ Q) P' Q where
  into_and := calc
    _ ⊢ P ∧ <affine> Q          := and_mono_right (affine_affinely _).mpr
    _ ⊢ <affine> (P ∧ Q)        := affinely_and_right.mp
    _ ⊢ <affine> P ∧ <affine> Q := affinely_and.mp
    _ ⊢ P' ∧ Q                  := and_mono h.from_affinely (affine_affinely _).mp

@[ipm_backtrack, rocq_alias into_and_sep]
instance intoAnd_sep [BI PROP] [BIPositive PROP] (P Q : PROP) :
    IntoAnd true iprop(P ∗ Q) P Q where
  into_and := calc
    _ ⊢ □ P ∗ □ Q := intuitionistically_sep.mp
    _ ⊢ □ P ∧ □ Q := and_sep_intuitionistically.mpr
    _ ⊢ □ (P ∧ Q) := intuitionistically_and.mpr

@[ipm_backtrack, rocq_alias into_and_sep_affine]
instance intoAnd_sep_affine (p : Bool) [BI PROP] (P Q : PROP)
    [TCOr (Affine P) (Absorbing Q)] [TCOr (Affine Q) (Absorbing P)] :
    IntoAnd p iprop(P ∗ Q) P Q where
  into_and := intuitionisticallyIf_mono sep_and

@[rocq_alias into_and_pure]
instance intoAnd_pure (p : Bool) (φ ψ : Prop) [BI PROP] :
    IntoAnd (PROP := PROP) p iprop(⌜φ ∧ ψ⌝) iprop(⌜φ⌝) iprop(⌜ψ⌝) where
  into_and := intuitionisticallyIf_mono pure_and.2

@[rocq_alias into_and_affinely]
instance intoAnd_affinely (p : Bool) [BI PROP] (P Q1 Q2 : PROP) [h : IntoAnd p P Q1 Q2] :
    IntoAnd p iprop(<affine> P) iprop(<affine> Q1) iprop(<affine> Q2) where
  into_and := calc
    _ ⊢ <affine> □?p P                  := intuitionisticallyIf_affinely.mp
    _ ⊢ <affine> □?p (Q1 ∧ Q2)          := affinely_mono h.into_and
    _ ⊢ □?p <affine> (Q1 ∧ Q2)          := intuitionisticallyIf_affinely.mpr
    _ ⊢ □?p (<affine> Q1 ∧ <affine> Q2) := intuitionisticallyIf_mono affinely_and.mp

@[rocq_alias into_and_intuitionistically]
instance intoAnd_intuitionistically (p : Bool) [BI PROP] (P Q1 Q2 : PROP)
    [h : IntoAnd p P Q1 Q2] : IntoAnd p iprop(□ P) iprop(□ Q1) iprop(□ Q2) where
  into_and := calc
      _ ⊢ □ □?p P           := (intuitionisticallyIf_comm_iff (q := true)).mp
      _ ⊢ □ □?p (Q1 ∧ Q2)   := intuitionistically_mono h.into_and
      _ ⊢ □?p □ (Q1 ∧ Q2)   := (intuitionisticallyIf_comm_iff (q := true)).mpr
      _ ⊢ □?p (□ Q1 ∧ □ Q2) := intuitionisticallyIf_mono intuitionistically_and.mp

@[rocq_alias into_and_persistently]
instance intoAnd_persistently (p : Bool) [BI PROP] (P Q1 Q2 : PROP) [h : IntoAnd p P Q1 Q2] :
    IntoAnd p iprop(<pers> P) iprop(<pers> Q1) iprop(<pers> Q2) where
  into_and := by
    refine Entails.trans ?_ (intuitionisticallyIf_mono persistently_and.1)
    cases p
    · exact persistently_mono h.1
    · calc
        _ ⊢ □ P                := intuitionistically_persistently.1
        _ ⊢ □?true (Q1 ∧ Q2)   := h.1
        _ ⊢ □ <pers> (Q1 ∧ Q2) := intuitionistically_persistently.2

/-! ### FromSep -/

@[rocq_alias from_sep_sep]
instance (priority := default - 10) fromSep_sep [BI PROP] (P1 P2 : PROP) :
    FromSep iprop(P1 ∗ P2) P1 P2 := ⟨.rfl⟩

@[rocq_alias from_sep_and]
instance (priority := default - 20) fromSep_and [BI PROP] (P1 P2 : PROP)
    [TCOr (Affine P1) (Absorbing P2)] [TCOr (Affine P2) (Absorbing P1)] :
    FromSep iprop(P1 ∧ P2) P1 P2 where
  from_sep := sep_and

@[rocq_alias from_sep_pure]
instance (priority := default + 20) fromSep_pure (φ ψ : Prop) [BI PROP] :
    FromSep (PROP := PROP) iprop(⌜φ ∧ ψ⌝) iprop(⌜φ⌝) iprop(⌜ψ⌝) where
  from_sep := pure_sep.1

@[rocq_alias from_sep_pure_iff]
instance (priority := default + 20) fromSep_pure_iff (φ ψ : Prop) [BI PROP] :
    FromSep (PROP := PROP) iprop(⌜φ ↔ ψ⌝) iprop(⌜φ → ψ⌝) iprop(⌜ψ → φ⌝) where
  from_sep := pure_sep.mp.trans <| pure_mono fun h => ⟨h.left, h.right⟩

@[rocq_alias from_sep_affinely]
instance (priority := default + 10) fromSep_affinely [BI PROP] (P Q1 Q2 : PROP)
    [h : FromSep P Q1 Q2] : FromSep iprop(<affine> P) iprop(<affine> Q1) iprop(<affine> Q2) where
  from_sep := affinely_sep_mpr.trans (affinely_mono h.1)

@[rocq_alias from_sep_intuitionistically]
instance (priority := default + 10) fromSep_intuitionistically [BI PROP] (P Q1 Q2 : PROP)
    [h : FromSep P Q1 Q2] : FromSep iprop(□ P) iprop(□ Q1) iprop(□ Q2) where
  from_sep := intuitionistically_sep_mpr.trans (intuitionistically_mono h.1)

@[rocq_alias from_sep_absorbingly]
instance (priority := default + 10) fromSep_absorbingly [BI PROP] (P Q1 Q2 : PROP)
    [h : FromSep P Q1 Q2] : FromSep iprop(<absorb> P) iprop(<absorb> Q1) iprop(<absorb> Q2) where
  from_sep := absorbingly_sep.2.trans (absorbingly_mono h.1)

@[rocq_alias from_sep_persistently]
instance (priority := default + 10) fromSep_persistently [BI PROP] (P Q1 Q2 : PROP)
    [h : FromSep P Q1 Q2] : FromSep iprop(<pers> P) iprop(<pers> Q1) iprop(<pers> Q2) where
  from_sep := persistently_sep_mpr.trans (persistently_mono h.1)

@[ipm_backtrack, rocq_alias from_sep_big_sepL_cons]
instance (priority := default + 10) fromSep_bigSepL_cons [BI PROP] {A}
    (Φ : Nat → A → PROP) (l : List A) (x : A) (l' : List A) [hl : IsCons l x l'] :
    FromSep ([∗list] k ↦ y ∈ l, Φ k y) (Φ 0 x) ([∗list] k ↦ y ∈ l', Φ (k + 1) y) where
  from_sep := hl.is_cons ▸ BigSepL.bigSepL_cons.mpr

@[ipm_backtrack, rocq_alias from_sep_big_sepL_app]
instance (priority := default + 10) fromSep_bigSepL_app [BI PROP] {A}
    (Φ : Nat → A → PROP) (l l1 l2 : List A) [hl : IsApp l l1 l2] :
    FromSep ([∗list] k ↦ y ∈ l, Φ k y)
      ([∗list] k ↦ y ∈ l1, Φ k y) ([∗list] k ↦ y ∈ l2, Φ (k + l1.length) y) where
  from_sep := hl.is_app ▸ BigSepL.bigSepL_append.mpr

@[ipm_backtrack, rocq_alias from_sep_big_sepL2_cons]
instance (priority := default + 5) fromSep_bigSepL2_cons [BI PROP] {A B}
    (Φ : Nat → A → B → PROP) (l₁ : List A) (x₁ : A) (l₁' : List A)
    (l₂ : List B) (x₂ : B) (l₂' : List B)
    [h₁ : IsCons l₁ x₁ l₁'] [h₂ : IsCons l₂ x₂ l₂'] :
    FromSep ([∗list] k ↦ y₁;y₂ ∈ l₁;l₂, Φ k y₁ y₂)
      (Φ 0 x₁ x₂) ([∗list] k ↦ y₁;y₂ ∈ l₁';l₂', Φ (k + 1) y₁ y₂) where
  from_sep := by
    rw [h₁.is_cons, h₂.is_cons]
    exact BigSepL2.bigSepL2_cons.mpr

@[ipm_backtrack, rocq_alias from_sep_big_sepL2_app]
instance (priority := default + 5) fromSep_bigSepL2_app [BI PROP] {A B}
    (Φ : Nat → A → B → PROP) (l₁ l₁' l₁'' : List A) (l₂ l₂' l₂'' : List B)
    [h₁ : IsApp l₁ l₁' l₁''] [h₂ : IsApp l₂ l₂' l₂''] :
    FromSep ([∗list] k ↦ y₁;y₂ ∈ l₁;l₂, Φ k y₁ y₂)
      ([∗list] k ↦ y₁;y₂ ∈ l₁';l₂', Φ k y₁ y₂)
      ([∗list] k ↦ y₁;y₂ ∈ l₁'';l₂'', Φ (k + l₁'.length) y₁ y₂) where
  from_sep := by
    rw [h₁.is_app, h₂.is_app]
    exact wand_elim BigSepL2.bigSepL2_app_wand

@[rocq_alias from_sep_big_sepMS_disj_union]
instance (priority := default + 20) fromSep_bigSepMS_disjUnion [BI PROP] {MS A : Type _}
    [LawfulFiniteMultiSet MS A] (Φ : A → PROP) (X₁ X₂ : MS) :
    FromSep ([∗mset] y ∈ X₁ ⊎ X₂, Φ y) ([∗mset] y ∈ X₁, Φ y) ([∗mset] y ∈ X₂, Φ y) where
  from_sep := BigSepMS.bigSepMS_disjUnion.2

/-! ### AndIntoSep -/

@[ipm_class, rocq_alias AndIntoSep]
class inductive AndIntoSep {PROP} [BI PROP] : PROP → outParam PROP → PROP → outParam PROP → Prop
  | affine (P Q Q' : PROP) [Affine P] [h : FromAffinely Q' Q] : AndIntoSep P P Q Q'
  | affinely (P Q : PROP) : AndIntoSep P iprop(<affine> P) Q Q

attribute [instance (default + 10), ipm_backtrack] AndIntoSep.affine
attribute [instance, ipm_backtrack] AndIntoSep.affinely

/-! ### IntoSep -/

@[rocq_alias into_sep_sep]
instance intoSep_sep [BI PROP] (P Q : PROP) : IntoSep iprop(P ∗ Q) P Q := ⟨.rfl⟩

set_option synthInstance.checkSynthOrder false in
@[ipm_backtrack, rocq_alias into_sep_and_persistent_l]
instance intoSep_and_persistent_left [BI PROP] (P Q P' Q' : PROP) [Persistent P]
    [inst : AndIntoSep P P' Q Q'] : IntoSep iprop(P ∧ Q) P' Q' where
  into_sep :=
    match P', inst with
    | _, AndIntoSep.affine (h := h) .. =>
      calc
        _ ⊢ <affine> P ∧ Q          := and_mono_left (affine_affinely _).mpr
        _ ⊢ P ∧ <affine> Q          := affinely_and_left_right.mp
        _ ⊢ <affine> P ∗ <affine> Q := persistent_and_affinely_sep_left_mp
        _ ⊢ P ∗ Q'                  := sep_mono (affine_affinely _).mp h.from_affinely
    | _, AndIntoSep.affinely .. => persistent_and_affinely_sep_left_mp

set_option synthInstance.checkSynthOrder false in
@[ipm_backtrack, rocq_alias into_sep_and_persistent_r]
instance intoSep_and_persistent_right [BI PROP] (P Q P' Q' : PROP) [Persistent Q]
    [inst : AndIntoSep Q Q' P P'] : IntoSep iprop(P ∧ Q) P' Q' where
  into_sep :=
    match P', inst with
    | P', AndIntoSep.affine (h := h) .. =>
      calc
        _ ⊢ P ∧ <affine> Q          := and_mono_right (affine_affinely _).mpr
        _ ⊢ <affine> P ∧ Q          := affinely_and_left_right.mpr
        _ ⊢ <affine> P ∗ <affine> Q := persistent_and_affinely_sep_right_mp
        _ ⊢ P' ∗ Q                  := sep_mono h.from_affinely (affine_affinely _).mp
    | _, AndIntoSep.affinely .. => persistent_and_affinely_sep_right_mp

@[rocq_alias into_sep_pure]
instance intoSep_pure (φ ψ : Prop) [BI PROP] :
    IntoSep (PROP := PROP) iprop(⌜φ ∧ ψ⌝) iprop(⌜φ⌝) iprop(⌜ψ⌝) where
  into_sep := pure_and.2.trans persistent_and_sep_mp

@[ipm_backtrack, rocq_alias into_sep_affinely]
instance (priority:=high) intoSep_affinely [BI PROP] [BIPositive PROP] (P Q1 Q2 : PROP)
    [h : IntoSep P Q1 Q2] : IntoSep iprop(<affine> P) iprop(<affine> Q1) iprop(<affine> Q2) where
  into_sep := (affinely_mono h.1).trans affinely_sep.1

@[ipm_backtrack, rocq_alias into_sep_intuitionistically]
instance (priority:=high) intoSep_intuitionistically [BI PROP] [BIPositive PROP]
    (P Q1 Q2 : PROP) [h : IntoSep P Q1 Q2] : IntoSep iprop(□ P) iprop(□ Q1) iprop(□ Q2) where
  into_sep := (intuitionistically_mono h.1).trans intuitionistically_sep.1

-- Rocq: This instance is kind of strange, it just gets rid of the affinely.
@[rocq_alias into_sep_affinely_trim]
instance (priority := default - 10) intoSep_affinely_trim [BI PROP] (P Q1 Q2 : PROP)
    [h : IntoSep P Q1 Q2] : IntoSep iprop(<affine> P) Q1 Q2 where
  into_sep := affinely_elim.trans h.1

@[ipm_backtrack, rocq_alias into_sep_persistently]
instance intoSep_persistently [BI PROP] [BIPositive PROP] (P Q1 Q2 : PROP)
    [h : IntoSep P Q1 Q2] : IntoSep iprop(<pers> P) iprop(<pers> Q1) iprop(<pers> Q2) where
  into_sep := (persistently_mono h.1).trans persistently_sep.1

@[ipm_backtrack, rocq_alias into_sep_persistently_affine]
instance intoSep_persistently_affine [BI PROP] (P Q1 Q2 : PROP) [h : IntoSep P Q1 Q2]
    [TCOr (Affine Q1) (Absorbing Q2)] [TCOr (Affine Q2) (Absorbing Q1)] :
    IntoSep iprop(<pers> P) iprop(<pers> Q1) iprop(<pers> Q2) where
  into_sep := calc
    _ ⊢ <pers> (Q1 ∧ Q2)      := persistently_mono <| h.into_sep.trans sep_and
    _ ⊢ <pers> Q1 ∧ <pers> Q2 := persistently_and.mp
    _ ⊢ <pers> Q1 ∗ <pers> Q2 := persistently_and_imp_sep

@[ipm_backtrack, rocq_alias into_sep_intuitionistically_affine]
instance intoSep_intuitionistically_affine [BI PROP] (P Q1 Q2 : PROP) [h : IntoSep P Q1 Q2]
    [TCOr (Affine Q1) (Absorbing Q2)] [TCOr (Affine Q2) (Absorbing Q1)] :
    IntoSep iprop(□ P) iprop(□ Q1) iprop(□ Q2) where
  into_sep := calc
    _ ⊢ □ (Q1 ∧ Q2) := intuitionistically_mono <| h.into_sep.trans sep_and
    _ ⊢ □ Q1 ∧ □ Q2 := intuitionistically_and.mp
    _ ⊢ □ Q1 ∗ □ Q2 := and_sep_intuitionistically.mp

@[ipm_backtrack, rocq_alias into_sep_big_sepL_cons]
instance intoSep_bigSepL_cons [BI PROP] {A}
    (Φ : Nat → A → PROP) (l : List A) (x : A) (l' : List A) [hl : IsCons l x l'] :
    IntoSep ([∗list] k ↦ y ∈ l, Φ k y) (Φ 0 x) ([∗list] k ↦ y ∈ l', Φ (k + 1) y) where
  into_sep := hl.is_cons ▸ BigSepL.bigSepL_cons.mp

@[ipm_backtrack, rocq_alias into_sep_big_sepL_app]
instance intoSep_bigSepL_app [BI PROP] {A}
    (Φ : Nat → A → PROP) (l l₁ l₂ : List A) [hl : IsApp l l₁ l₂] :
    IntoSep ([∗list] k ↦ y ∈ l, Φ k y)
      ([∗list] k ↦ y ∈ l₁, Φ k y) ([∗list] k ↦ y ∈ l₂, Φ (k + l₁.length) y) where
  into_sep := hl.is_app ▸ BigSepL.bigSepL_append.mp

@[rocq_alias into_sep_big_sepL2_cons]
instance intoSep_bigSepL2_cons [BI PROP] {A B}
    (Φ : Nat → A → B → PROP) (l₁ : List A) (x₁ : A) (l₁' : List A)
    (l₂ : List B) (x₂ : B) (l₂' : List B)
    [h₁ : IsCons l₁ x₁ l₁'] [h₂ : IsCons l₂ x₂ l₂'] :
    IntoSep ([∗list] k ↦ y₁;y₂ ∈ l₁;l₂, Φ k y₁ y₂)
      (Φ 0 x₁ x₂) ([∗list] k ↦ y₁;y₂ ∈ l₁';l₂', Φ (k + 1) y₁ y₂) where
  into_sep := by
    rw [h₁.is_cons, h₂.is_cons]
    exact BigSepL2.bigSepL2_cons.mp

@[rocq_alias into_sep_big_sepMS_disj_union]
instance intoSep_bigSepMS_disjUnion [BI PROP] {MS A}
    [LawfulFiniteMultiSet MS A] (Φ : A → PROP) (X₁ X₂ : MS) :
    IntoSep ([∗mset] y ∈ X₁ ⊎ X₂, Φ y) ([∗mset] y ∈ X₁, Φ y) ([∗mset] y ∈ X₂, Φ y) where
  into_sep := BigSepMS.bigSepMS_disjUnion.mp

/-! ### FromOr -/

@[rocq_alias from_or_or]
instance fromOr_or [BI PROP] (P1 P2 : PROP) : FromOr iprop(P1 ∨ P2) P1 P2 := ⟨.rfl⟩

@[rocq_alias from_or_pure]
instance fromOr_pure (φ ψ : Prop) [BI PROP] :
    FromOr (PROP := PROP) iprop(⌜φ ∨ ψ⌝) iprop(⌜φ⌝) iprop(⌜ψ⌝) where
  from_or := pure_or.1

@[rocq_alias from_or_affinely]
instance fromOr_affinely [BI PROP] (P Q1 Q2 : PROP) [h : FromOr P Q1 Q2] :
    FromOr iprop(<affine> P) iprop(<affine> Q1) iprop(<affine> Q2) where
  from_or := affinely_or.2.trans (affinely_mono h.1)

@[rocq_alias from_or_intuitionistically]
instance fromOr_intuitionistically [BI PROP] (P Q1 Q2 : PROP) [h : FromOr P Q1 Q2] :
    FromOr iprop(□ P) iprop(□ Q1) iprop(□ Q2) where
  from_or := intuitionistically_or.2.trans (intuitionistically_mono h.1)

@[rocq_alias from_or_absorbingly]
instance fromOr_absorbingly [BI PROP] (P Q1 Q2 : PROP) [h : FromOr P Q1 Q2] :
    FromOr iprop(<absorb> P) iprop(<absorb> Q1) iprop(<absorb> Q2) where
  from_or := absorbingly_or.2.trans (absorbingly_mono h.1)

@[rocq_alias from_or_persistently]
instance fromOr_persistently [BI PROP] (P Q1 Q2 : PROP) [h : FromOr P Q1 Q2] :
    FromOr iprop(<pers> P) iprop(<pers> Q1) iprop(<pers> Q2) where
  from_or := persistently_or.2.trans (persistently_mono h.1)

/-! ### IntoOr -/

@[rocq_alias into_or_or]
instance intoOr_or [BI PROP] (P Q : PROP) : IntoOr iprop(P ∨ Q) P Q := ⟨.rfl⟩

@[rocq_alias into_or_pure]
instance intoOr_pure (φ ψ : Prop) [BI PROP] :
    IntoOr (PROP := PROP) iprop(⌜φ ∨ ψ⌝) iprop(⌜φ⌝) iprop(⌜ψ⌝) where
  into_or := pure_or.2

@[rocq_alias into_or_affinely]
instance intoOr_affinely [BI PROP] (P Q1 Q2 : PROP) [h : IntoOr P Q1 Q2] :
    IntoOr iprop(<affine> P) iprop(<affine> Q1) iprop(<affine> Q2) where
  into_or := (affinely_mono h.1).trans affinely_or.1

@[rocq_alias into_or_intuitionistically]
instance intoOr_intuitionistically [BI PROP] (P Q1 Q2 : PROP) [h : IntoOr P Q1 Q2] :
    IntoOr iprop(□ P) iprop(□ Q1) iprop(□ Q2) where
  into_or := (intuitionistically_mono h.1).trans intuitionistically_or.1

@[rocq_alias into_or_absorbingly]
instance intoOr_absorbingly [BI PROP] (P Q1 Q2 : PROP) [h : IntoOr P Q1 Q2] :
    IntoOr iprop(<absorb> P) iprop(<absorb> Q1) iprop(<absorb> Q2) where
  into_or := (absorbingly_mono h.1).trans absorbingly_or.1

@[rocq_alias into_or_persistently]
instance intoOr_persistently [BI PROP] (P Q1 Q2 : PROP) [h : IntoOr P Q1 Q2] :
    IntoOr iprop(<pers> P) iprop(<pers> Q1) iprop(<pers> Q2) where
  into_or := (persistently_mono h.1).trans persistently_or.1

/-! ### IntoPersistently -/

@[rocq_alias into_persistent_persistently]
instance (priority := default + 20) intoPersistently_persistently (p : Bool) [BI PROP]
    (P Q : PROP) [h : IntoPersistently true P Q] : IntoPersistently p iprop(<pers> P) Q where
  into_persistently := persistentlyIf_persistently.1.trans h.1

@[rocq_alias into_persistent_affinely]
instance (priority := default + 20) intoPersistently_affinely (p : Bool) [BI PROP]
    (P Q : PROP) [h : IntoPersistently p P Q] : IntoPersistently p iprop(<affine> P) Q where
  into_persistently := (persistentlyIf_mono affinely_elim).trans h.1

@[rocq_alias into_persistent_intuitionistically]
instance (priority := default + 20) intoPersistently_intuitionistically (p : Bool) [BI PROP]
    (P Q : PROP) [h : IntoPersistently true P Q] : IntoPersistently p iprop(□ P) Q where
  into_persistently := persistentlyIf_intutitionistically.trans h.1

@[rocq_alias into_persistent_here]
instance (priority := default + 10) intoPersistently_self [BI PROP] (P : PROP) :
    IntoPersistently true P P := ⟨.rfl⟩

@[rocq_alias into_persistent_persistent]
instance (priority := default - 10) intoPersistently_persistent [BI PROP] (P : PROP)
    [h : Persistent P] : IntoPersistently false P P where
  into_persistently := h.1

/-! ### FromAffinely -/

@[ipm_backtrack, rocq_alias from_affinely_affine]
instance fromAffinely_affine [BI PROP] (P : PROP) [Affine P] : FromAffinely P P true where
  from_affinely := affinely_elim

@[rocq_alias from_affinely_default]
instance (priority := default - 50) fromAffinely_default [BI PROP] (P : PROP) :
    FromAffinely iprop(<affine> P) P true := ⟨.rfl⟩

@[rocq_alias from_affinely_intuitionistically]
instance (priority := default - 10) fromAffinely_intuitionistically [BI PROP] (P : PROP) :
    FromAffinely iprop(□ P) iprop(<pers> P) true := ⟨.rfl⟩

instance fromAffinely_self [BI PROP] (P : PROP) : FromAffinely P P false := ⟨.rfl⟩

/-! ### IntoAbsorbingly -/

@[rocq_alias into_absorbingly_True]
instance (priority := default + 30) intoAbsorbingly_true [BI PROP] :
    IntoAbsorbingly (PROP := PROP) iprop(True) emp where
  into_absorbingly := absorbingly_emp.2

@[ipm_backtrack, rocq_alias into_absorbingly_absorbing]
instance (priority := default + 20) intoAbsorbingly_absorbing [BI PROP]
    (P : PROP) [Absorbing P] : IntoAbsorbingly P P where
  into_absorbingly := absorbing_absorbingly.2

@[rocq_alias into_absorbingly_intuitionistically]
instance (priority := default + 10) intoAbsorbingly_intuitionistically [BI PROP] (P : PROP) :
    IntoAbsorbingly iprop(<pers> P) iprop(□ P) where
  into_absorbingly := absorbingly_intuitionistically.2

@[rocq_alias into_absorbingly_default]
instance (priority := default - 10) intoAbsorbingly_default [BI PROP] (P : PROP) :
    IntoAbsorbingly iprop(<absorb> P) P := ⟨.rfl⟩

/-! ### FromAssumption -/

@[rocq_alias from_assumption_exact]
instance (priority := default + 100) fromAssumption_exact (p : Bool) [BI PROP]
    ioP (P : PROP) : FromAssumption p ioP P P where
  from_assumption := intuitionisticallyIf_elim

@[rocq_alias from_assumption_persistently_r]
instance (priority := default + 30) fromAssumption_persistently_right [BI PROP] ioP (P Q : PROP)
    [h : FromAssumption true ioP P Q] : FromAssumption true ioP P iprop(<pers> Q) where
  from_assumption := (persistent (P := iprop(□ P))).trans (persistently_mono h.1)

@[rocq_alias from_assumption_affinely_r]
instance (priority := default + 30) fromAssumption_affinely_right [BI PROP] ioP (P Q : PROP)
    [h : FromAssumption true ioP P Q] : FromAssumption true ioP P iprop(<affine> Q) where
  from_assumption := affinely_idem.2.trans <| affinely_mono h.1

@[rocq_alias from_assumption_intuitionistically_r]
instance (priority := default + 30) fromAssumption_intuitionistically_right [BI PROP]
    ioP (P Q : PROP) [h : FromAssumption true ioP P Q] : FromAssumption true ioP P iprop(□ Q) where
  from_assumption := intuitionistically_idem.2.trans <| intuitionistically_mono h.1

@[rocq_alias from_assumption_absorbingly_r]
instance (priority := default + 20) fromAssumption_absorbingly_right (p : Bool) [BI PROP]
    ioP (P Q : PROP) [h : FromAssumption p ioP P Q] : FromAssumption p ioP P iprop(<absorb> Q) where
  from_assumption := absorbingly_intro.trans <| absorbingly_mono h.1

@[rocq_alias from_assumption_intuitionistically_l]
instance (priority := default + 20) fromAssumption_intuitionistically_left (p : Bool) [BI PROP]
    (P Q : PROP) [h : FromAssumption true .in P Q] : FromAssumption p .in iprop(□ P) Q where
  from_assumption := intuitionisticallyIf_intutitionistically.1.trans h.1

@[rocq_alias from_assumption_intuitionistically_l_true]
instance (priority := default + 20) fromAssumption_intuitionistically_l_true
    (p : Bool) [BI PROP] (P Q : PROP) [h : FromAssumption p .in P Q] :
    FromAssumption p .in iprop(□ P) Q where
  from_assumption := calc
    _ ⊢ □ □?p P := (intuitionisticallyIf_comm_iff (q := true)).1
    _ ⊢ □?p P   := intuitionistically_elim
    _ ⊢ Q       := h.from_assumption

@[rocq_alias from_assumption_persistently_l_true]
instance (priority := default + 30) fromAssumption_persistently_l_true [BI PROP] (P Q : PROP)
    [h : FromAssumption true .in P Q] : FromAssumption true .in iprop(<pers> P) Q where
  from_assumption := intuitionistically_persistently.1.trans h.1

@[rocq_alias from_assumption_persistently_l_false]
instance (priority := default + 30) fromAssumption_persistently_l_false [BI PROP] [BIAffine PROP]
    (P Q : PROP) [h : FromAssumption true .in P Q] : FromAssumption false .in iprop(<pers> P) Q where
  from_assumption := intuitionistically_iff_persistently.2.trans h.1

@[rocq_alias from_assumption_affinely_l_true]
instance (priority := default + 20) fromAssumption_affinely_left (p : Bool) [BI PROP]
    (P Q : PROP) [h : FromAssumption p .in P Q] : FromAssumption p .in iprop(<affine> P) Q where
  from_assumption := (intuitionisticallyIf_mono affinely_elim).trans h.1

set_option synthInstance.checkSynthOrder false in
@[rocq_alias from_assumption_forall]
instance (priority := default + 10) fromAssumption_forall (p : Bool) [BI PROP]
    (Φ : α → PROP) (x : α) (Q : PROP) [h : FromAssumption p .in (Φ x) Q] :
    FromAssumption p .in iprop(∀ x, Φ x) Q where
  from_assumption := (intuitionisticallyIf_mono <| forall_elim x).trans h.1

-- TODO: Do these two instances exist in Rocq? Do we want to have them?
set_option synthInstance.checkSynthOrder false in
@[ipm_backtrack]
instance fromAssumption_and_left [BI PROP] (p : Bool) (P1 P2 Q : PROP)
    [h : FromAssumption p .in P1 Q] : FromAssumption p .in iprop(P1 ∧ P2) Q where
  from_assumption :=
    match p, h with
    | true, h => calc
        _ ⊢ □ P1 ∧ □ P2 := intuitionistically_and.mp
        _ ⊢ □ P1        := and_elim_l
        _ ⊢ Q           := h.from_assumption
    | false, h => and_elim_l.trans h.from_assumption

set_option synthInstance.checkSynthOrder false in
@[ipm_backtrack]
instance fromAssumption_and_right [BI PROP] (p : Bool) (P1 P2 Q : PROP)
    [h : FromAssumption p .in P2 Q] : FromAssumption p .in iprop(P1 ∧ P2) Q where
  from_assumption :=
    match p, h with
    | true, h => calc
        _ ⊢ □ P1 ∧ □ P2 := intuitionistically_and.mp
        _ ⊢ □ P2        := and_elim_r
        _ ⊢ Q           := h.1
    | false, h => and_elim_r.trans h.1

@[rocq_alias from_assumption_tforall]
instance (priority := default + 10) fromAssumption_tforall {TT : Tele} (p : Bool) [BI PROP]
    (Φ : TT.Arg → PROP) (x : TT.Arg) (Q : PROP) [h : FromAssumption p .in (Φ x) Q] :
    FromAssumption p .in (BI.tforall Φ) Q where
  from_assumption :=
    (intuitionisticallyIf_mono <| (tforall_forall Φ).mp.trans (forall_elim x)).trans
    h.from_assumption

/-! ### IntoPure -/

@[rocq_alias into_pure_pure]
instance intoPure_pure (φ : Prop) [BI PROP] : IntoPure (PROP := PROP) iprop(⌜φ⌝) φ := ⟨.rfl⟩

@[rocq_alias into_pure_pure_and]
instance intoPure_pure_and (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP)
    [h1 : IntoPure P1 φ1] [h2 : IntoPure P2 φ2] : IntoPure iprop(P1 ∧ P2) (φ1 ∧ φ2) where
  into_pure := (and_mono h1.1 h2.1).trans pure_and.1

@[rocq_alias into_pure_pure_or]
instance intoPure_pure_or (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP)
    [h1 : IntoPure P1 φ1] [h2 : IntoPure P2 φ2] : IntoPure iprop(P1 ∨ P2) (φ1 ∨ φ2) where
  into_pure := (or_mono h1.1 h2.1).trans pure_or.1

@[rocq_alias into_pure_pure_impl]
instance intoPure_pure_imp (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP)
    [h1 : FromPure a P1 .out φ1] [or : TCOr (TCEq a false) (BIAffine PROP)]
    [h2 : IntoPure P2 φ2] : IntoPure iprop(P1 → P2) (φ1 → φ2) where
  into_pure := (imp_mono h1.1 h2.1).trans <| match a, or with
    | false, _ => pure_imp.2
    | true, TCOr.r => (imp_mono_left (affine_affinely _).2).trans pure_imp.2
    | true, TCOr.l (t:=heq) => nomatch heq

@[rocq_alias into_pure_exist]
instance intoPure_exists [BI PROP] (Φ : α → PROP) (φ : α → Prop)
    [h : ∀ x, IntoPure (Φ x) (φ x)] : IntoPure iprop(∃ x, Φ x) (∃ x, φ x) where
  into_pure := (exists_mono fun x => (h x).1).trans pure_exists.1

@[rocq_alias into_pure_pure_sep]
instance intoPure_pure_sep (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP)
    [h1 : IntoPure P1 φ1] [h2 : IntoPure P2 φ2] : IntoPure iprop(P1 ∗ P2) (φ1 ∧ φ2) where
  into_pure := calc
    _ ⊢ ⌜φ1⌝ ∗ ⌜φ2⌝ := sep_mono h1.into_pure h2.into_pure
    _ ⊢ ⌜φ1⌝ ∧ ⌜φ2⌝ := sep_and
    _ ⊢ ⌜φ1 ∧ φ2⌝   := pure_and.mp

@[rocq_alias into_pure_affinely]
instance intoPure_affinely [BI PROP] (P : PROP) (φ : Prop)
    [h : IntoPure P φ] : IntoPure iprop(<affine> P) φ where
  into_pure := affinely_elim.trans h.1

@[rocq_alias into_pure_intuitionistically]
instance intoPure_intuitionistically [BI PROP] (P : PROP) (φ : Prop)
    [h : IntoPure P φ] : IntoPure iprop(□ P) φ where
  into_pure := intuitionistically_elim.trans h.1

@[rocq_alias into_pure_absorbingly]
instance intoPure_absorbingly [BI PROP] (P : PROP) (φ : Prop)
    [h : IntoPure P φ] : IntoPure iprop(<absorb> P) φ where
  into_pure := (absorbingly_mono h.1).trans absorbingly_pure.1

@[rocq_alias into_pure_persistently]
instance intoPure_persistently [BI PROP] (P : PROP) (φ : Prop)
    [h : IntoPure P φ] : IntoPure iprop(<pers> P) φ where
  into_pure := (persistently_mono h.1).trans persistently_elim

/--
  The Rocq instance has `BiPureForall PROP` as a premise. This premise is not
  necessary in Lean, as `pure_forall` is provable classically for every BI,
  and thus `BiPureForall` is ignored in Lean.
-/
@[rocq_alias into_pure_forall]
instance intoPure_forall {α} [BI PROP] (Φ : α → PROP) (φ : α → Prop)
    [h : ∀ x, IntoPure (Φ x) (φ x)] : IntoPure iprop(∀ x, Φ x) (∀ x, φ x) where
  into_pure := (forall_mono fun x => (h x).into_pure).trans pure_forall.mpr

/--
  The Rocq instance has `BiPureForall PROP` as a premise. This premise is not
  necessary in Lean, as `(⌜φ1⌝ → ⌜φ2⌝) ⊢ ⌜φ1 → φ2⌝` is provable directly using
  `pure_imp` in Lean.
-/
@[rocq_alias into_pure_pure_wand]
instance intoPure_pure_wand [BI PROP] (a : Bool) (φ1 φ2 : Prop) (P1 P2 : PROP)
    [h1 : FromPure a P1 .out φ1] [h2 : IntoPure P2 φ2] :
    IntoPure iprop(P1 -∗ P2) (φ1 → φ2) where
  into_pure := by
    calc
      _ ⊢ <affine>?a ⌜φ1⌝ -∗ ⌜φ2⌝ := wand_mono h1.from_pure h2.into_pure
      _ ⊢ <affine> ⌜φ1⌝ -∗ ⌜φ2⌝   := wand_mono_left affinely_affinelyIf
      _ ⊢ ⌜φ1⌝ → ⌜φ2⌝             := imp_intro <| pure_elim_right fun hφ1 => ?_
      _ ⊢ ⌜φ1 → φ2⌝               := pure_imp.mpr
    calc
      _ ⊢ emp ∗ (<affine> ⌜φ1⌝ -∗ ⌜φ2⌝)           := emp_sep.mpr
      _ ⊢ <affine> ⌜φ1⌝ ∗ (<affine> ⌜φ1⌝ -∗ ⌜φ2⌝) :=
          sep_mono_left <| affinely_intro <| pure_intro hφ1
      _ ⊢ ⌜φ2⌝                                    := wand_elim_right

/--
  The Rocq instance has `BiPureForall PROP` as a premise. This premise is not
  necessary in Lean. See `intoPure_forall`.
-/
@[rocq_alias into_pure_tforall]
instance intoPure_tforall {TT : Tele} [BI PROP] (Φ : TT.Arg → PROP) (φ : TT.Arg → Prop)
    [h : ∀ x, IntoPure (Φ x) (φ x)] : IntoPure iprop(∀.. x, Φ x) (∀.. x, φ x) where
  into_pure := calc
    _ ⊢ ∀ x, Φ x         := (tforall_forall Φ).mp
    _ ⊢ ∀ x, ⌜φ x⌝       := forall_mono fun x => (h x).into_pure
    _ ⊢ ⌜∀ x, φ x⌝       := pure_forall.mpr
    _ ⊢ ⌜Tele.tforall φ⌝ := pure_mono (Tele.tforall_forall φ).mpr

@[rocq_alias into_pure_texist]
instance intoPure_texist {TT : Tele} [BI PROP] (Φ : TT.Arg → PROP) (φ : TT.Arg → Prop)
    [h : ∀ x, IntoPure (Φ x) (φ x)] : IntoPure iprop(∃.. x, Φ x) (∃.. x, φ x) where
  into_pure := calc
    _ ⊢ ∃ x, Φ x        := (texist_exist Φ).mp
    _ ⊢ ∃ x, ⌜φ x⌝      := exists_mono fun x => (h x).into_pure
    _ ⊢ ⌜∃ x, φ x⌝      := pure_exists.mp
    _ ⊢ ⌜Tele.texist φ⌝ := pure_mono (Tele.texist_exist φ).mpr

@[rocq_alias into_pure_big_sepL]
instance intoPure_bigSepL [BI PROP] {A} (Φ : Nat → A → PROP)
    (φ : Nat → A → Prop) (l : List A) [h : ∀ k x, IntoPure (Φ k x) (φ k x)] :
    IntoPure ([∗list] k ↦ x ∈ l, Φ k x) (∀ k x, l[k]? = some x → φ k x) where
  into_pure := (BigSepL.bigSepL_mono fun _ => (h ..).into_pure).trans BigSepL.bigSepL_pure_intro

@[rocq_alias into_pure_big_sepM]
instance intoPure_bigSepM [BI PROP] {K V : Type _} {M : Type _ → Type _}
    [LawfulFiniteMap M K] (Φ : K → V → PROP) (φ : K → V → Prop) (m : M V)
    [h : ∀ k x, IntoPure (Φ k x) (φ k x)] :
    IntoPure ([∗map] k ↦ x ∈ m, Φ k x) (PartialMap.all φ m) where
  into_pure := (BigSepM.bigSepM_mono fun _ => (h ..).into_pure).trans BigSepM.bigSepM_pure_intro

@[rocq_alias into_pure_big_sepS]
instance intoPure_bigSepS [BI PROP] {S A} [LawfulFiniteSet S A]
    (Φ : A → PROP) (φ : A → Prop) (X : S) [h : ∀ x, IntoPure (Φ x) (φ x)] :
    IntoPure ([∗set] y ∈ X, Φ y) (∀ y, y ∈ X → φ y) where
  into_pure := (BigSepS.bigSepS_mono fun _ => (h _).into_pure).trans BigSepS.bigSepS_pure_intro

@[rocq_alias into_pure_big_sepMS]
instance intoPure_bigSepMS [BI PROP] {MS A} [LawfulFiniteMultiSet MS A]
    (Φ : A → PROP) (φ : A → Prop) (X : MS) [h : ∀ x, IntoPure (Φ x) (φ x)] :
    IntoPure ([∗mset] y ∈ X, Φ y) (∀ y, y ∈ X → φ y) where
  into_pure := (BigSepMS.bigSepMS_mono fun _ => (h _).into_pure).trans BigSepMS.bigSepMS_pure_intro

/-! ### FromPure -/

@[rocq_alias from_pure_emp]
instance fromPure_emp [BI PROP] : FromPure (PROP := PROP) true emp ioφ True where
  from_pure := affinely_true.1

@[rocq_alias from_pure_pure]
instance fromPure_pure [BI PROP] (φ : Prop) :
    FromPure (PROP := PROP) false iprop(⌜φ⌝) ioφ φ where
  from_pure := .rfl

@[rocq_alias from_pure_pure_and]
instance fromPure_pure_and (a1 a2 : Bool) (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP)
    [h1 : FromPure a1 P1 io φ1] [h2 : FromPure a2 P2 io φ2] :
    FromPure (a1 || a2) iprop(P1 ∧ P2) io (φ1 ∧ φ2) where
  from_pure := by
    calc
      _ ⊢ <affine>?(a1 || a2) (⌜φ1⌝ ∧ ⌜φ2⌝) := affinelyIf_mono pure_and.2
      _ ⊢ <affine>?(a1 || a2) ⌜φ1⌝ ∧ <affine>?(a1 || a2) ⌜φ2⌝ := affinelyIf_and.1
      _ ⊢ P1 ∧ P2 := and_mono ((affinelyIf_flag_mono ?_).trans h1.1)
                              ((affinelyIf_flag_mono ?_).trans h2.1) <;> simp_all

@[rocq_alias from_pure_pure_or]
instance fromPure_pure_or (a1 a2 : Bool) (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP)
    [h1 : FromPure a1 P1 io φ1] [h2 : FromPure a2 P2 io φ2] :
    FromPure (a1 || a2) iprop(P1 ∨ P2) io (φ1 ∨ φ2) where
  from_pure := by
    calc
      _ ⊢ <affine>?(a1 || a2) (⌜φ1⌝ ∨ ⌜φ2⌝) := affinelyIf_mono pure_or.2
      _ ⊢ <affine>?(a1 || a2) ⌜φ1⌝ ∨ <affine>?(a1 || a2) ⌜φ2⌝ := affinelyIf_or.1
      _ ⊢ P1 ∨ P2 := or_mono ((affinelyIf_flag_mono ?_).trans h1.1)
                             ((affinelyIf_flag_mono ?_).trans h2.1) <;> simp_all

@[rocq_alias from_pure_pure_impl]
instance fromPure_pure_imp (a : Bool) (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP)
    [h1 : IntoPure P1 φ1] [h2 : FromPure a P2 io φ2] : FromPure a iprop(P1 → P2) io (φ1 → φ2) where
  from_pure := calc
    _ ⊢ <affine>?a (⌜φ1⌝ → ⌜φ2⌝) := affinelyIf_mono pure_imp.mp
    _ ⊢ ⌜φ1⌝ → <affine>?a ⌜φ2⌝   :=
        imp_intro <| affinelyIf_and_left.mp.trans (affinelyIf_mono imp_elim_left)
    _ ⊢ P1 → P2                  := imp_mono h1.into_pure h2.from_pure

@[rocq_alias from_pure_exist]
instance fromPure_exists (a : Bool) [BI PROP] (Φ : α → PROP) (φ : α → Prop)
    [h : ∀ x, FromPure a iprop(Φ x) io (φ x)] : FromPure a iprop(∃ x, Φ x) io (∃ x, φ x) where
  from_pure := calc
    _ ⊢ <affine>?a ∃ x, ⌜φ x⌝ := affinelyIf_mono pure_exists.mpr
    _ ⊢ ∃ x, <affine>?a ⌜φ x⌝ := affinelyIf_exists.mp
    _ ⊢ ∃ a, Φ a              := exists_mono fun x => (h x).from_pure

@[rocq_alias from_pure_forall]
instance fromPure_forall (a : Bool) [BI PROP] (Φ : α → PROP) (φ : α → Prop)
    [h : ∀ x, FromPure a iprop(Φ x) io (φ x)] : FromPure a iprop(∀ x, Φ x) io (∀ x, φ x) where
  from_pure := calc
    _ ⊢ <affine>?a ∀ x, ⌜φ x⌝ := affinelyIf_mono pure_forall.1
    _ ⊢ ∀ x, <affine>?a ⌜φ x⌝ := affinelyIf_forall
    _ ⊢ ∀ a, Φ a              := forall_mono fun x => (h x).1

@[rocq_alias from_pure_pure_sep_true]
instance fromPure_pure_sep_true (a1 a2 : Bool) (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP)
    [h1 : FromPure a1 P1 io φ1] [h2 : FromPure a2 P2 io φ2] :
    FromPure (a1 && a2) iprop(P1 ∗ P2) io (φ1 ∧ φ2) where
  from_pure := by
    calc
      _ ⊢ <affine>?(a1 && a2) (⌜φ1⌝ ∧ ⌜φ2⌝) := affinelyIf_mono pure_and.2
      _ ⊢@{PROP} <affine>?a1 ⌜φ1⌝ ∗ <affine>?a2 ⌜φ2⌝ := ?_
      _ ⊢ P1 ∗ P2 := sep_mono h1.1 h2.1
    exact match a1, a2 with
      | false, false => persistent_and_sep_mp
      | false, true => persistent_and_affinely_sep_right.1
      | true, false => persistent_and_affinely_sep_left.1
      | true, true => affinely_and.1.trans persistent_and_sep_mp

@[rocq_alias from_pure_pure_wand]
instance fromPure_pure_wand (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP)
    [h1 : IntoPure P1 φ1] [h2 : FromPure a P2 io φ2] [or : TCOr (TCEq a false) (Affine P1)] :
    FromPure a iprop(P1 -∗ P2) io (φ1 → φ2) where
  from_pure := match a, or, h2 with
    | false, _, h2 => pure_wand_mpr.trans (wand_mono h1.1 h2.1)
    | true, TCOr.r, h2 => by
      refine (wand_intro ?_).trans (wand_mono_right h2.1)
      calc
        _ ⊢ ⌜φ1 → φ2⌝ ∧ P1            := persistent_and_affinely_sep_left.2
        _ ⊢ ⌜φ1 → φ2⌝ ∧ <affine> P1   := and_mono_right (affine_affinely P1).2
        _ ⊢ <affine> (⌜φ1 → φ2⌝ ∧ P1) := affinely_and_right.1
        _ ⊢ <affine> ⌜φ2⌝             :=
            affinely_mono <| (and_mono pure_imp.1 h1.1).trans imp_elim_left
    | true, .l (t := h_teq), _ => nomatch h_teq

@[rocq_alias from_pure_persistently]
instance fromPure_persistently [BI PROP] (P : PROP) (a : Bool) (φ : Prop)
    [h : FromPure a P io φ] : FromPure false iprop(<pers> P) io φ where
  from_pure := calc
    _ ⊢ ⌜φ⌝      := affinelyIf_elim
    _ ⊢@{PROP} <pers> ⌜φ⌝ := persistently_pure.2
    _ ⊢ <pers> <affine> ⌜φ⌝ := persistently_affinely.2
    _ ⊢ <pers> P := persistently_mono <| affinely_affinelyIf.trans h.1

@[rocq_alias from_pure_affinely_true]
instance fromPure_affinely_true (a : Bool) [BI PROP] (P : PROP) (φ : Prop)
    [h : FromPure a P io φ] : FromPure true iprop(<affine> P) io φ where
  from_pure := affinely_idem.2.trans <| affinely_mono <| affinely_affinelyIf.trans h.1

@[rocq_alias from_pure_intuitionistically_true]
instance fromPure_intuitionistically_true (a : Bool) [BI PROP] (P : PROP) (φ : Prop)
    [h : FromPure a P io φ] : FromPure true iprop(□ P) io φ where
  from_pure := calc
    _ ⊢ □ <affine> ⌜φ⌝            := intuitionistically_of_intuitionistic.2
    _ ⊢ □ <affine> <affine>?a ⌜φ⌝ :=
        intuitionistically_mono <| affinely_idem.2.trans <| affinely_mono <| affinely_affinelyIf
    _ ⊢ □ <affine>?a ⌜φ⌝          := intuitionistically_affinely.1
    _ ⊢ □ P                       := intuitionistically_mono h.1

@[rocq_alias from_pure_absorbingly]
instance fromPure_absorbingly (a : Bool) [BI PROP] (P : PROP) (φ : Prop)
    [h : FromPure a P io φ] : FromPure false iprop(<absorb> P) io φ where
  from_pure := absorbingly_affinely_intro_of_persistent.trans <|
    absorbingly_mono <| affinely_affinelyIf.trans h.1

@[rocq_alias from_pure_tforall]
instance fromPure_tforall {TT : Tele} (a : Bool) [BI PROP] (Φ : TT.Arg → PROP)
    (φ : TT.Arg → Prop) [h : ∀ x, FromPure a (Φ x) io (φ x)] :
    FromPure a iprop(∀.. x, Φ x) io (∀.. x, φ x) where
  from_pure := calc
    _ ⊢ <affine>?a ⌜∀ x, φ x⌝ := affinelyIf_mono <| pure_mono (Tele.tforall_forall φ).mp
    _ ⊢ <affine>?a ∀ x, ⌜φ x⌝ := affinelyIf_mono pure_forall.mp
    _ ⊢ ∀ x, <affine>?a ⌜φ x⌝ := affinelyIf_forall
    _ ⊢ ∀ x, Φ x              := forall_mono fun x => (h x).from_pure
    _ ⊢ tforall Φ             := (tforall_forall Φ).mpr

@[rocq_alias from_pure_texist]
instance fromPure_texist {TT : Tele} (a : Bool) [BI PROP] (Φ : TT.Arg → PROP)
    (φ : TT.Arg → Prop) [h : ∀ x, FromPure a (Φ x) io (φ x)] :
    FromPure a iprop(∃.. x, Φ x) io (∃.. x, φ x) where
  from_pure := calc
    _ ⊢ <affine>?a ⌜∃ x, φ x⌝ := affinelyIf_mono <| pure_mono (Tele.texist_exist φ).mp
    _ ⊢ <affine>?a ∃ x, ⌜φ x⌝ := affinelyIf_mono pure_exists.mpr
    _ ⊢ ∃ x, <affine>?a ⌜φ x⌝ := affinelyIf_exists.mp
    _ ⊢ ∃ x, Φ x              := exists_mono fun x => (h x).from_pure
    _ ⊢ texist Φ              := (texist_exist Φ).mpr

@[rocq_alias from_pure_big_sepL]
instance fromPure_bigSepL (a : Bool) [BI PROP] {A} (Φ : Nat → A → PROP) io
    (φ : Nat → A → Prop) (l : List A)
    [h : ∀ k x, FromPure a (Φ k x) io (φ k x)] [or : TCOr (TCEq a true) (BIAffine PROP)] :
    FromPure a ([∗list] k ↦ x ∈ l, Φ k x) io (∀ k x, l[k]? = some x → φ k x) where
  from_pure := match a, or, h with
    | true, _, h =>
      BigSepL.bigSepL_affinely_pure_elim.trans <| BigSepL.bigSepL_mono fun _ => (h ..).from_pure
    | false, TCOr.r, h =>
      BigSepL.bigSepL_pure.mpr.trans <| BigSepL.bigSepL_mono fun _ => (h ..).from_pure
    | false, TCOr.l (t := heq), _ => nomatch heq

@[rocq_alias from_pure_big_sepM]
instance fromPure_bigSepM (a : Bool) [BI PROP] {K V : Type _} {M : Type _ → Type _}
    [LawfulFiniteMap M K] (Φ : K → V → PROP) (φ : K → V → Prop) (m : M V) io
    [h : ∀ k x, FromPure a (Φ k x) io (φ k x)] [or : TCOr (TCEq a true) (BIAffine PROP)] :
    FromPure a ([∗map] k ↦ x ∈ m, Φ k x) io (PartialMap.all φ m) where
  from_pure := match a, or, h with
    | true, _, h =>
      BigSepM.bigSepM_affinely_pure_elim.trans <| BigSepM.bigSepM_mono fun _ => (h ..).from_pure
    | false, TCOr.r, h =>
      BigSepM.bigSepM_pure.mpr.trans <| BigSepM.bigSepM_mono fun _ => (h ..).from_pure
    | false, TCOr.l (t := heq), _ => nomatch heq

@[rocq_alias from_pure_big_sepS]
instance fromPure_bigSepS (a : Bool) [BI PROP] {S A : Type _} [LawfulFiniteSet S A]
    (Φ : A → PROP) (φ : A → Prop) (X : S) io
    [h : ∀ x, FromPure a (Φ x) io (φ x)] [or : TCOr (TCEq a true) (BIAffine PROP)] :
    FromPure a ([∗set] y ∈ X, Φ y) io (∀ y, y ∈ X → φ y) where
  from_pure := match a, or, h with
    | true, _, h =>
      BigSepS.bigSepS_affinely_pure_elim.trans <| BigSepS.bigSepS_mono fun _ => (h _).from_pure
    | false, TCOr.r, h =>
      BigSepS.bigSepS_pure.mpr.trans <| BigSepS.bigSepS_mono fun _ => (h _).from_pure
    | false, TCOr.l (t := heq), _ => nomatch heq

@[rocq_alias from_pure_big_sepMS]
instance fromPure_bigSepMS (a : Bool) [BI PROP] {MS A : Type _}
    [LawfulFiniteMultiSet MS A] (Φ : A → PROP) (φ : A → Prop) (X : MS) io
    [h : ∀ x, FromPure a (Φ x) io (φ x)] [or : TCOr (TCEq a true) (BIAffine PROP)] :
    FromPure a ([∗mset] y ∈ X, Φ y) io (∀ y, y ∈ X → φ y) where
  from_pure := match a, or, h with
    | true, _, h =>
      BigSepMS.bigSepMS_affinely_pure_elim.trans <| BigSepMS.bigSepMS_mono fun _ => (h _).from_pure
    | false, TCOr.r, h =>
      BigSepMS.bigSepMS_pure.mpr.trans <| BigSepMS.bigSepMS_mono fun _ => (h _).from_pure
    | false, TCOr.l (t := heq), _ => nomatch heq

/-! ### FromModal -/

@[rocq_alias from_modal_affinely]
instance (priority := default + 10) fromModal_affinely [BI PROP] io (P : PROP) :
  FromModal io modality_affinely True iprop(<affine> P) iprop(<affine> P) P where
  from_modal := by simp [modality_affinely]

@[rocq_alias from_modal_persistently]
instance (priority := default + 10) fromModal_persistently [BI PROP] io (P : PROP) :
  FromModal io modality_persistently True iprop(<pers> P) iprop(<pers> P) P where
  from_modal := by simp [modality_persistently]

@[rocq_alias from_modal_intuitionistically]
instance (priority := default + 20) fromModal_intuitionistically [BI PROP] io (P : PROP) :
    FromModal io modality_intuitionistically True iprop(□ P) iprop(□ P) P where
  from_modal := by simp [modality_intuitionistically]

@[ipm_backtrack, rocq_alias from_modal_intuitionistically_affine_bi]
instance (priority := default + 30) fromModal_intuitionistically_affine_bi
    [BI PROP] [BIAffine PROP] (P : PROP) io :
    FromModal io modality_persistently True iprop(□ P) iprop(□ P) P where
  from_modal := by simp [modality_persistently]; apply intuitionistically_iff_persistently.2

@[rocq_alias from_modal_absorbingly]
instance fromModal_absorbingly [BI PROP] (P : PROP) io :
  FromModal io modality_id True iprop(<absorb> P) iprop(<absorb> P) P where
  from_modal := by simp [modality_id]; apply absorbingly_intro

/-! ### ElimModal -/

@[rocq_alias elim_modal_wand]
instance elimModal_wand [BI PROP] φ p p' io (P P' Q Q' R : PROP)
    [h : ElimModal φ p io p' P P' Q Q'] :
    ElimModal φ p io p' P P' iprop(R -∗ Q) iprop(R -∗ Q') where
  elim_modal hφ := by
    refine wand_intro ?_
    calc
      _ ⊢ □?p P ∗ (□?p' P' -∗ R -∗ Q') ∗ R := sep_assoc.1
      _ ⊢ □?p P ∗ (□?p' P' -∗ Q') :=
          sep_mono_right $ wand_elim $ wand_intro_left $ wand_intro_left $ sep_assoc.2.trans ?_
      _ ⊢ Q := h.1 hφ
    calc
      _ ⊢ (R ∗ □?p' P') ∗ (□?p' P' -∗ R -∗ Q') := sep_mono_left sep_comm.1
      _ ⊢ R ∗ □?p' P' ∗ (□?p' P' -∗ R -∗ Q')   := sep_assoc.1
      _ ⊢ Q'                                   := wand_elim_swap $ wand_elim_swap .rfl

@[rocq_alias elim_modal_wandM]
instance elimModal_wandM [BI PROP] φ p p' io (P P' Q Q' : PROP) (mR : Option PROP)
    [h : ElimModal φ p io p' P P' Q Q'] :
    ElimModal φ p io p' P P' iprop(mR -∗? Q) iprop(mR -∗? Q') where
  elim_modal hφ := calc
    _ ⊢ □?p P ∗ (□?p' P' -∗ mR.getD iprop(emp) -∗ Q') :=
        sep_mono_right <| wand_mono_right wandM_sound.mp
    _ ⊢ mR.getD iprop(emp) -∗ Q                       :=
        (elimModal_wand φ p p' io P P' Q Q' (mR.getD emp)).elim_modal hφ
    _ ⊢ mR -∗? Q                                      := wandM_sound.mpr

@[rocq_alias elim_modal_forall]
instance elimModal_forall [BI PROP] φ p p' io P P' (Φ Ψ : α → PROP)
    [h : ∀ x, ElimModal φ p io p' P P' (Φ x) (Ψ x)] :
    ElimModal φ p io p' P P' iprop(∀ x, Φ x) iprop(∀ x, Ψ x) where
  elim_modal hφ := forall_intro λ a =>
    (sep_mono_right (wand_mono_right (forall_elim a))).trans ((h a).1 hφ)

@[rocq_alias elim_modal_absorbingly_here]
instance elimModal_absorbingly_here [BI PROP] p io (P Q : PROP) [Absorbing Q] :
    ElimModal True p io false iprop(<absorb> P) P Q Q where
  elim_modal _ := calc
    _ ⊢ <absorb> P ∗ (P -∗ Q)   := sep_mono_left intuitionisticallyIf_elim
    _ ⊢ <absorb> (P ∗ (P -∗ Q)) := absorbingly_sep_left.1
    _ ⊢ P ∗ (P -∗ Q)            := absorbing_absorbingly.1
    _ ⊢ Q                       := wand_elim_right

@[rocq_alias elim_modal_tforall]
instance elimModal_tforall {TT : Tele} [BI PROP] φ p p' io (P P' : PROP)
    (Φ Ψ : TT.Arg → PROP) [h : ∀ x, ElimModal φ p io p' P P' (Φ x) (Ψ x)] :
    ElimModal φ p io p' P P' iprop(∀.. x, Φ x) iprop(∀.. x, Ψ x) where
  elim_modal hφ := by
    refine .trans ?_ (tforall_forall Φ).mpr
    refine forall_intro fun x => ?_
    exact (sep_mono_right <| wand_mono_right <|
      (tforall_forall Ψ).mp.trans (forall_elim x)).trans ((h x).elim_modal hφ)

/-! ### AddModal -/

theorem addModal_wand_mp [BI PROP] {P P' Q R : PROP} [h : AddModal P P' Q] :
    P ∗ (P' -∗ R -∗ Q) ⊢ R -∗ Q := by
  have h1 : (P' -∗ R -∗ Q) ∗ R ⊢ P' -∗ Q := by
    apply wand_intro
    calc
      _ ⊢ (P' -∗ R -∗ Q) ∗ R ∗ P'   := sep_assoc.mp
      _ ⊢ (P' -∗ R -∗ Q) ∗ P' ∗ R   := sep_mono_right sep_comm.mp
      _ ⊢ ((P' -∗ R -∗ Q) ∗ P') ∗ R := sep_assoc.mpr
      _ ⊢ (R -∗ Q) ∗ R              := sep_mono_left wand_elim_left
      _ ⊢ Q                         := wand_elim_left
  apply wand_intro
  calc
    _ ⊢ P ∗ (P' -∗ R -∗ Q) ∗ R := sep_assoc.mp
    _ ⊢ P ∗ (P' -∗ Q)          := sep_mono_right h1
    _ ⊢ Q                      := h.add_modal

@[rocq_alias add_modal_wand]
instance addModal_wand [BI PROP] (P P' Q R : PROP) [h : AddModal P P' Q] :
    AddModal P P' iprop(R -∗ Q) where
  add_modal := addModal_wand_mp

@[rocq_alias add_modal_wandM]
instance addModal_wandM [BI PROP] (P P' Q : PROP) (mR : Option PROP)
    [h : AddModal P P' Q] : AddModal P P' iprop(mR -∗? Q) where
  add_modal := by
    cases mR with
    | none => exact h.add_modal
    | some R => exact addModal_wand_mp

@[rocq_alias add_modal_forall]
instance addModal_forall {A : Type} [BI PROP] (P P' : PROP) (Φ : A → PROP)
    [h : ∀ x, AddModal P P' (Φ x)] : AddModal P P' iprop(∀ x, Φ x) where
  add_modal := by
    apply forall_intro
    intro a
    exact (sep_mono_right (wand_mono .rfl (forall_elim a))).trans (h a).add_modal

@[rocq_alias add_modal_tforall]
instance addModal_tforall {TT : Tele} [BI PROP] (P P' : PROP) (Φ : TT.Arg → PROP)
    [h : ∀ x, AddModal P P' (Φ x)] : AddModal P P' (BI.tforall Φ) where
  add_modal := by
    refine .trans ?_ (tforall_forall Φ).mpr
    refine forall_intro fun x => ?_
    exact (sep_mono_right <| wand_mono_right <|
      (tforall_forall Φ).mp.trans (forall_elim x)).trans (h x).add_modal

/-! ### CombineSepAs -/

@[rocq_alias maybe_combine_sep_as_default]
instance (priority := default - 20) combineSepAs_default [BI PROP] (P Q : PROP) :
    CombineSepAs P Q iprop(P ∗ Q) where
  combine_sep_as := by rfl

@[rocq_alias maybe_combine_sep_as_affinely]
instance combineSepAs_affinely [BI PROP] (Q1 Q2 P : PROP)
    [h : CombineSepAs Q1 Q2 P] :
    CombineSepAs iprop(<affine> Q1) iprop(<affine> Q2) iprop(<affine> P) where
  combine_sep_as := affinely_sep_mpr.trans (affinely_mono h.combine_sep_as)

@[rocq_alias maybe_combine_sep_as_intuitionistically]
instance combineSepAs_intuitionistically [BI PROP] (Q1 Q2 P : PROP)
    [h : CombineSepAs Q1 Q2 P] :
    CombineSepAs iprop(□ Q1) iprop(□ Q2) iprop(□ P) where
  combine_sep_as := intuitionistically_sep_mpr.trans (intuitionistically_mono h.combine_sep_as)

@[rocq_alias maybe_combine_sep_as_absorbingly]
instance combineSepAs_absorbingly [BI PROP] (Q1 Q2 P : PROP)
    [h : CombineSepAs Q1 Q2 P] :
    CombineSepAs iprop(<absorb> Q1) iprop(<absorb> Q2) iprop(<absorb> P) where
  combine_sep_as :=
    (absorbingly_sep (P := Q1) (Q := Q2)).mpr.trans (absorbingly_mono h.combine_sep_as)

@[rocq_alias maybe_combine_sep_as_persistently]
instance combineSepAs_persistently [BI PROP] (Q1 Q2 P : PROP)
    [h : CombineSepAs Q1 Q2 P] :
    CombineSepAs iprop(<pers> Q1) iprop(<pers> Q2) iprop(<pers> P) where
  combine_sep_as := persistently_sep_mpr.trans (persistently_mono h.combine_sep_as)

/-! ### CombineSepGives -/

@[rocq_alias combine_sep_as_affinely]
instance combineSepGives_affinely [BI PROP] (Q1 Q2 P : PROP)
    [h : CombineSepGives Q1 Q2 P] :
    CombineSepGives iprop(<affine> Q1) iprop(<affine> Q2) P where
  combine_sep_gives := calc
    <affine> Q1 ∗ <affine> Q2 ⊢ <affine> (Q1 ∗ Q2) := affinely_sep_mpr
    _                         ⊢ <affine> <pers> P  := affinely_mono h.combine_sep_gives
    _                         ⊢ <pers> P           := affinely_elim

@[rocq_alias combine_sep_as_intuitionistically]
instance combineSepGives_intuitionistically [BI PROP] (Q1 Q2 P : PROP)
    [h : CombineSepGives Q1 Q2 P] :
    CombineSepGives iprop(□ Q1) iprop(□ Q2) P where
  combine_sep_gives := calc
    □ Q1 ∗ □ Q2 ⊢ □ (Q1 ∗ Q2) := intuitionistically_sep_mpr
    _           ⊢ □ <pers> P  := intuitionistically_mono h.combine_sep_gives
    _           ⊢ <pers> P    := intuitionistically_elim

@[rocq_alias combine_sep_as_absorbingly]
instance combineSepGives_absorbingly [BI PROP] (Q1 Q2 P : PROP)
    [h : CombineSepGives Q1 Q2 P] :
    CombineSepGives iprop(<absorb> Q1) iprop(<absorb> Q2) P where
  combine_sep_gives := calc
    <absorb> Q1 ∗ <absorb> Q2 ⊢ <absorb> (Q1 ∗ Q2) := absorbingly_sep.mpr
    _                         ⊢ <absorb> <pers> P  := absorbingly_mono h.combine_sep_gives
    _                         ⊢ <pers> P           := absorbingly_persistently.mp

@[rocq_alias combine_sep_as_persistently]
instance combineSepGives_persistently [BI PROP] (Q1 Q2 P : PROP)
    [h : CombineSepGives Q1 Q2 P] :
    CombineSepGives iprop(<pers> Q1) iprop(<pers> Q2) iprop(<pers> P) where
  combine_sep_gives := persistently_sep_mpr.trans (persistently_mono h.combine_sep_gives)

/-! ### ElimInv -/

@[rocq_alias elim_inv_acc_without_close]
instance elimInv_acc_without_close [BI PROP] {X : Type}
    φ1 φ2 Pinv Pin (M1 M2 : PROP → PROP) α β mγ Q (Q' : X → PROP)
    [h1 : IntoAcc Pinv φ1 Pin M1 M2 α β mγ]
    [h2 : ElimAcc φ2 M1 M2 α β mγ Q Q'] :
    ElimInv (φ1 ∧ φ2) X Pinv Pin α false none Q Q' where
  elim_inv := by
    intro ⟨hφ1, _⟩
    iintro ⟨Hinv, Hin, Hcont⟩
    iapply h2.elim_acc $$ [Hcont]
    · assumption
    · simp only [Option.getD_none, sep_emp.to_eq]; iassumption
    · iapply h1.into_acc hφ1 $$ Hinv Hin

@[rocq_alias elim_inv_acc_with_close]
instance elimInv_acc_with_close [BI PROP] {X : Type}
    φ1 φ2 Pinv Pin (M1 M2 : PROP → PROP) α β mγ Q (Q' : PROP)
    [h1 : IntoAcc Pinv φ1 Pin M1 M2 α β mγ]
    [h2 : ∀ R, ElimModal φ2 false .in false (M1 R) R Q Q'] :
    ElimInv (φ1 ∧ φ2) X Pinv Pin α true
            (some (fun x => iprop(β x -∗ M2 (mγ x |>.getD emp))))
            Q (fun _ => Q') where
  elim_inv := by
    intro ⟨hφ1, hφ2⟩
    have hAcc := h1.into_acc
    unfold accessor at hAcc
    iintro ⟨Hinv, Hin, Hcont⟩
    iapply (h2 _ |>.elim_modal hφ2)
    isplitl [Hinv Hin]
    · dsimp
      iapply hAcc hφ1 $$ Hinv Hin
    · dsimp
      iintro ⟨%_, Hα, Hclose⟩
      iapply Hcont
      isplitl [Hα] <;> iassumption

/-! ### IntoIH -/

@[rocq_alias into_ih_entails]
instance intoIH_entails [BI PROP] (P Q : PROP) : IntoIH (Entails' P Q) P Q where
  into_ih := λ hpq => intuitionistically_elim.trans hpq

@[rocq_alias into_ih_forall]
instance (priority := default - 2) intoIH_forall [BI PROP] (φ : α → Prop) (P : PROP) (Φ : α → PROP)
    [h : ∀ x, IntoIH (φ x) P (Φ x)] :
    IntoIH (∀ x, φ x) P (BI.forall Φ) where
  into_ih := by
    intro hφ
    apply forall_intro
    intro x
    exact (h x).into_ih (hφ x)

@[rocq_alias into_ih_impl]
instance (priority := default - 1) intoIH_imp [BI PROP] (φ ψ : Prop) (Δ P Q : PROP)
    [h1 : MakeAffinely iprop(⌜φ⌝) P]
    [h2 : IntoIH ψ Δ Q] :
    IntoIH (φ → ψ) Δ iprop(P -∗ Q) where
  into_ih := by
    intro hImp
    apply wand_intro
    refine (sep_mono_right h1.make_affinely.mpr).trans ?_
    refine persistent_and_affinely_sep_right.2.trans ?_
    exact pure_elim_right (fun hφ => h2.into_ih (hImp hφ))

#rocq_ignore into_ih_Forall
  "List.Forall does not exist in the core Lean libraries, and ∀ x ∈ l, p x is used instead"

/-- Support for induction principles whose IH is guarded by `List.Forall₂`, e.g.
    arising from mutual inductive types relating two lists element-wise. -/
@[rocq_alias into_ih_Forall2]
instance (priority := default - 2) intoIH_listForall₂ [BI PROP]
    (φ : α → β → Prop) (l1 : List α) (l2 : List β)
    (P : PROP) (Φ : α → β → PROP)
    [h : ∀ x1 x2, IntoIH (φ x1 x2) P (Φ x1 x2)] :
    IntoIH (List.Forall₂ φ l1 l2) P (bigSepL2 (fun _ x1 x2 => iprop(□ Φ x1 x2)) l1 l2) where
  into_ih := by
    intro h
    induction h with
    | nil => simp [bigSepL2, affine]
    | cons x xs ih =>
      simp [bigSepL2] at ⊢
      apply intuitionistically_sep_idem.mpr.trans
      refine sep_mono ?_ ?_
      · exact intuitionistically_intro_intuitionistically ((h _ _).into_ih x)
      · exact ih
