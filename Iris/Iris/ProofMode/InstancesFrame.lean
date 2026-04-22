/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
module

public import Iris.BI
public import Iris.ProofMode.Classes
public import Iris.ProofMode.ClassesMake
public meta import Iris.ProofMode.Expr
public import Iris.Std.TC

@[expose] public section

namespace Iris.ProofMode
open Qq Iris.BI Iris.Std

/- When framing [R] against itself, we leave [True] if possible since it is a weaker goal. Otherwise we leave [emp].
Only if all those options fail, we start decomposing [R]. -/
@[ipm_backtrack, rocq_alias frame_here_absorbing]
instance (priority := high + 10) frame_here_absorbing [BI PROP] p (R : PROP) [QuickAbsorbing R] : Frame p R R iprop(True) where
  frame := sep_comm.1.trans <| (sep_mono_r intuitionisticallyIf_elim).trans quick_absorbing.absorbing

@[ipm_backtrack, rocq_alias frame_here]
instance (priority := high + 5) frame_here [BI PROP] p (R : PROP) : Frame p R R iprop(emp) where
  frame := sep_emp.1.trans intuitionisticallyIf_elim

@[ipm_backtrack, rocq_alias frame_affinely_here_absorbing]
instance (priority := high + 10) frame_affinely_here_absorbing [BI PROP] p (R : PROP) [QuickAbsorbing R] : Frame p iprop(<affine> R) R iprop(True) where
  frame := sep_comm.1.trans <| (sep_mono_r (intuitionisticallyIf_elim.trans affinely_elim)).trans quick_absorbing.absorbing

@[ipm_backtrack, rocq_alias frame_affinely_here]
instance (priority := high + 10) frame_affinely_here [BI PROP] p (R : PROP) : Frame p iprop(<affine> R) R iprop(emp) where
  frame := sep_emp.1.trans (intuitionisticallyIf_elim.trans affinely_elim)

@[ipm_backtrack, rocq_alias frame_here_pure_persistent]
instance frame_here_pure_persistent [BI PROP] {a : Bool} {φ : Prop} {Q : PROP}
    [FromPure a Q φ] : Frame true iprop(⌜φ⌝) Q iprop(emp) where
  frame :=
    have h : □?true iprop(⌜φ⌝) ∗ emp ⊢ □ iprop(⌜φ⌝) := sep_emp.1
    h.trans (affinely_of_intuitionistically.trans (affinely_affinelyIf.trans from_pure))

@[ipm_backtrack, rocq_alias frame_here_pure]
instance frame_here_pure [BI PROP] {a : Bool} {φ : Prop} {Q : PROP}
    [h1 : FromPure a Q φ] [hor : TCOr (TCEq a false) (BIAffine PROP)] :
    Frame false iprop(⌜φ⌝) Q iprop(emp) where
  frame :=
    sep_emp.1.trans <|
    match hor with
    | @TCOr.l _ _ heq => by cases heq; refine h1.1
    | TCOr.r => (affinely_intro .rfl).trans <| affinely_affinelyIf.trans h1.1

@[ipm_backtrack, rocq_alias frame_wand]
instance frame_wand [BI PROP] p (R P1 P2 Q2 : PROP)
    [h : Frame p R P2 Q2] : Frame p R iprop(P1 -∗ P2) iprop(P1 -∗ Q2) where
  frame := wand_intro <| sep_assoc.1.trans <| (sep_mono_r wand_elim_l).trans h.frame

@[ipm_backtrack, rocq_alias frame_affinely]
instance frame_affinely [BI PROP] p (R P Q Q' : PROP)
    [hor : TCOr (TCEq p true) (QuickAffine R)]
    [h1 : Frame p R P Q] [h2 : MakeAffinely Q Q'] :
    Frame p R iprop(<affine> P) Q' where
  frame :=
    let h_aff : Affine iprop(□?p R) := match hor with
      | @TCOr.l _ _ heq => by cases heq; exact inferInstance
      | @TCOr.r _ _ hq => by have := hq.quick_affine; exact inferInstance
    (sep_mono_r h2.make_affinely.2).trans <|
    (sep_mono_l (affine_affinely _).symm.1).trans <|
    affinely_sep_2.trans <|
    affinely_mono h1.frame

@[ipm_backtrack, rocq_alias frame_intuitionistically]
instance frame_intuitionistically [BI PROP] (R P Q Q' : PROP)
    [h1 : Frame true R P Q] [h2 : MakeIntuitionistically Q Q'] :
    Frame true R iprop(□ P) Q' where
  frame :=
    (sep_mono_r h2.make_intuitionistically.2).trans <|
    (sep_mono_l intuitionistically_idem.2).trans <|
    intuitionistically_sep_2.trans <|
    intuitionistically_mono h1.frame

@[ipm_backtrack, rocq_alias frame_absorbingly]
instance frame_absorbingly [BI PROP] p (R P Q Q' : PROP)
    [h1 : Frame p R P Q] [h2 : MakeAbsorbingly Q Q'] :
    Frame p R iprop(<absorb> P) Q' where
  frame :=
    (sep_mono_r h2.make_absorbingly.2).trans <|
    absorbingly_sep_r.1.trans <|
    absorbingly_mono h1.frame

@[ipm_backtrack, rocq_alias frame_persistently]
instance frame_persistently [BI PROP] (R P Q Q' : PROP)
    [h1 : Frame true R P Q] [h2 : MakePersistently Q Q'] :
    Frame true R iprop(<pers> P) Q' where
  frame :=
    (sep_mono_r h2.make_persistently.2).trans <|
    (sep_mono_l persistent).trans <|
    persistently_sep_2.trans <|
    persistently_mono h1.frame

@[ipm_backtrack, rocq_alias frame_impl_persistent]
instance frame_impl_persistent [BI PROP] (R P1 P2 Q2 : PROP)
    [h : Frame true R P2 Q2] : Frame true R iprop(P1 → P2) iprop(P1 → Q2) where
  frame := imp_intro <|
    (and_mono_l persistently_and_intuitionistically_sep_l.2).trans <|
    and_assoc.1.trans <|
    (and_mono_r (and_comm.1.trans imp_elim_r)).trans <|
    persistently_and_intuitionistically_sep_l.1.trans h.frame

/- You may wonder why this uses [Persistent] and not [QuickPersistent].
The reason is that [QuickPersistent] is not needed anywhere else, and
even without [QuickPersistent], this instance avoids quadratic complexity:
we usually use the [Quick*] classes to not traverse the same term over and over
again, but here [P1] is encountered at most once. It is hence not worth adding
a new typeclass just for this extremely rarely used instance. -/
@[ipm_backtrack, rocq_alias frame_impl]
instance frame_impl [BI PROP] (R P1 P2 Q2 : PROP)
    [hp : Persistent P1] [ha : QuickAbsorbing P1]
    [h : Frame false R P2 Q2] : Frame false R iprop(P1 → P2) iprop(P1 → Q2) where
  frame :=
    have : Absorbing P1 := ha.quick_absorbing
    imp_intro <|
      persistent_and_affinely_sep_r.1.trans <|
      sep_assoc.1.trans <|
      (sep_mono_r (sep_comm.1.trans (persistent_and_affinely_sep_l.2.trans imp_elim_r))).trans <|
      h.frame

@[ipm_backtrack, rocq_alias frame_later]
instance frame_later [BI PROP] p (R R' P Q Q' : PROP)
    [h1 : IntoLaterN true 1 R' R] [h2 : Frame p R P Q] [h3 : MakeLaterN 1 Q Q'] :
    Frame p R' iprop(▷ P) Q' where
  frame :=
    (sep_mono_r h3.make_laterN.2).trans <|
    (sep_mono_l ((intuitionisticallyIf_mono h1.into_laterN).trans later_intuitionisticallyIf_2)).trans <|
    later_sep.2.trans <|
    later_mono h2.frame

@[ipm_backtrack, rocq_alias frame_laterN]
instance frame_laterN [BI PROP] p n (R R' P Q Q' : PROP)
    [h1 : IntoLaterN true n R' R] [h2 : Frame p R P Q] [h3 : MakeLaterN n Q Q'] :
    Frame p R' iprop(▷^[n] P) Q' where
  frame :=
    (sep_mono_r h3.make_laterN.2).trans <|
    (sep_mono_l ((intuitionisticallyIf_mono h1.into_laterN).trans (laterN_intuitionisticallyIf_2 n))).trans <|
    (laterN_sep n).2.trans <|
    laterN_mono n h2.frame

@[ipm_backtrack, rocq_alias frame_bupd]
instance frame_bupd [BI PROP] [BIUpdate PROP] p (R P Q Q' : PROP)
    [h : Frame p R P Q] [h2 : MakeBUpd Q Q'] : Frame p R iprop(|==> P) Q' where
  frame := (sep_mono .rfl h2.1.2).trans <| bupd_frame_l.trans (BIUpdate.mono h.frame)

@[ipm_backtrack, rocq_alias frame_fupd]
instance frame_fupd [BI PROP] [BIFUpdate PROP] p (E1 E2 : CoPset) (R P Q Q' : PROP)
    [h : Frame p R P Q] [h2 : MakeFUpd E1 E2 Q Q'] : Frame p R iprop(|={E1,E2}=> P) Q' where
  frame := (sep_mono .rfl h2.1.2).trans <| fupd_frame_l.trans (BIFUpdate.mono h.frame)

@[ipm_backtrack, rocq_alias frame_except_0]
instance frame_except_0 [BI PROP] p (R P Q Q' : PROP)
    [h1 : Frame p R P Q] [h2 : MakeExcept0 Q Q'] : Frame p R iprop(◇ P) Q' where
  frame :=
    (sep_mono_r h2.make_except0.2).trans <|
    (sep_mono_l except0_intro).trans <|
    except0_sep.2.trans <|
    except0_mono h1.frame


section tactic_theorems

@[rocq_alias maybe_frame_default_persistent]
theorem maybeFrame_default_persistent [BI PROP] (R P : PROP) :
  Frame true R P P where
  frame := sep_elim_r

@[rocq_alias maybe_frame_default]
theorem maybeFrame_default [BI PROP] (R P : PROP)
  [h : TCOr (Affine R) (Absorbing P)]:
  Frame false R P P where
  frame := by simp only [intuitionisticallyIf_false']; exact sep_elim_r

@[rocq_alias frame_sep_persistent_l]
theorem frame_sep_both [BI PROP] (R P1 P2 Q1 Q2 Q' : PROP)
  [h1 : Frame true R P1 Q1] [h2 : Frame true R P2 Q2] [MakeSep Q1 Q2 Q'] :
  Frame true R iprop(P1 ∗ P2) Q' where
  frame := (sep_mono_r make_sep.2).trans <|
    (sep_mono_l intuitionistically_sep_idem.2).trans <|
    sep_sep_sep_comm.1.trans <|
    sep_mono h1.frame h2.frame

@[rocq_alias frame_sep_l]
theorem frame_sep_l [BI PROP] p (R P1 P2 Q Q' : PROP)
  [h1 : Frame p R P1 Q] [h2 : MakeSep Q P2 Q'] :
  Frame p R iprop(P1 ∗ P2) Q' where
  frame := (sep_mono_r make_sep.2).trans <|
    sep_assoc.2.trans <|
    sep_mono_l h1.frame

@[rocq_alias frame_sep_r]
theorem frame_sep_r [BI PROP] p (R P1 P2 Q Q' : PROP)
  [h1 : Frame p R P2 Q] [h2 : MakeSep P1 Q Q'] :
  Frame p R iprop(P1 ∗ P2) Q' where
  frame :=(sep_mono_r make_sep.2).trans <|
    sep_left_comm.1.trans <|
    sep_mono_r h1.frame

@[rocq_alias frame_and]
theorem frame_and [BI PROP] p (R P1 P2 Q1 Q2 Q' : PROP)
  [h1 : Frame p R P1 Q1] [h2 : Frame p R P2 Q2] [h3 : MakeAnd Q1 Q2 Q'] :
  Frame p R iprop(P1 ∧ P2) Q' where
  frame := and_intro
    ((sep_mono_r (h3.make_and.2.trans and_elim_l)).trans h1.frame)
    ((sep_mono_r (h3.make_and.2.trans and_elim_r)).trans h2.frame)

@[rocq_alias frame_or]
theorem frame_or [BI PROP] p (R P1 P2 Q1 Q2 Q' : PROP)
  [h1 : Frame p R P1 Q1] [h2 : Frame p R P2 Q2] [h3 : MakeOr Q1 Q2 Q'] :
  Frame p R iprop(P1 ∨ P2) Q' where
  frame :=
    (sep_mono_r h3.make_or.2).trans <|
    sep_or_l.1.trans <|
    or_mono h1.frame h2.frame

end tactic_theorems

meta section tactics
open Lean

/-- corresponds to the MaybeFrame typeclass in Rocq -/
@[rocq_alias MaybeFrame']
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
    return .success q(frame_sep_l $p $R $P1 $P2 $Q1 $Q')
  else
    let Q2 : Q($prop) ← mkFreshExprMVarQ q($prop)
    let .some _ ← synthInstanceRecursiveQ q(Frame $p $R $P2 $Q2) |
      return .continue
    let Q' : Q($prop) ← mkFreshExprMVarQ q($prop)
    let .some _ ← synthInstanceRecursiveQ q(MakeSep $P1 $Q2 $Q') |
      throwError "MakeSep should always succeed"
    return .success q(frame_sep_r $p $R $P1 $P2 $Q2 $Q')

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
