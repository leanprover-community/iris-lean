/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
import Qq
import Iris.BI
import Iris.ProofMode.Classes
import Iris.Std

namespace Iris.ProofMode
open Iris.BI Iris.Std
open Lean Lean.Expr Lean.Meta Qq

@[match_pattern] def nameAnnotation := `name
@[match_pattern] def uniqAnnotation := `uniq

def parseName? : Expr → Option (Name × Name × Expr)
  | .mdata ⟨[(nameAnnotation, .ofName name), (uniqAnnotation, .ofName uniq)]⟩ e => do
    some (name, uniq, e)
  | _ => none

def mkNameAnnotation (name uniq : Name) (e : Expr) : Expr :=
  .mdata ⟨[(nameAnnotation, .ofName name), (uniqAnnotation, .ofName uniq)]⟩ e

def getFreshName : TSyntax ``binderIdent → CoreM (Name × Syntax)
  | `(binderIdent| $name:ident) => pure (name.getId, name)
  | stx => return (← mkFreshUserName `x, stx)

def isTrue (p : Q(Bool)) : Bool := p.constName! == ``true

def matchBool (p : Q(Bool)) : ($p =Q true) ⊕' ($p =Q false) :=
  if isTrue p then .inl ⟨⟩ else .inr ⟨⟩

section hyps

inductive Hyps {prop : Q(Type u)} (bi : Q(BI $prop)) : (e : Q($prop)) → Type where
  | emp (_ : $e =Q emp) : Hyps bi e
  | sep (tm elhs erhs : Q($prop)) (_ : $e =Q iprop($elhs ∗ $erhs))
        (lhs : Hyps bi elhs) (rhs : Hyps bi erhs) : Hyps bi e
  | hyp (tm : Q($prop)) (name uniq : Name) (p : Q(Bool)) (ty : Q($prop))
        (_ : $e =Q iprop(□?$p $ty)) : Hyps bi e
deriving Repr

instance : Inhabited (Hyps bi s) := ⟨.emp ⟨⟩⟩

def Hyps.tm : @Hyps _ prop bi s → Q($prop)
  | .emp _ => s
  | .sep tm .. | .hyp tm .. => tm

def Hyps.mkEmp {prop : Q(Type u)} (bi : Q(BI $prop)) (e := q(BI.emp : $prop)) : Hyps bi e := .emp ⟨⟩

def Hyps.mkSep {prop : Q(Type u)} {bi : Q(BI $prop)} {elhs erhs}
    (lhs : Hyps bi elhs) (rhs : Hyps bi erhs) (e := q(BI.sep $elhs $erhs)) : Hyps bi e :=
  .sep q(BI.sep $(lhs.tm) $(rhs.tm) : $prop) elhs erhs ⟨⟩ lhs rhs

def mkIntuitionisticIf {prop : Q(Type u)} (_bi : Q(BI $prop))
    (p : Q(Bool)) (e : Q($prop)) : {A : Q($prop) // $A =Q iprop(□?$p $e)} :=
  match matchBool p with
  | .inl _ => ⟨q(iprop(□ $e)), ⟨⟩⟩
  | .inr _ => ⟨e, ⟨⟩⟩

def Hyps.mkHyp {prop : Q(Type u)} (bi : Q(BI $prop))
    (name uniq : Name) (p : Q(Bool)) (ty : Q($prop)) (e := q(iprop(□?$p $ty))) : Hyps bi e :=
  .hyp (mkIntuitionisticIf bi p (mkNameAnnotation name uniq ty)) name uniq p ty ⟨⟩

-- TODO: should this ensure that adding a hypothesis to emp creates a
-- hyp node instead of a sep node?
def Hyps.add {prop : Q(Type u)} (bi : Q(BI $prop))
    (name uniq : Name) (p : Q(Bool)) (ty : Q($prop)) {e} (h : Hyps bi e)
    : Hyps bi q(iprop($e ∗ □?$p $ty)) :=
  Hyps.mkSep h (.mkHyp bi name uniq p ty)

partial def parseHyps? {prop : Q(Type u)} (bi : Q(BI $prop)) (expr : Expr) :
    Option ((s : Q($prop)) × Hyps bi s) := do
  if let some #[_, _, P, Q] := appM? expr ``sep then
    let ⟨elhs, lhs⟩ ← parseHyps? bi P
    let ⟨erhs, rhs⟩ ← parseHyps? bi Q
    some ⟨q(BI.sep $elhs $erhs), .sep expr elhs erhs ⟨⟩ lhs rhs⟩
  else if expr.isAppOfArity ``emp 2 then
    some ⟨expr, .emp ⟨⟩⟩
  else if let some #[_, _, P] := appM? expr ``intuitionistically then
    let (name, uniq, (ty : Q($prop))) ← parseName? P
    some ⟨q(iprop(□ $ty)), .hyp expr name uniq q(true) ty ⟨⟩⟩
  else
    let (name, uniq, ty) ← parseName? expr
    some ⟨ty, .hyp expr name uniq q(false) ty ⟨⟩⟩

partial def Hyps.find? {u prop bi} (name : Name) :
    ∀ {s}, @Hyps u prop bi s → Option (Name × Q(Bool) × Q($prop))
  | _, .emp _ => none
  | _, .hyp _ name' uniq p ty _ => if name == name' then (uniq, p, ty) else none
  | _, .sep _ _ _ _ lhs rhs => rhs.find? name <|> lhs.find? name

variable (oldUniq new : Name) {prop : Q(Type u)} {bi : Q(BI $prop)} in
def Hyps.rename : ∀ {e}, Hyps bi e → Option (Hyps bi e)
  | _, .emp _ => none
  | _, .sep _ _ _ _ lhs rhs =>
    match rhs.rename with
    | some rhs' => some (.mkSep lhs rhs' _)
    | none => match lhs.rename with
      | some lhs' => some (.mkSep lhs' rhs _)
      | none => none
  | _, .hyp _ _ uniq p ty _ =>
    if oldUniq == uniq then some (Hyps.mkHyp bi new uniq p ty _) else none

def Hyps.select (ty : Expr) : ∀ {s}, @Hyps u prop bi s → MetaM (Name × Q(Bool) × Q($prop))
  | _, .emp _ => failure
  | _, .hyp _ _ uniq p ty' _ => do
    let .true ← isDefEq ty ty' | failure
    pure (uniq, p, ty')
  | _, .sep _ _ _ _ lhs rhs => try Hyps.select ty rhs catch _ => Hyps.select ty lhs


private theorem intuitionistically_sep_dup [BI PROP] {P : PROP} : □ P ⊣⊢ □ P ∗ □ P :=
  intuitionistically_sep_idem.symm

private theorem sep_emp_rev [BI PROP] {P : PROP} : P ⊣⊢ P ∗ emp := sep_emp.symm

private theorem emp_sep_rev [BI PROP] {P : PROP} : P ⊣⊢ emp ∗ P := emp_sep.symm

section split

private theorem split_es [BI PROP] {Q Q1 Q2 : PROP} (h : Q ⊣⊢ Q1 ∗ Q2) : emp ∗ Q ⊣⊢ Q1 ∗ Q2 :=
  emp_sep.trans h
private theorem split_ls [BI PROP] {P Q Q1 Q2 : PROP} (h : Q ⊣⊢ Q1 ∗ Q2) : P ∗ Q ⊣⊢ (P ∗ Q1) ∗ Q2 :=
  (sep_congr_r h).trans sep_assoc.symm
private theorem split_rs [BI PROP] {P Q Q1 Q2 : PROP} (h : Q ⊣⊢ Q1 ∗ Q2) : P ∗ Q ⊣⊢ Q1 ∗ (P ∗ Q2) :=
  (sep_congr_r h).trans sep_left_comm
private theorem split_se [BI PROP] {P P1 P2 : PROP} (h : P ⊣⊢ P1 ∗ P2) : P ∗ emp ⊣⊢ P1 ∗ P2 :=
  sep_emp.trans h
private theorem split_sl [BI PROP] {P Q P1 P2 : PROP} (h : P ⊣⊢ P1 ∗ P2) : P ∗ Q ⊣⊢ (P1 ∗ Q) ∗ P2 :=
  (sep_congr_l h).trans sep_right_comm
private theorem split_sr [BI PROP] {P Q P1 P2 : PROP} (h : P ⊣⊢ P1 ∗ P2) : P ∗ Q ⊣⊢ P1 ∗ (P2 ∗ Q) :=
  (sep_congr_l h).trans sep_assoc
private theorem split_ss [BI PROP] {P Q P1 P2 Q1 Q2 : PROP}
    (h1 : P ⊣⊢ P1 ∗ P2) (h2 : Q ⊣⊢ Q1 ∗ Q2) : P ∗ Q ⊣⊢ (P1 ∗ Q1) ∗ (P2 ∗ Q2) :=
  (sep_congr h1 h2).trans sep_sep_sep_comm

private inductive SplitResult {prop : Q(Type u)} (bi : Q(BI $prop)) (e : Q($prop)) where
  | emp (_ : $e =Q BI.emp)
  | left
  | right
  | split {elhs erhs : Q($prop)} (lhs : Hyps bi elhs) (rhs : Hyps bi erhs)
          (pf : Q($e ⊣⊢ $elhs ∗ $erhs))

variable {prop : Q(Type u)} (bi : Q(BI $prop)) (toRight : Name → Name → Bool) in
private def Hyps.splitCore : ∀ {e}, Hyps bi e → SplitResult bi e
  | _, .emp _ => .emp ⟨⟩
  | ehyp, h@(.hyp _ name uniq b ty _) =>
    match matchBool b with
    | .inl _ =>
      have : $ehyp =Q iprop(□ $ty) := ⟨⟩
      .split h h q(intuitionistically_sep_dup)
    | .inr _ => if toRight name uniq then .right else .left
  | _, .sep _ _ _ _ lhs rhs =>
    let resl := lhs.splitCore
    let resr := rhs.splitCore
    match resl, resr with
    | .emp _, .emp _ | .left, .emp _ | .emp _, .left | .left, .left => .left
    | .right, .emp _ | .emp _, .right | .right, .right => .right
    | .left, .right => .split lhs rhs q(.rfl)
    | .right, .left => .split rhs lhs q(sep_comm)
    | .emp _, .split r1 r2 rpf => .split r1 r2 q(split_es $rpf)
    | .left, .split r1 r2 rpf => .split (lhs.mkSep r1) r2 q(split_ls $rpf)
    | .right, .split r1 r2 rpf => .split r1 (lhs.mkSep r2) q(split_rs $rpf)
    | .split l1 l2 lpf, .emp _ => .split l1 l2 q(split_se $lpf)
    | .split l1 l2 lpf, .left => .split (l1.mkSep rhs) l2 q(split_sl $lpf)
    | .split l1 l2 lpf, .right => .split l1 (l2.mkSep rhs) q(split_sr $lpf)
    | .split l1 l2 lpf, .split r1 r2 rpf => .split (l1.mkSep r1) (l2.mkSep r2) q(split_ss $lpf $rpf)

def Hyps.split {prop : Q(Type u)} (bi : Q(BI $prop)) (toRight : Name → Name → Bool)
    {e} (hyps : Hyps bi e) :
    (elhs erhs : Q($prop)) × Hyps bi elhs × Hyps bi erhs × Q($e ⊣⊢ $elhs ∗ $erhs) :=
  match hyps.splitCore bi toRight with
  | .emp _ => ⟨_, _, hyps, hyps, q(sep_emp_rev)⟩
  | .left => ⟨_, _, hyps, .mkEmp bi, q(sep_emp_rev)⟩
  | .right => ⟨_, _, .mkEmp bi, hyps, q(emp_sep_rev)⟩
  | .split lhs rhs pf => ⟨_, _, lhs, rhs, pf⟩

end split

section remove

structure RemoveHyp {prop : Q(Type u)} (bi : Q(BI $prop)) (e : Q($prop)) where
  (e' : Q($prop)) (hyps' : Hyps bi e') (out out' : Q($prop)) (p : Q(Bool))
  (eq : $out =Q iprop(□?$p $out'))
  (pf : Q($e ⊣⊢ $e' ∗ $out))
  deriving Inhabited

private inductive RemoveHypCore {prop : Q(Type u)} (bi : Q(BI $prop)) (e : Q($prop)) (α : Type) where
  | none
  | one (a : α) (out' : Q($prop)) (p : Q(Bool)) (eq : $e =Q iprop(□?$p $out'))
  | main (a : α) (_ : RemoveHyp bi e)

private theorem remove_l [BI PROP] {P P' Q R : PROP} (h : P ⊣⊢ P' ∗ R) :
    P ∗ Q ⊣⊢ (P' ∗ Q) ∗ R :=
  (sep_congr_l h).trans sep_right_comm

private theorem remove_r [BI PROP] {P Q Q' R : PROP} (h : Q ⊣⊢ Q' ∗ R) :
    P ∗ Q ⊣⊢ (P ∗ Q') ∗ R :=
  (sep_congr_r h).trans sep_assoc.symm

variable [Monad m] {prop : Q(Type u)} (bi : Q(BI $prop)) (rp : Bool)
  (check : Name → Name → Q(Bool) → Q($prop) → m (Option α)) in
/-- If `rp` is true, the hyp will be removed even if it is in the intuitionistic context. -/
private def Hyps.removeCore : ∀ {e}, Hyps bi e → m (RemoveHypCore bi e α)
  | _, .emp _ => pure .none
  | e, h@(.hyp _ name uniq p ty _) => do
    if let some a ← check name uniq p ty then
      match matchBool p, rp with
      | .inl _, false =>
        have : $e =Q iprop(□ $ty) := ⟨⟩
        return .main a ⟨e, h, e, ty, q(true), ⟨⟩, q(intuitionistically_sep_dup)⟩
      | _, _ => return .one a ty p ⟨⟩
    else
      return .none
  | _, .sep _ elhs erhs _ lhs rhs => do
    match ← rhs.removeCore with
    | .one a out' p h =>
      return .main a ⟨elhs, lhs, erhs, out', p, h, q(.rfl)⟩
    | .main a ⟨_, rhs', out, out', p, h, pf⟩ =>
      let hyps' := .mkSep lhs rhs'
      return .main a ⟨_, hyps', out, out', p, h, q(remove_r $pf)⟩
    | .none => match ← lhs.removeCore with
      | .one a out' p h =>
        return .main a ⟨erhs, rhs, elhs, out', p, h, q(sep_comm)⟩
      | .main a ⟨_, lhs', out, out', p, h, pf⟩ =>
        let hyps' := .mkSep lhs' rhs
        return .main a ⟨_, hyps', out, out', p, h, q(remove_l $pf)⟩
      | .none => pure .none

def Hyps.removeG [Monad m] {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q(Prop)}
    (rp : Bool) (hyps : Hyps bi e)
    (check : Name → Name → Q(Bool) → Q($prop) → m (Option α)) :
    m (Option (α × RemoveHyp bi e)) := do
  match ← hyps.removeCore bi rp check with
  | .none => return none
  | .one a out' p h => return some ⟨a, _, .mkEmp bi, e, out', p, h, q(emp_sep_rev)⟩
  | .main a res => return some (a, res)

def Hyps.remove {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (rp : Bool) (hyps : Hyps bi e) (uniq : Name) : RemoveHyp bi e :=
  match Id.run (hyps.removeG rp fun _ uniq' _ _ => if uniq == uniq' then some () else none) with
  | some (_, r) => r
  | none => panic! "variable not found"

end remove

section replace

-- TODO: What to do with this? Is this necessary? Should this be a general abstraction?
def Replaces [BI PROP] (K A B : PROP) := (B -∗ K) ⊢ (A -∗ K)

theorem Replaces.apply [BI PROP] {P P' Q : PROP}
    (h : Replaces Q P P') (h_entails : P' ⊢ Q) : P ⊢ Q :=
  wand_entails <| (entails_wand h_entails).trans h

theorem replaces_r [BI PROP] {K P Q Q' : PROP} (h : Replaces K Q Q') :
    Replaces K iprop(P ∗ Q) iprop(P ∗ Q') :=
  wand_intro <| sep_assoc.2.trans <| wand_elim <|
  (wand_intro <| sep_assoc.1.trans wand_elim_l).trans h

theorem replaces_l [BI PROP] {K P P' Q : PROP} (h : Replaces K P P') :
    Replaces K iprop(P ∗ Q) iprop(P' ∗ Q) :=
  (wand_mono_l sep_comm.1).trans <| (replaces_r h).trans (wand_mono_l sep_comm.1)

theorem to_persistent_spatial [BI PROP] {P P' Q : PROP}
    [hP : IntoPersistently false P P'] [or : TCOr (Affine P) (Absorbing Q)] :
    Replaces Q P iprop(□ P') :=
  match or with
  | TCOr.l => wand_mono_l <| (affine_affinely P).2.trans (affinely_mono hP.1)
  | TCOr.r =>
    wand_intro <| (sep_mono_r <| hP.1.trans absorbingly_intuitionistically.2).trans <|
    absorbingly_sep_r.1.trans <| (absorbingly_mono wand_elim_l).trans absorbing

theorem to_persistent_intuitionistic [BI PROP] {P P' Q : PROP}
    [hP : IntoPersistently true P P'] : Replaces Q iprop(□ P) iprop(□ P') :=
  wand_mono_l <| affinely_mono hP.1

theorem from_affine [BI PROP] {p : Bool} {P P' Q : PROP} [hP : FromAffinely P' P p] :
    Replaces Q iprop(□?p P) P' :=
  wand_mono_l <| affinelyIf_of_intuitionisticallyIf.trans hP.1

inductive ReplaceHyp {prop : Q(Type u)} (bi : Q(BI $prop)) (Q : Q($prop)) where
  | none
  | unchanged (ehyps') (hyps' : Hyps bi ehyps')
  | main (e e' : Q($prop)) (hyps' : Hyps bi e') (pf : Q(Replaces $Q $e $e'))

variable [Monad m] [MonadLiftT MetaM m] {prop : Q(Type u)} (bi : Q(BI $prop)) (Q : Q($prop))
  (uniq : Name) (repl : Name → Q(Bool) → Q($prop) → m (ReplaceHyp bi Q)) in
def Hyps.replace : ∀ {e}, Hyps bi e → m (ReplaceHyp bi Q)
  | _, .emp _ => pure .none
  | _, .hyp _ name uniq' p ty _ => do
    if uniq == uniq' then
      let res ← repl name p ty
      if let .main e e' hyps' _ := res then
        let e' ← instantiateMVarsQ e'
        if e == e' then
          return .unchanged _ hyps'
      return res
    else return .none
  | _, .sep _ elhs erhs _ lhs rhs => do
    match ← rhs.replace with
    | .unchanged _ rhs' => return .unchanged _ (.mkSep lhs rhs')
    | .main erhs₀ _ rhs' pf =>
      let hyps' := .mkSep lhs rhs'
      return .main q(iprop($elhs ∗ $erhs₀)) _ hyps' q(replaces_r $pf)
    | .none => match ← lhs.replace with
      | .unchanged _ lhs' => return .unchanged _ (.mkSep lhs' rhs)
      | .main elhs₀ _ lhs' pf =>
        let hyps' := .mkSep lhs' rhs
        return .main q(iprop($elhs₀ ∗ $erhs)) _ hyps' q(replaces_l $pf)
      | .none => pure .none

end replace

end hyps

/-- This is the same as `Entails`, but it takes a `BI` instead.
This constant is used to detect iris proof goals. -/
abbrev Entails' [BI PROP] : PROP → PROP → Prop := Entails

structure IrisGoal where
  u : Level
  prop : Q(Type u)
  bi : Q(BI $prop)
  e : Q($prop)
  hyps : Hyps bi e
  goal : Q($prop)

def isIrisGoal (expr : Expr) : Bool := isAppOfArity expr ``Entails' 4

def parseIrisGoal? (expr : Expr) : Option IrisGoal := do
  -- remove top-level metadata when matching on the goal
  let expr := expr.consumeMData
  let some #[prop, bi, P, goal] := expr.appM? ``Entails' | none
  let u := expr.getAppFn.constLevels![0]!
  let ⟨e, hyps⟩ ← parseHyps? bi P
  some { u, prop, bi, e, hyps, goal }

def IrisGoal.toExpr : IrisGoal → Expr
  | { hyps, goal, .. } => q(Entails' $(hyps.tm) $goal)

def IrisGoal.strip : IrisGoal → Expr
  | { e, goal, .. } =>
    if e.consumeMData.isAppOfArity ``emp 2 then
      q(BIBase.EmpValid $goal)
    else
      q(Entails $e $goal)

/-- This is only used for display purposes, so that we can render context variables that appear
to have type `A : PROP` even though `PROP` is not a type. -/
def HypMarker {PROP : Type _} (_A : PROP) : Prop := True

/-- addLocalVarInfo associates the syntax `stx` (usually representing a hypothesis) with its type.
This allows one to hover over the syntax and see the type. isBinder marks the place where the
 hypothesis is introduced, e.g. for jump to definition. -/
def addLocalVarInfo (stx : Syntax) (lctx : LocalContext)
    (expr : Expr) (expectedType? : Option Expr) (isBinder := false) : MetaM Unit := do
  Elab.withInfoContext' (pure ())
    (fun _ =>
      return .inl <| .ofTermInfo
        { elaborator := .anonymous, lctx, expr, stx, expectedType?, isBinder })
    (return .ofPartialTermInfo { elaborator := .anonymous, lctx, stx, expectedType? })

def addHypInfo (stx : Syntax) (name uniq : Name) (prop : Q(Type u)) (ty : Q($prop))
    (isBinder := false) : MetaM Unit := do
  let lctx ← getLCtx
  let ty := q(HypMarker $ty)
  addLocalVarInfo stx (lctx.mkLocalDecl ⟨uniq⟩ name ty) (.fvar ⟨uniq⟩) ty isBinder

/-- Hyps.findWithInfo should be used on names obtained from the syntax of a tactic to highlight them correctly. -/
def Hyps.findWithInfo {u prop bi} (hyps : @Hyps u prop bi s) (name : Ident) : MetaM Name := do
  let some (uniq, _, ty) := hyps.find? name.getId | throwError "unknown hypothesis {name}"
  addHypInfo name name.getId uniq prop ty
  pure uniq

/-- Hyps.addWithInfo should be used by tactics that introduce a hypothesis based on the name given by the user. -/
def Hyps.addWithInfo {prop : Q(Type u)} (bi : Q(BI $prop))
    (name : TSyntax ``binderIdent) (p : Q(Bool)) (ty : Q($prop)) {e} (h : Hyps bi e)
    : MetaM (Name × Hyps bi q(iprop($e ∗ □?$p $ty))) := do
  let uniq' ← mkFreshId
  let (nameTo, nameRef) ← getFreshName name
  addHypInfo nameRef nameTo uniq' prop ty (isBinder := true)
  let hyps := Hyps.add bi nameTo uniq' p ty h
  return ⟨uniq', hyps⟩
