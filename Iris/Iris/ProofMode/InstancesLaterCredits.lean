/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI.LaterCredits
public import Iris.ProofMode.Classes
public import Iris.ProofMode.Instances
public import Iris.ProofMode.InstancesUpdates
public import Iris.ProofMode.NatCancel
public import Iris.ProofMode.Tactics

@[expose] public section

namespace Iris.ProofMode

open Iris.BI

section LaterCredits

variable {PROP : Type _} [BI PROP] [BILaterCredits PROP]

/- Make sure that the rule for `+` is used before `.succ`, otherwise `m + (n + 1)` would be
split off by the `.succ` rule via unfolding `Nat.add`. See Iris issue #470. -/

@[rocq_alias from_sep_lc_add]
instance (priority := default) {n m} : FromSep (PROP := PROP) (£ (n + m)) (£ n) (£ m) where
  from_sep := lc_split.mpr

@[rocq_alias from_sep_lc_S]
instance (priority := default - 10) {n} : FromSep (PROP := PROP) (£ (.succ n)) (£ 1) (£ n) where
  from_sep := lc_succ.mpr

@[rocq_alias into_sep_lc_add]
instance (priority := default) {n m} : IntoSep (PROP := PROP) (£ (n + m)) (£ n) (£ m) where
  into_sep := lc_split.mp

@[rocq_alias into_sep_lc_S]
instance (priority := default - 10) {n} : IntoSep (PROP := PROP) (£ (.succ n)) (£ 1) (£ n) where
  into_sep := lc_succ.mp

@[rocq_alias combine_sep_lc_add]
instance (priority := default) {n m} : CombineSepAs (PROP := PROP) (£ n) (£ m) (£ (n + m)) where
  combine_sep_as := lc_split.mpr

#rocq_ignore combine_sep_lc_S_l
  "Not necessary in Lean as it is more common to use +1 instead of .succ"

end LaterCredits

end Iris.ProofMode

/-! ## The tactic `inext n credit: H` -/

public section

open Lean Tactic Meta Qq Iris BI ProofMode

universe u

@[rocq_alias tac_lc_add_laterN_split]
theorem tac_lc_add_laterN_split {PROP : Type u} [BI PROP] [BILaterCredits PROP]
    [BIFUpdate PROP] [BIFUpdLaterCredits PROP]
    {φ : Prop} {n m newM : Nat} {stuck : Bool} {E : CoPset}
    {e P R Q goal : PROP}
    (heq : e ⊣⊢ P ∗ £ m)
    (inst : ElimModal φ false .in false iprop(|={E}=> goal) goal goal goal) (hφ : φ)
    (hc : NatCancel m n newM 0 stuck)
    (hR : P ∗ £ newM ⊣⊢ R) (h2 : R ⊢ ▷^[n] Q) (h3 : Q ⊢ goal) :
    e ⊢ goal := by
  have hm : m = n + newM := by have := hc.nat_cancel; omega
  subst hm
  refine heq.mp.trans ?_
  iintro ⟨HP, Hcred⟩
  iapply inst.elim_modal hφ
  isplitl
  · icases lc_split.mp $$ Hcred with ⟨Hn, Hm⟩
    icombine HP Hm as H
    ihave H := (hR.mp.trans h2) $$ H
    simp only [BIBase.intuitionisticallyIf, Bool.false_eq_true, ↓reduceIte]
    iapply lc_fupd_add_laterN n $$ Hn
    iapply laterN_mono n (h3.trans fupd_intro) $$ H
  · simp only [BIBase.intuitionisticallyIf, Bool.false_eq_true, ↓reduceIte]
    iintro H //

theorem tac_lc_add_laterN_full {PROP : Type u} [BI PROP] [BILaterCredits PROP]
    [BIFUpdate PROP] [BIFUpdLaterCredits PROP]
    {φ : Prop} {n m : Nat} {stuck : Bool} {E : CoPset}
    {e P Q goal : PROP}
    (heq : e ⊣⊢ P ∗ £ m)
    (inst : ElimModal φ false .in false iprop(|={E}=> goal) goal goal goal) (hφ : φ)
    (hc : NatCancel m n 0 0 stuck)
    (h2 : P ⊢ ▷^[n] Q) (h3 : Q ⊢ goal) :
    e ⊢ goal :=
  tac_lc_add_laterN_split heq inst hφ hc .rfl (sep_elim_left.trans h2) h3

public meta section

/-- The `ElimModal` instance shape needed to eliminate a fancy update at the goal. -/
abbrev ElimFUpdGoal (PROP : Type u) [BI PROP] [BIFUpdate PROP]
    (φ : Prop) (E : CoPset) (goal Q : PROP) : Prop :=
  ElimModal φ false .in false iprop(|={E}=> goal) goal goal Q

elab "inext " t:(colGt term:max)? " credit: " h:ident : tactic => do
  let n : Q(Nat) ← match t with
  | none => pure <| mkNatLit 1
  | some t => do
    let n ← Lean.Elab.Term.elabTermEnsuringType t q(Nat)
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars n

  ProofModeM.runTactic `inext fun mvar { u, prop, bi, e, hyps, goal, .. } => do
    -- Search for the later credit hypothesis from the context
    let ivar ← hyps.findWithInfo h
    let some ⟨name, _, p, ty⟩ := hyps.getDecl? ivar
      | throwError m!"inext: unknown hypothesis {h}"
    if isTrue p then throwError "inext: {h} is not in the spatial context"
    -- We use direct `Expr` manipulation here and below since `Qq` makes compiling this function very slow
    --- see https://github.com/leanprover-community/iris-lean/pull/633
    let some #[_, _, c] := Expr.appM? ty ``LaterCredits.lc
      | throwError m!"inext: {h} is not a spatial later credit hypothesis"
    let ⟨e', hyps', _, _, _, _, pfEq⟩ := hyps.remove false ivar
    let .some instLC ← trySynthInstance (mkAppN (.const ``BILaterCredits [u]) #[prop, bi])
      | throwError "inext: Missing BILaterCredits instance"
    let .some instFUpd ← trySynthInstance (mkAppN (.const ``BIFUpdate [u]) #[prop, bi])
      | throwError "inext: Missing BIFUpdate instance"
    let .some instFLC ← trySynthInstance
        (mkAppN (.const ``BIFUpdLaterCredits [u]) #[prop, bi, instLC, instFUpd])
      | throwError "inext: Missing BIFUpdLaterCredits instance"

    let φ ← mkFreshExprMVarQ q(Prop)
    let E ← mkFreshExprMVarQ q(CoPset)
    let Q' ← mkFreshExprMVarQ q($prop)
    let elimTy := mkAppN (.const ``ElimFUpdGoal [u]) #[prop, bi, instFUpd, φ, E, goal, Q']
    let .some ⟨inst, _⟩ ← ProofMode.trySynthInstance elimTy
    | throwError "inext: ElimModal type class synthesis failed with {goal}"
    unless ← isDefEq Q' goal do
      throwError "inext: eliminating the fancy update does not preserve the goal {goal}"

    let hφ ← iSolveSidecondition q($φ)

    let newC ← mkFreshExprMVarQ q(Nat)
    let newN ← mkFreshExprMVarQ q(Nat)
    let stuck ← mkFreshExprMVarQ q(Bool)
    have c : Q(Nat) := c
    let some hcancel ← ProofModeM.trySynthInstanceQ q(NatCancel $c $n $newC $newN $stuck)
      | throwError "inext: unable to cancel {n} later credits from {c}"
    unless ← isDefEq newN q(0) do
      throwError "inext: insufficient credits"

    have modality : Q(@Modality $prop $prop $bi $bi) :=
      mkAppN (.const ``modality_laterN [u]) #[prop, n, bi]

    let newC : Q(Nat) ← instantiateMVars newC
    match newC.nat? with
    -- Later credits used up, discard the later credits hypothesis
    | some 0 =>
      let ⟨eQ, newHyps', pfModAction⟩ ← iModAction hyps' modality
      let pf ← addBIGoal newHyps' goal
      mvar.assign <| mkAppN (.const ``tac_lc_add_laterN_full [u])
        #[prop, bi, instLC, instFUpd, instFLC, φ, n, c, stuck, E,
          e, e', eQ, goal, pfEq, inst, hφ, hcancel, pfModAction, pf]
    -- Update the later credits hypothesis and introduce it into the context
    | _ =>
      let newTy := mkApp ty.appFn! newC
      let ⟨eAdd, newHyps, pfNewHyps⟩ := Hyps.add _ name ivar q(false) newTy hyps'
      let ⟨eQ, newHyps', pfModAction⟩ ← iModAction newHyps modality
      let pf ← addBIGoal newHyps' goal
      mvar.assign <| mkAppN (.const ``tac_lc_add_laterN_split [u])
        #[prop, bi, instLC, instFUpd, instFLC, φ, n, c, newC, stuck, E,
          e, e', eAdd, eQ, goal, pfEq, inst, hφ, hcancel, pfNewHyps, pfModAction, pf]

end

end
