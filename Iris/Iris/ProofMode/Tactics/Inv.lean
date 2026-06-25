/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Alvin Tang
-/
module

public meta import Iris.ProofMode.Tactics.Assumption
public meta import Iris.ProofMode.Tactics.Cases
public meta import Iris.ProofMode.Tactics.Intro
public meta import Iris.ProofMode.Patterns.CasesPattern
public meta import Iris.ProofMode.Patterns.IntroPattern
public meta import Iris.ProofMode.Patterns.SelPattern
public meta import Iris.ProofMode.ClassesMake

namespace Iris.ProofMode

public meta section
open Lean Elab Tactic Meta Qq BI Std

def optionMap {PROP : Type u} {X : Type} (mP : Option (X → PROP)) (x : X) : Option PROP :=
  mP.map (· x)

theorem tac_inv_elim [BI PROP]
    {e e' e'' goal : PROP} {ϕ : Prop} {X : Type} {p close : Bool}
    {Pinv Pin : PROP} {mPclose : Option <| X → PROP} {Pout Q' : X → PROP}
    (inst : ElimInv ϕ X Pinv Pin Pout close mPclose goal Q')
    (hϕ : ϕ)
    (hAcc : ∀ x, e'' ∗ Pout x ∗ ((mPclose.map (· x)).getD emp) ⊢ Q' x)
    (pf : e ⊣⊢ e' ∗ □?p Pinv)
    (pfPin : e' ∗ (Pin -∗ Pin) ⊢ e'' ∗ Pin) :
    e ⊢ goal := sorry

  -- have h0 := inst.elim_inv hϕ
  -- have h1 : e ⊢ Pinv ∗ Pin ∗ ∀ a, Pout a -∗ Option.map (fun x => x a) mPclose -∗? Q' a := calc
  --   e ⊢ e' ∗ □?p Pinv            := pf.mp
  --   _ ⊢ □?p Pinv ∗ e'            := sep_comm.mp
  --   _ ⊢ Pinv ∗ e'                := sep_mono_left intuitionisticallyIf_elim
  --   _ ⊢ Pinv ∗ e' ∗ emp          := sep_mono_right sep_emp.mpr
  --   _ ⊢ Pinv ∗ e' ∗ (Pin -∗ Pin) := sep_mono_right <| sep_mono_right wand_rfl
  --   _ ⊢ Pinv ∗ e'' ∗ Pin         := sep_mono_right pfPin
  --   _ ⊢ Pinv ∗ Pin ∗ e''         := sep_mono_right sep_comm.mp
  --   _ ⊢ _                        := sep_mono_right <| sep_mono_right <| forall_intro (wand_intro <| hAcc ·)
  -- apply h1.trans
  -- cases mPclose with
  -- | none =>
  --   apply (sep_mono_right <| sep_mono_right <| forall_mono <| fun _ => wand_mono_left sep_emp.mp).trans h0
  -- | some _ =>
  --   apply (sep_mono_right <| sep_mono_right <| forall_intro (forall_elim · |>.trans wand_curry.mp)).trans h0

private def iInvCore {u} {prop : Q(Type u)} {bi} {e}
    (hyps : Hyps bi e) (goal : Q($prop)) (ivar : IVarId) (specPat : Option SpecPat)
    (introPat : iCasesPat) (closePat : Option iCasesPat) :
    ProofModeM Q($e ⊢ $goal) := do
  -- Find the hypothesis from the context
  let ⟨_, hyps', _, Pinv, _, _ , pfEq⟩ := hyps.remove false ivar

  let ϕ ← mkFreshExprMVarQ q(Prop)
  let Pin : Q($prop) ← mkFreshExprMVarQ q($prop)
  let X ← mkFreshExprMVarQ q(Type)
  let Pout ← mkFreshExprMVarQ q($X → $prop)
  -- Decide whether to use `elimInv_acc_with_close` or `elimInv_acc_without_close`
  let close := if closePat.isSome then q(true) else q(false)
  let mPclose ← mkFreshExprMVarQ q(Option ($X → $prop))
  let Q' ← mkFreshExprMVarQ q($X → $prop)
  let some inst ← ProofModeM.trySynthInstanceQ q(ElimInv $ϕ $X $Pinv $Pin $Pout $close $mPclose $goal $Q')
  | throwError "iinv: invalid invariant {Pinv} (ElimInv type class synthesis failed)"

  let ⟨e'', hyps'', p'', out'', pfPin⟩ ← iSpecializeCore hyps' q(false) q(iprop($Pin -∗ $Pin)) [specPat.getD <| .autoframe .spatial]
  have : $out'' =Q $Pin := ⟨⟩
  have : $p'' =Q false := ⟨⟩

  -- Solve side conditions automatically if possible, otherwise add them into the proof state
  let hϕ ← iSolveSidecondition q($ϕ) false

  match mPclose with
  | ~q(some $f) =>

    let hAcc : Q(∀ x : $X, $e'' ∗ $Pout x ∗ $f x ⊢ $Q' x) ←
      withLocalDeclDQ (u := 0) (← mkFreshUserName `x) X fun x => do
        match closePat with
        | some closePat =>
          mkLambdaFVars #[x] <| ← iCasesCore _ hyps'' q(iprop($Q' $x)) (.conjunction [introPat, closePat]) q(false) q(iprop($Pout $x ∗ $f $x))
        -- Throw an error if `hclose` is not given, but `mPclose` is not `none`
        | none => throwError "iinv: error"

    return q(tac_inv_elim $inst $hϕ $hAcc $pfEq $pfPin)

  | ~q(none) =>
    let hAcc : Q(∀ x : $X, $e'' ∗ $Pout x ⊢ $Q' x) ←
      withLocalDeclDQ (u := 0) (← mkFreshUserName `x) X fun x => do
        mkLambdaFVars #[x] <| ← iCasesCore _ hyps'' q(iprop($Q' $x)) introPat q(false) q($Pout $x)

    let hAcc : Q(∀ x : $X, $e'' ∗ $Pout x ∗ emp ⊢ $Q' x) :=
      q(fun x => sep_assoc.mpr.trans <| sep_emp.mp.trans ($hAcc x))

    return q(tac_inv_elim $inst $hϕ $hAcc $pfEq $pfPin)

/-- Find an invariant hypothesis with a given `Namespace` value. -/
private def findInvariantWithNamespace {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (N : Q(Namespace)) (hyps : Hyps bi e) : ProofModeM <| Option IVarId := do
  match hyps with
  | .emp _ => return none
  | .hyp _ _ ivar _ ty _ =>
    let inst ← ProofModeM.trySynthInstanceQ q(IntoInv $ty $N)
    return if inst.isSome then some ivar else none
  | .sep _ _ _ _ lhs rhs =>
    let rhsInvariant ← findInvariantWithNamespace N rhs
    match rhsInvariant with
    | some ivar => return some ivar
    | none => return ← findInvariantWithNamespace N lhs

/-- `iinv` opens an invariant in the proof state. -/
syntax (name := iinv) "iinv " colGt term (" $$ " colGt ppSpace specPat)?
    " with " colGt icasesPat (colGt icasesPat)? : tactic

elab_rules : tactic
  | `(tactic| iinv $t:term $[$$ $spat:specPat]? with $ipat:icasesPat $[$cpat:icasesPat]?) => do
    -- Parse the introduction and selection patterns
    let specPat ← liftMacroM <| spat.mapM SpecPat.parse
    let introPat ← liftMacroM <| iCasesPat.parse ipat
    let closePat ← liftMacroM <| cpat.mapM iCasesPat.parse

    ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
      -- Find the invariant hypothesis
      let ivar ← do match ← try? <| hyps.findWithInfo ⟨t⟩ with
      -- Hypothesis supplied by the user: return the `IVarId` value of the invariant directly
      | some ivar => pure ivar
      -- Namespace supplied by the user: use `IntoInv` to find the corresponding hypothesis
      | none =>
        let N ← elabTermEnsuringTypeQ t q(Namespace)
        match ← findInvariantWithNamespace N hyps with
        | some ivar => pure ivar
        | none => throwError m!"iinv: invariant {N} not found"

      let pf ← iInvCore hyps goal ivar specPat introPat closePat
      mvar.assign pf
