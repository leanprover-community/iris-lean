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

@[rocq_alias tac_inv_elim]
theorem tac_inv_elim [BI PROP]
    {e e' goal : PROP} {ϕ : Prop} {X : Type} {p close : Bool}
    {Pinv Pin : PROP} {mPclose : Option <| X → PROP} {Pout Q' : X → PROP}
    (inst : ElimInv ϕ X Pinv Pin Pout close mPclose goal Q')
    (hϕ : ϕ)
    (hAcc : ∀ x, e'' ⊢ Pout x -∗ mPclose.map (· x) -∗? Q' x)
    (pf : e ⊣⊢ e' ∗ □?p Pinv)
    (pfPin : e' ∗ (Pin -∗ Pin) ⊢ e'' ∗ out'') :
    e ⊢ goal := by
  have h := inst.elim_inv hϕ
  cases mPclose with simp_all
  | none => calc
    e ⊢ e' ∗ □?p Pinv                          := pf.mp
    _ ⊢ □?p Pinv ∗ e'                          := sep_comm.mp
    _ ⊢ Pinv ∗ e'                              := sep_mono_left intuitionisticallyIf_elim
    _ ⊢ Pinv ∗ ∀ x, Pout x -∗ Q' x             := sorry
    _ ⊢ Pinv ∗ emp ∗ ∀ x, Pout x -∗ Q' x       := sep_mono_right emp_sep.mpr
    _ ⊢ Pinv ∗ Pin ∗ ∀ x, Pout x -∗ Q' x       := sep_mono_right <| sep_mono_left sorry
    _ ⊢ Pinv ∗ Pin ∗ ∀ x, Pout x ∗ emp -∗ Q' x := sep_mono_right <| sep_mono_right <| forall_mono (fun _ => wand_mono_left sep_emp.mp)
    _ ⊢ goal                                   := h
  | some mPclose => calc
    e ⊢ e' ∗ □?p Pinv                                := pf.mp
    _ ⊢ □?p Pinv ∗ e'                                := sep_comm.mp
    _ ⊢ Pinv ∗ e'                                    := sep_mono_left intuitionisticallyIf_elim
    _ ⊢ Pinv ∗ ∀ x, Pout x -∗ mPclose x -∗ Q' x      := sorry
    _ ⊢ Pinv ∗ ∀ x, Pout x ∗ mPclose x -∗ Q' x       := sep_mono_right <| forall_mono <| fun _ => wand_curry.mp
    _ ⊢ Pinv ∗ emp ∗ ∀ x, Pout x ∗ mPclose x -∗ Q' x := sep_mono_right emp_sep.mpr
    _ ⊢ Pinv ∗ Pin ∗ ∀ x, Pout x ∗ mPclose x -∗ Q' x := sep_mono_right <| sep_mono_left sorry
    _ ⊢ goal                                         := h

private def iInvCore {u} {prop : Q(Type u)} {bi e} (hyps : Hyps bi e) (goal : Q($prop))
    (ivar : IVarId)
    (specPats : List SpecPat)
    (introPat : Syntax × IntroPat)
    (closePat : Option <| Syntax × IntroPat) :
    ProofModeM Q($e ⊢ $goal) := do
  -- Find the hypothesis from the context
  let ⟨_, hyps', _, Pinv, _, _ , pfEq⟩ := hyps.remove false ivar

  let ϕ ← mkFreshExprMVarQ q(Prop)
  let Pin ← mkFreshExprMVarQ q($prop)
  let X ← mkFreshExprMVarQ q(Type)
  let Pout ← mkFreshExprMVarQ q($X → $prop)
  let close := if closePat.isSome then q(true) else q(false)
  let mPclose ← mkFreshExprMVarQ q(Option ($X → $prop))
  let Q' ← mkFreshExprMVarQ q($X → $prop)
  let some inst ← ProofModeM.trySynthInstanceQ q(ElimInv $ϕ $X $Pinv $Pin $Pout $close $mPclose $goal $Q')
  | throwError "iinv: invalid invariant {Pinv}"

  -- Solve side conditions automatically if possible, otherwise add them into the proof state
  let hϕ ← iSolveSidecondition q($ϕ) false

  let ⟨e'', _, _, _, pfPin⟩ ← iSpecializeCore hyps' q(false) q(iprop($Pin -∗ $Pin)) specPats

  -- Create the wand proposition and apply the introduction pattern to destruct the premise
  let hAcc : Q(∀ x : $X, $e'' ⊢ $Pout x -∗ optionMap $mPclose x -∗? $Q' x) ←
    withLocalDeclDQ (u := 0) (← mkFreshUserName `x) X fun x => do
      let poutX : Q($prop) := Expr.headBeta q($Pout $x)
      let qX : Q($prop) := Expr.headBeta q($Q' $x)
      let body ← match mPclose with
      | ~q(none) =>
        iIntroCore hyps' q(iprop($poutX -∗ $qX)) [introPat]
      | ~q(some $f) =>
        let f : Q($X → $prop) := f
        match closePat with
        | some closePat =>
          let closeX : Q($prop) := Expr.headBeta q($f $x)
          iIntroCore hyps' q(iprop($poutX -∗ $closeX -∗ $qX)) [introPat, closePat]
        -- Throw an error if `hclose` is not given, but `mPclose` is not `none`
        | none => throwError "iinv: error"
      mkLambdaFVars #[x] body

  return q(tac_inv_elim $inst $hϕ $hAcc $pfEq $pfPin)

/-- `iinv` opens an invariant in the proof state. -/
syntax (name := iinv) "iinv " colGt ident (" with " (colGt ppSpace specPat)+)?
    " as " colGt introPat (introPat)? : tactic

elab_rules : tactic
  | `(tactic| iinv $h:ident $[with $spats:specPat*]? as $ipat:introPat $[$cpat:introPat]?) => do
    -- Parse the introduction and selection patterns
    let specPats ← spats.mapM (liftMacroM <| ·.mapM SpecPat.parse) <&> (·.getD #[] |>.toList)
    let introPat ← liftMacroM <| IntroPat.parse ipat
    let closePat ← liftMacroM <| cpat.mapM IntroPat.parse

    ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
      -- Find the hypothesis in which the invariant is opened
      let ivar ← hyps.findWithInfo h

      let pf ← iInvCore hyps goal ivar specPats introPat closePat
      mvar.assign pf
