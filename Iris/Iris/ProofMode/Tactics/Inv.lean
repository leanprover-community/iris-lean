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
    {e e' e'' goal : PROP} {ϕ : Prop} {X : Type} {p close : Bool}
    {Pinv Pin : PROP} {mPclose : Option <| X → PROP} {Pout Q' : X → PROP}
    (inst : ElimInv ϕ X Pinv Pin Pout close mPclose goal Q')
    (hϕ : ϕ)
    (hAcc : ∀ x, e'' ⊢ Pout x -∗ mPclose.map (· x) -∗? Q' x)
    (pf : e ⊣⊢ e' ∗ □?p Pinv)
    (pfPin : e' ∗ (Pin -∗ Pin) ⊢ e'' ∗ Pin) :
    e ⊢ goal := by
  have h0 := inst.elim_inv hϕ
  have h1 : e ⊢ Pinv ∗ Pin ∗ e'' := calc
    e ⊢ e' ∗ □?p Pinv            := pf.mp
    _ ⊢ □?p Pinv ∗ e'            := sep_comm.mp
    _ ⊢ Pinv ∗ e'                := sep_mono_left intuitionisticallyIf_elim
    _ ⊢ Pinv ∗ e' ∗ emp          := sep_mono_right sep_emp.mpr
    _ ⊢ Pinv ∗ e' ∗ (Pin -∗ Pin) := sep_mono_right <| sep_mono_right wand_rfl
    _ ⊢ Pinv ∗ e'' ∗ Pin         := sep_mono_right pfPin
    _ ⊢ Pinv ∗ Pin ∗ e''         := sep_mono_right sep_comm.mp
  cases mPclose with simp_all
  | none => calc
    e ⊢ Pinv ∗ Pin ∗ e''                       := h1
    _ ⊢ Pinv ∗ Pin ∗ ∀ x, Pout x -∗ Q' x       :=
        sep_mono_right <| sep_mono_right <| forall_intro hAcc
    _ ⊢ Pinv ∗ Pin ∗ ∀ x, Pout x ∗ emp -∗ Q' x :=
        sep_mono_right <| sep_mono_right <| forall_mono <| fun _ => wand_mono_left sep_emp.mp
    _ ⊢ goal                                   := h0
  | some mPclose => calc
    e ⊢ Pinv ∗ Pin ∗ e''                              := h1
    _ ⊢ Pinv ∗ Pin ∗ ∀ x, Pout x -∗ mPclose x -∗ Q' x :=
        sep_mono_right <| sep_mono_right <| forall_intro hAcc
    _ ⊢ Pinv ∗ Pin ∗ ∀ x, Pout x ∗ mPclose x -∗ Q' x  :=
        sep_mono_right <| sep_mono_right <| forall_intro (forall_elim · |>.trans wand_curry.mp)
    _ ⊢ goal                                          := h0

private def iInvCore {u} {prop : Q(Type u)} {bi e} (hyps : Hyps bi e) (goal : Q($prop))
    (ivar : IVarId)
    (specPat : Option SpecPat)
    (introPat : Syntax × IntroPat)
    (closePat : Option <| Syntax × IntroPat) :
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

  -- Solve side conditions automatically if possible, otherwise add them into the proof state
  let hϕ ← iSolveSidecondition q($ϕ) false

  -- Using this instead of `.autoframe .spatial` in order to handle `Pin = True`
  let ⟨e'', hyps'', p'', out'', pfPin⟩ ←
    match specPat with
    | some pat => iSpecializeCore hyps' q(false) q(iprop($Pin -∗ $Pin)) [pat]
    | none =>
      -- Special case: `Pin = True`, not solved by `.autoframe .spatial`
      -- Ideally `.autoframe .spatial` applies `iItrivial`
      /-
        Alternatively use:
        `{ kind := .spatial, negate := true, trivial := true, frame := [], hyps := [] }`,
        but it does not always choose the correct hypotheses and thus produce unprovable goals
      -/
      match Pin with
      | ~q(iprop(True)) =>
        pure ⟨_, hyps', q(false), Pin, q(sep_mono_right true_intro)⟩
      | _=>
        iSpecializeCore hyps' q(false) q(iprop($Pin -∗ $Pin)) [.autoframe .spatial]

  have : $out'' =Q $Pin := ⟨⟩
  have : $p'' =Q false := ⟨⟩

  -- Create the wand proposition and apply the introduction pattern to destruct the premise
  let hAcc : Q(∀ x : $X, $e'' ⊢ $Pout x -∗ optionMap $mPclose x -∗? $Q' x) ←
    withLocalDeclDQ (u := 0) (← mkFreshUserName `x) X fun x => do
      let body ← match mPclose with
      | ~q(none) =>
        iIntroCore hyps'' q(iprop($Pout $x -∗ $Q' $x)) [introPat]
      | ~q(some $f) =>
        match closePat with
        | some closePat =>
          let f : Q($X → $prop) := f
          iIntroCore hyps'' q(iprop($Pout $x -∗ $f $x -∗ $Q' $x)) [introPat, closePat]
        -- Throw an error if `hclose` is not given, but `mPclose` is not `none`
        | none => throwError "iinv: error"
      mkLambdaFVars #[x] body

  return q(tac_inv_elim $inst $hϕ $hAcc $pfEq $pfPin)

/-- `iinv` opens an invariant in the proof state. -/
syntax (name := iinv) "iinv " colGt ident " as " colGt introPat (introPat)?
    (" with " colGt ppSpace specPat)? : tactic

elab_rules : tactic
  | `(tactic| iinv $h:ident as $ipat:introPat $[$cpat:introPat]? $[with $spat:specPat]?) => do
    -- Parse the introduction and selection patterns
    let specPat ← liftMacroM <| spat.mapM SpecPat.parse
    let introPat ← liftMacroM <| IntroPat.parse ipat
    let closePat ← liftMacroM <| cpat.mapM IntroPat.parse

    ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
      -- Find the hypothesis in which the invariant is opened
      let ivar ← hyps.findWithInfo h

      let pf ← iInvCore hyps goal ivar specPat introPat closePat
      mvar.assign pf
