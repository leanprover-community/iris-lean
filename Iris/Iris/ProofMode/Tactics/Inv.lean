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

public section
open BI

@[rocq_alias tac_inv_elim]
theorem tac_inv_elim [BI PROP]
    {e e' e'' goal : PROP} {ϕ : Prop} {X : Type} {p close : Bool}
    {Pinv Pin : PROP} {mPclose : Option <| X → PROP} {Pout Q' : X → PROP}
    (inst : ElimInv ϕ X Pinv Pin Pout close mPclose goal Q')
    (hϕ : ϕ)
    (pf : match mPclose with
      | none => ∀ x, e'' ∗ Pout x ⊢ Q' x
      | some Pclose => ∀ x, e'' ∗ Pout x ∗ Pclose x ⊢ Q' x)
    (pfEq : e ⊣⊢ e' ∗ □?p Pinv)
    (pfPin : e' ∗ (Pin -∗ Pin) ⊢ e'' ∗ Pin) :
    e ⊢ goal := by
  have h0 := inst.elim_inv
  have h1 : e ⊢ Pinv ∗ Pin ∗ e'' := calc
    e ⊢ e' ∗ □?p Pinv            := pfEq.mp
    _ ⊢ □?p Pinv ∗ e'            := sep_comm.mp
    _ ⊢ Pinv ∗ e'                := sep_mono_left intuitionisticallyIf_elim
    _ ⊢ Pinv ∗ e' ∗ emp          := sep_mono_right sep_emp.mpr
    _ ⊢ Pinv ∗ e' ∗ (Pin -∗ Pin) := sep_mono_right <| sep_mono_right wand_rfl
    _ ⊢ Pinv ∗ e'' ∗ Pin         := sep_mono_right pfPin
    _ ⊢ Pinv ∗ Pin ∗ e''         := sep_mono_right sep_comm.mp
  cases mPclose with simp_all
  | none => calc
    e ⊢ Pinv ∗ Pin ∗ e'' := h1
    _ ⊢ _ := sep_mono_right <| sep_mono_right <| forall_intro (wand_intro <| pf ·)
    _ ⊢ goal := h0
  | some Pclose => calc
    e ⊢ Pinv ∗ Pin ∗ e'' := h1
    _ ⊢ _ := sep_mono_right <| sep_mono_right <| forall_intro (wand_intro <| pf ·)
    _ ⊢ goal := h0

public meta section
open Lean Elab Tactic Meta Qq BI Std

/--
  An annotation of `wandM` with `@[reducible]` is useful when `whnf` is called,
  but `whnf` is not strong enough to simplify occurrences of `wandM` in the
  proof goal. This funnction is similar to `pm_reduce` in the Rocq version,
  which forces the reduction of `wandM` (`-∗?`), occurrences of `Option.getD`
  and pattern matching (`match … with …`).
-/
def pmReduce (e : Expr) : ProofModeM Expr := do
  #[``BIBase.wandM, ``Option.getD].foldlM (·.addDeclToUnfold ·) {} >>=
  (Simp.mkContext {} #[·] (← getSimpCongrTheorems) >>= (Lean.Meta.dsimp e · <&> Prod.fst))

private def iInvCore {u} {prop : Q(Type u)} {bi} {e}
    (hyps : Hyps bi e) (goal : Q($prop)) (ivar : IVarId) (specPat : Option SpecPat)
    (casesPat : iCasesPat) (closePat : Option iCasesPat) :
    ProofModeM Q($e ⊢ $goal) := do
  -- Find the hypothesis from the context
  let ⟨_, hyps', _, Pinv, _, _, pfEq⟩ := hyps.remove false ivar

  let ϕ ← mkFreshExprMVarQ q(Prop)
  let Pin : Q($prop) ← mkFreshExprMVarQ q($prop)
  let X : Q(Type) ← mkFreshExprMVarQ q(Type)
  let Pout ← mkFreshExprMVarQ q($X → $prop)
  -- Decide whether to use `elimInv_acc_with_close` or `elimInv_acc_without_close`
  let close := if closePat.isSome then q(true) else q(false)
  let mPclose ← mkFreshExprMVarQ q(Option ($X → $prop))
  let Q' ← mkFreshExprMVarQ q($X → $prop)
  let some inst ← ProofModeM.trySynthInstanceQ q(ElimInv $ϕ $X $Pinv $Pin $Pout $close $mPclose $goal $Q')
  | throwError "iinv: invalid invariant {Pinv} (ElimInv type class synthesis failed)"

  let ⟨e'', hyps'', p'', out'', pfPin⟩ ←
    iSpecializeCore hyps' q(false) q(iprop($Pin -∗ $Pin)) [specPat.getD <| .autoframe .spatial]
  have : $out'' =Q $Pin := ⟨⟩
  have : $p'' =Q false := ⟨⟩

  -- Solve side conditions automatically if possible, otherwise add them into the proof state
  let hϕ ← iSolveSidecondition q($ϕ) false

  -- Simplify occurrences of `wandM`, `Option.getD`, pattern matching, etc.
  let Pout' : Q($X → $prop) ← pmReduce Pout
  let Q'' : Q($X → $prop) ← pmReduce Q'

  -- Add the new goal into the proof state upon applying the case destruction patterns
  match mPclose with
  | ~q(some $f) =>
    let f' : Q($X → $prop) ← pmReduce f
    let pf : Q(∀ x, $e'' ∗ $Pout x ∗ $f x ⊢ $Q' x) ←
      withLocalDeclDQ (← mkFreshUserName .anonymous) X fun x => do
        match closePat with
        | some closePat =>
          iCasesCore _ hyps'' q($Q'' $x) (.conjunction [casesPat, closePat])
            q(false) q(iprop($Pout' $x ∗ $f' $x)) >>=
          (mkLambdaFVars #[x] ·)
        -- Throw an error if `hclose` is not given, but `mPclose` is not `none`
        | none => throwError "iinv: missing cases pattern for the closing hypothesis"
    return q(tac_inv_elim $inst $hϕ $pf $pfEq $pfPin)
  | ~q(none) =>
    let pf : Q(∀ x, $e'' ∗ $Pout x ⊢ $Q' x) ←
      withLocalDeclDQ (← mkFreshUserName .anonymous) X fun x => do
        iCasesCore _ hyps'' q($Q'' $x) casesPat q(false) q($Pout' $x) >>=
        (mkLambdaFVars #[x] ·)
    return q(tac_inv_elim $inst $hϕ $pf $pfEq $pfPin)

/-- Given a `Namespace` value, find a corresponding invariant hypothesis. -/
private def findInvariantWithNamespace {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (N : Q(Namespace)) (hyps : Hyps bi e) : ProofModeM <| Option IVarId := do
  match hyps with
  | .emp _ => return none
  | .hyp _ _ ivar _ ty _ =>
    return (← ProofModeM.trySynthInstanceQ q(IntoInv $ty $N)) <&> (fun _ => ivar)
  | .sep _ _ _ _ lhs rhs =>
    return (← findInvariantWithNamespace N rhs) <|> (← findInvariantWithNamespace N lhs)

syntax (name := iinv) "iinv " colGt term (" $$ " colGt ppSpace specPat)?
    " with " colGt icasesPat (colGt icasesPat)? : tactic

/--
  `iinv H with casesPat` opens an invariant hypothesis `H` and uses the
  cases pattern `casesPat` to destruct the result without any additional
  hypothesis for closing the invariant. The type class
  `elimInv_acc_without_close` is used with this tactic.

  `iinv H with casesPat closePat` opens an invariant hypothesis `H`,
  uses the cases pattern `casesPat` to destruct the result and generates a
  hypothesis for closing the invariant, which is destructed by the cases
  pattern `closePat`. The type class `elimInv_acc_with_close` is used with
  this tactic.

  Furthermore, the following syntax is available.
  - `iinv N with casesPat`: similar to `iinv H with casesPat`, where
    an invariant with the namespace `N` is opened.
  - `iinv H $$ specPat with casesPat`: similar to `iinv H with casesPat`,
    with a specialisation pattern `specPat` for resource consumption needed
    to open the invariant. Without `specPat`, the specialisation pattern is
    by default the auto-framing of spatial hypotheses.
-/
elab_rules : tactic
  | `(tactic| iinv $t:term $[$$ $spat:specPat]? with $casesPat:icasesPat $[$closePat:icasesPat]?) => do
    -- Parse the introduction and selection patterns
    let specPat ← liftMacroM <| spat.mapM SpecPat.parse
    let casesPat ← liftMacroM <| iCasesPat.parse casesPat
    let closePat ← liftMacroM <| closePat.mapM iCasesPat.parse

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
        | none => throwError m!"iinv: invariant hypothesis with the namespace {N} not found"

      let pf ← iInvCore hyps goal ivar specPat casesPat closePat
      mvar.assign pf
