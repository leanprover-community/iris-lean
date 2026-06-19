/-
Copyright (c) 2026 Yunsong Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang, Michael Sammler, Alvin Tang
-/
module

public meta import Iris.ProofMode.Tactics.Basic
public meta import Iris.ProofMode.Tactics.Assumption
public meta import Iris.ProofMode.Tactics.Cases
public meta import Iris.ProofMode.Patterns.CasesPattern
public meta import Iris.ProofMode.ClassesMake
public meta import Iris.ProofMode.Tactics.RevertIntro
public meta import Iris.ProofMode.Tactics.Revert
public meta import Lean.Meta.Tactic.TryThis

namespace Iris.ProofMode

public meta section
open BI Std Lean Elab Tactic Meta Qq Parser.Tactic

syntax (name := iinduction) "iinduction" colGt term
    ("using" ident)?
    ("generalizing" (ppSpace colGt selPat)+)?
    (inductionAlts)? : tactic

/-- Information from the tactic user for an induction subgoal -/
private structure Alt where
  -- The name of the constructor
  ctor : Name
  -- The alternative names supplied by the tactic user
  vars : Array <| TSyntax `Lean.binderIdent
  -- User-supplied tactics for this case, `none` if a hole (`_` or `?_`) is given
  tacs : Option <| TSyntax `Lean.Parser.Tactic.tacticSeq
  -- The syntax, useful for error message printing
  stx : TSyntax `Lean.Parser.Tactic.inductionAlt

/-- Information from the tactic user for all induction subgoals -/
private structure Alts where
  -- User-supplied tactic to be applied before splitting into cases
  tac : Option <| TSyntax `tactic
  -- The alternative cases supplied by the user
  alts : Array Alt
  -- The wildcard case, if supplied by the user
  wildcard : Option Alt
  -- The syntax, useful for error message printing
  stx : TSyntax `Lean.Parser.Tactic.inductionAlts

/--
  Given user-supplied alternative names and tactic sequences, parse the syntax
  and return an `Alts` instance.
-/
private def parseInductionAlts (altsSyntax : TSyntax `Lean.Parser.Tactic.inductionAlts) :
    TacticM Alts := do
  -- For parsing the user-supplied names for variables and induction hypotheses
  let parseVars (vars : Array Syntax) : TacticM (Array (TSyntax `Lean.binderIdent)) := do
    vars.mapM fun v =>
      match v with
      | `(ident| $id:ident) => `(binderIdent| $id:ident)
      | _                   => `(binderIdent| _)

  let mut parsedAlts := #[]

  match altsSyntax with
  | `(inductionAlts| with $[$tac]? $[$alts]*) =>
    for alt in alts do
      let (lhs, tacs) ← match alt with
        | `(inductionAlt| $[$lhs:inductionAltLHS]* => $tac:tacticSeq) => pure (lhs, some tac)
        | `(inductionAlt| $[$lhs:inductionAltLHS]* => $_:hole)
        | `(inductionAlt| $[$lhs:inductionAltLHS]* => $_:syntheticHole) => pure (lhs, none)
        | _ => throwErrorAt alt "iinduction: invalid syntax"

      for l in lhs do
        match l with
        | `(inductionAltLHS| | $ctor:ident $[$vars]*)
        | `(inductionAltLHS| | @ $ctor:ident $[$vars]*) =>
          parsedAlts := parsedAlts.push ⟨ctor.getId, ← parseVars vars, tacs, alt⟩
        | `(inductionAltLHS| | $_:hole $[$vars]*) =>
          if parsedAlts.size < alts.size - 1 then
            throwErrorAt alt
              s!"iinduction: invalid occurrence of the wildcard alternative `| _ => ...`: ".append
              "It must be the last alternative"
          return ⟨tac, parsedAlts, some ⟨.anonymous, ← parseVars vars, tacs, alt⟩, altsSyntax⟩
        | _ => throwErrorAt l "iinduction: invalid syntax"
    return ⟨tac, parsedAlts, none, altsSyntax⟩
  | _ => throwErrorAt altsSyntax "iinduction: invalid syntax"

/--
  This theorem is used for updating the proof in `InductionState` as `addIHs`
  iterates through the list of induction hypotheses and introduces them from
  the regular Lean context into the intuitionistic context.

  The initial set of hypotheses that exist in the Iris context after applying
  Lean's built-in induction step is represented by `P`. Since the spatial
  context is empty (that is, all hypotheses exist in intuitionistic context),
  `P ⊢ □ P` must hold.

  The proposition `Q` represents these initial hypotheses as well as induction
  hypotheses introduced into the intuitionistic context up until the most
  recent `addIHs` iteration. At every iteration of `addIHs`, an induction
  hypothesis `R` is obtained upon type class synthesis with `IntoIH`. The proof
  for `InductionState` is obtained using this theorem accordingly.
-/
@[rocq_alias tac_revert_ih]
theorem revert_IH [BI PROP] {P Q R : PROP} {φ}
    (ih : φ)
    (h1 : P ⊢ □ P)
    (h2 : P ⊢ Q)
    (inst : IntoIH φ P R) :
    P ⊢ (Q ∗ □ R) := calc
  _ ⊢ □ P         := h1
  _ ⊢ □ P ∗ □ P   := intuitionistically_sep_dup.mp
  _ ⊢ □ P ∗ □ □ P := sep_mono_right intuitionistically_idem.mpr
  _ ⊢ □ P ∗ □ R   := sep_mono_right <| intuitionistically_mono <| inst.into_ih ih
  _ ⊢ □ Q ∗ □ R   := sep_mono_left <| intuitionistically_mono h2
  _ ⊢ Q ∗ □ R     := sep_mono_left intuitionistically_elim

/--
  Designed to be a mutable state such that `newHyps` contains induction
  hypotheses generated by Lean's built-in induction.
-/
private structure InductionState {u} {prop : Q(Type u)} {bi} (origE : Q($prop)) where
  {newE : Q($prop)}
  (newHyps : Hyps bi newE)
  (pf : Q($origE ⊢ $newE))

/-- Introduce into the intuitionistic context of the Iris proof state. -/
private def addIHs {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (pfIntHyps : Q($e ⊢ □ $e)) (hyps : Hyps bi e) (ihFVars : List FVarId) :
    ProofModeM (@InductionState u prop bi e) := do

  -- Initialise the mutable instance of `InductionState`
  let mut st := { newHyps := hyps, pf := q(.rfl) }

  -- Iteratively move the induction hypotheses into the intuitionistic context
  for i in ihFVars do
    let ⟨_u, (ϕ : Q(Prop)), (p : Q($ϕ))⟩ ← inferTypeQ <| mkFVar i

    -- Obtain the proposition to be introduced into the intuitionistic context
    let Q ← mkFreshExprMVarQ q($prop)
    let some inst ← ProofModeM.trySynthInstanceQ q(IntoIH $ϕ $e $Q)
    | throwError m!"iinduction: unable to perform type class synthesis with IntoIH for the induction hypothesis {ϕ}"

    -- Introduce the induction hypothesis into the intuitionistic context
    let nameIdent := mkIdent <| ← i.getUserName
    let binderIdent ← `(binderIdent| $nameIdent:ident)
    let ⟨_, newHyps⟩ ← Hyps.addWithInfo bi binderIdent q(true) Q st.newHyps
    let pf := q(revert_IH $p $pfIntHyps $st.pf $inst)

    st := { newHyps, pf }

  return st

private def throwMissingAlt {α} (ctor : Name) : ProofModeM α :=
  throwError "iinduction: alternative `{ctor.getString!}` has not been provided"

/--
  Check that all the alternative names are valid and that there are no duplicates.
  Otherwise, throw an error on the corresponding line.
-/
private def checkCtors (ctors : List Name) (parsedAlts : Alts) : ProofModeM Unit := do
  let mut handledCtors : Std.HashSet Name := {}

  for alt in parsedAlts.alts do
    if !ctors.contains alt.ctor then
      throwOrLogErrorAt alt.stx
        m!"iinduction: invalid alternative name `{alt.ctor}`"

    if handledCtors.contains alt.ctor then
      throwOrLogErrorAt alt.stx
        m!"iinduction: duplicate alternative name `{alt.ctor}`"

    handledCtors := handledCtors.insert alt.ctor

private def iInductionCore {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (hyps : Hyps bi e) (goal : Q($prop)) (fvar : FVarId)
    (parsedAlts : Option Alts) (altRecName : Option Name) (genSelTargets : List SelTarget) :
    ProofModeM Q($e ⊢ $goal) := do
  let targets := genSelTargets ++
    (hyps.spatialIVarIds.map ({ kind := .ipm ·, explicit := false })).filter (not <| (genSelTargets.map (·.kind)).contains ·.kind)

  -- Find the recursor name and constructor names of the inductive datatype
  let fvarType ← liftM <| (inferType <| mkFVar fvar) >>= whnf
  let recName ← match fvarType.getAppFn with
  | .const indName _ =>
    match (← getEnv).find? indName with
    | some (.inductInfo _) =>
      altRecName.elim
        (getCustomEliminator? #[mkFVar fvar] true <&> (·.getD <| mkRecName indName))
        pure
    | _ => throwError "iinduction: {indName} is not inductive"
  | _ => throwError "iinduction: unable to determine inductive type"

  let matcher := fun ctor alt => alt.ctor != .anonymous && ctor == alt.ctor

  -- Find the constructor names
  let recCtors := ((← Lean.Meta.getElimInfo recName).altsInfo.map (·.name)).toList

  -- Check that all alternative names supplied by the user are valid
  parsedAlts.forM fun parsedAlts => do
    checkCtors recCtors parsedAlts
    if recCtors.length == parsedAlts.alts.size then
      parsedAlts.wildcard.forM fun w =>
        throwOrLogErrorAt w.stx "iinduction: wildcard alternative is not needed"

  -- Define the names for variables and induction hypotheses if supplied by user
  let varNames ←
    match parsedAlts with
    | none =>
      pure <| recCtors.toArray.map <| fun _ => { explicit := true, varNames := [] }
    | some parsedAlts => do
      recCtors.toArray.mapM <| fun ctor =>
      match parsedAlts.alts.find? (matcher ctor) <|> parsedAlts.wildcard with
      | some alt =>
        pure { explicit := true, varNames := alt.vars.toList.map <|
          fun stx => match stx.raw with
          | `(binderIdent| $id:ident) => id.getId
          | _ => Name.mkSimple "_" }
      | none =>
        -- Defer the check if the first tactic for the `with` syntax is given
        if parsedAlts.tac.isSome then
          pure { explicit := true, varNames := [] }
        else
          throwMissingAlt ctor

  let pf ← iRevertIntro hyps goal targets <|
    fun hyps' goal' kIntro => do
      -- Create a new metavariable for the proof goal upon reverting hypotheses
      let m ← mkBIGoal hyps' goal'

      -- Use built-in induction in Lean to generate the subgoals for induction
      let subgoals ← m.mvarId!.withContext do
        m.mvarId!.induction fvar recName varNames

      -- Handle each subgoal generated by Lean's induction
      for ⟨s, ctor⟩ in subgoals.toList.zip recCtors do
        s.mvarId.withContext do
          s.mvarId.setTag ctor
            -- Obtain the type of the induction subgoal
            let sType ← s.mvarId.getType >>= instantiateMVars

            let some irisGoal := parseIrisGoal? sType
            -- This should not happen
            | throwOrLogError "iinduction: fail to parse induction subgoal"

            -- Find the induction hypotheses generated by Lean's `induction` tactic
            let ihFVars ← s.mvarId.withContext getLCtx >>=
              (·.decls.toList.reduceOption.filterM
                (instantiateMVars ·.type <&> (·.find? isIrisGoal |>.isSome)) <&>
                (·.map (·.fvarId)))

            -- A proof that all hypotheses in the Iris goal exist in the intuitionistic context
            let some pfIntHyps := irisGoal.hyps.buildIntuitionisticProof
            | throwOrLogError "iinduction: spatial context should be empty"

            -- Introduce the induction hypothesis back into the Iris proof state
            let st ← addIHs pfIntHyps irisGoal.hyps ihFVars

            parsedAlts.forM fun parsedAlts => do
              parsedAlts.alts.find? (matcher ctor) <|> parsedAlts.wildcard |>.forM
                fun ⟨_, vars, _, stx⟩ => do
                  -- Check that the number of arguments matches what are needed
                  if vars.size > s.fields.size then
                    throwOrLogErrorAt stx <|
                      s!"iinduction: too many variable names provided at alternative `{ctor}`: ".append
                      s!"{vars.size} provided, but {s.fields.size} expected"
                  -- Label the arguments with their types, shown when the user hovers over them
                  for ⟨fieldFVar, varStx⟩ in s.fields.zip vars do
                    if let `(binderIdent| $id:ident) := varStx then
                      let lctx ← getLCtx
                      let fieldType ← inferType fieldFVar
                      addLocalVarInfo id lctx fieldFVar fieldType true

            let pf' ← withoutFVars (u := 0) ihFVars.toArray <| kIntro st.newHyps irisGoal.goal <|
              fun hyps goal => do match parsedAlts with
                -- Remove the induction hypotheses from the regular Lean context
                | none => addBIGoal hyps goal ctor
                | some parsedAlts =>
                  -- Check if the alternative names for this constructor are supplied by the user
                  match parsedAlts.alts.find? (matcher ctor) <|> parsedAlts.wildcard with
                  | some ⟨_, _, tacticSeq, stx⟩ =>
                    -- Generate the induction subgoal, label the induction subgoal with `ctor`
                    match tacticSeq with
                    | none => addBIGoal hyps goal ctor
                    -- Run the tactics supplied by the user, if available
                    | some tacticSeq =>
                        let ⟨pf, allSolved⟩ ←
                          addBIGoalRunTactics hyps goal ctor parsedAlts.tac tacticSeq
                        -- Throw an error if the first tactic already solves the goal
                        if allSolved then
                          throwOrLogErrorAt stx
                            s!"iinduction: alternative `{ctor.getString!}` is not needed"
                        pure pf
                  -- Alternative names not found, acceptable only when `firstTactic` solves it
                  | none =>
                    match parsedAlts.tac with
                    -- No first tactic given, the alternative name is missing
                    | none => throwMissingAlt ctor
                    | some firstTactic =>
                      let m ← mkBIGoal hyps goal ctor
                      let subgoals ← evalTacticAt firstTactic m.mvarId!
                      -- First tactic supplied by the user but does not completely solve this case
                      if !subgoals.isEmpty then
                        throwOrLogErrorAt parsedAlts.stx
                          m!"iinduction: alternative `{ctor.getString!}` has not been provided"
                      pure m

            -- Fill the metavariable for the induction subgoal generated by Lean
            s.mvarId.assign q($(st.pf).trans $pf')

      return m

  return pf

private def generalizeTermWithFVar (x : TSyntax `term) : TacticM FVarId := do
  let e ← withMainContext <| elabTerm x none
  let e ← instantiateMVars e

  -- Return the `FVarId` value directly if the term expresson is a free variable
  if e.isFVar then
    return e.fvarId!

  -- Otherwise, generalise the term expression and return the `FVarId`
  let mvarId ← getMainGoal
  let (fvars, newMVarId) ← mvarId.generalize #[{ expr := e }]
  replaceMainGoal [newMVarId]

  return fvars[0]!

/--
  The `iinduction` tactic applies induction in the Iris Proof Mode in a similar
  way as the `induction` tactic. Given an expression `e`, the application of
  `iinduction e` performs the following steps:
  1. Generalises the expression `e` using `Lean.Meta.Tactic.Generalize`.
  2. Reverts all hypotheses in the spatial context, as well as those specified
     in the `generalizing` clause.
  3. Obtain the induction subgoals.
  4. Moves all induction hypotheses into the intuitionstic context.
  5. Introduce hypotheses reverted in steps 2 and 3 back into the Iris contexts.

  Similar to the regular `induction` tactic, the following syntax is available.
  - `iinduction e using r`: to specify the induction principle `r`.
  - `iinduction e generalizing z₁ ... zₙ`: to generalise `z₁ ... zₙ`,
    which is expressed as a selection pattern. Both Iris hypotheses and pure
    Lean hypotheses can be generalised.
  - `iinduction e with | constr₁ => tac₁ | ... | constrₙ => tacₙ`:
    arguments are optionally given names or otherwise remain inaccessible.

  As an example, consider the following Iris context, where `n : Nat`.

  ```
  ∗HP : P
  □HQ : Q m
  □HR : R
  ∗HS : S
  □HT : T n
  ```

  By applying `iinduction n generalizing HT`, all spatial hypotheses
  (`HP` and `HS`) are reverted. The hypothesis `HT` must also be reverted
  because it involves the induction target `n`.

  By applying `iinduction n generalizing HQ HT`, the hypotheses `HQ`
  are additionally reverted and thus included as a wand premise in the induction
  hypothesis.

  One can also generalise pure variables in the regular Lean context.
  If there exists some pure/Iris hypotheses that is forward-dependent, they
  should also be included in the `generalizing` clause. In the example above,
  instead of `iinduction n generalizing %m HT`, one should use
  `iinduction n generalizing %m HQ HT`.
-/
elab_rules : tactic
  | `(tactic| iinduction $x
        $[using $r]?
        $[generalizing $genSelPats*]?
        $[$alts]?) => do
    let fvar ← generalizeTermWithFVar x

    -- Parse the recursor name provided by the user
    let recName := r.map (·.getId)

    -- Parse the list of alternative names supplied by the user
    let parsedAlts ← alts.mapM parseInductionAlts

    ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
      let mkTactic := fun newPats => `(tactic| iinduction $x $[using $r]? generalizing $newPats* $[$alts]?)
      let genSelTargets ← do match genSelPats with
      | none =>
        checkDependentHyps "iinduction" hyps [] fvar #[] mkTactic
        pure []
      | some genSelPats =>
        -- Parse the selection patterns for generalising hypotheses
        let parsedGenSelPats ← liftMacroM <| SelPat.parse genSelPats
        let genSelTargets ← SelPat.resolve hyps parsedGenSelPats
        -- Check for dependencies with the hypotheses in the selection targets
        checkDependentHyps "iinduction" hyps genSelTargets fvar genSelPats mkTactic
        pure genSelTargets

      let pf ← iInductionCore hyps goal fvar parsedAlts recName genSelTargets
      mvar.assign pf
