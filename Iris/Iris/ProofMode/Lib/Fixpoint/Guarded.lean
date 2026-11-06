/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.Approx
public import Iris.BI.Lib.FixpointBanach
public import Iris.ProofMode.Lib.Fixpoint.Common
public import Iris.ProofMode.Lib.Fixpoint.Tupling

/-! # `iguarded`

Guarded fixpoints via `partial_fixpoint` on `Iris.Approx`: `Approx.lift` of the body is always
monotone, and contractiveness makes the fixpoint exact. -/

namespace Iris.Fixpoint
open Lean Elab Command Meta Term

/-! ## Building commands -/

/-- The arguments `binders` bind: explicit ones positionally, implicit ones by name, instances
omitted. -/
meta def binderArgs (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) :
    MacroM (Array Term) :=
  binders.foldlM (init := #[]) fun acc b => do
    let ids := b.raw[1].getArgs.filter (·.isIdent) |>.map (⟨·⟩ : Syntax → Ident)
    match b.raw.getKind with
    | ``Lean.Parser.Term.explicitBinder => return acc ++ ids.map (⟨·.raw⟩)
    | ``Lean.Parser.Term.implicitBinder | ``Lean.Parser.Term.strictImplicitBinder =>
      ids.foldlM (init := acc) fun acc id => do
        return acc.push ⟨(← `(Lean.Parser.Term.namedArgument| ($id := $id))).raw⟩
    | _ => return acc

/-- Add `attr` to the attributes in `mods`. -/
meta def addAttribute (mods : TSyntax ``Lean.Parser.Command.declModifiers)
    (attr : TSyntax ``Lean.Parser.Term.attrInstance) :
    CommandElabM (TSyntax ``Lean.Parser.Command.declModifiers) := do
  let old : Array (TSyntax ``Lean.Parser.Term.attrInstance) := match mods.raw[1].getOptional? with
    | some stx => stx[1].getSepArgs.map (⟨·⟩)
    | none => #[]
  let all : Syntax.TSepArray ``Lean.Parser.Term.attrInstance "," := .ofElems (old.push attr)
  let attrs ← `(Lean.Parser.Term.attributes| @[$all,*])
  return ⟨mods.raw.setArg 1 (mkNullNode #[attrs])⟩

/-- Elaborate `cmd` and return whether it succeeded; on failure, drop its messages and
declarations. -/
meta def tryElabCommand (cmd : TSyntax `command) : CommandElabM Bool := do
  let (msgs, env) := ((← get).messages, ← getEnv)
  modify fun s => { s with messages := {} }
  elabCommand cmd
  let ok := !(← get).messages.hasErrors
  modify fun s => { s with messages := if ok then msgs ++ s.messages else msgs }
  unless ok do setEnv env
  return ok

/-- Elaborate the theorem `cmd`, omitting section instances its statement does not use. -/
meta def elabTheorem (cmd : TSyntax `command) : CommandElabM Unit := do
  -- `omit` takes no antiquotation for its binders: replace the placeholder's.
  let omitting (insts : Array Syntax) : CommandElabM (TSyntax `command) := do
    let stx ← `(command| omit [Inhabited Nat] in $cmd)
    return ⟨stx.raw.modifyArg 0 (·.setArg 1 (mkNullNode insts))⟩
  -- Probe each instance: omitting a used one is an error. Probes run synchronously, so all their
  -- messages land in `messages` and can be dropped.
  let unused ← (← getScope).varDecls.filterM fun b => do
    unless b.raw.isOfKind ``Lean.Parser.Term.instBinder do return false
    -- A successful probe keeps its messages and declaration: drop both.
    let msgs := (← get).messages
    let sync (sc : Scope) := { sc with opts := Elab.async.set sc.opts false }
    let ok ← withoutModifyingEnv <| withScope sync do tryElabCommand (← omitting #[b.raw])
    modify fun s => { s with messages := msgs }
    return ok
  elabCommand (← if unused.isEmpty then pure cmd else omitting (unused.map (·.raw)))

/-- `mods`, with the modifiers that `extra` sets added. `declModifiers` args: docstring (0),
attributes (1), visibility (2), `protected` (3), `noncomputable` (4), `unsafe` (5),
`partial`/`nonrec` (6). -/
meta def addModifiers (mods extra : TSyntax ``Lean.Parser.Command.declModifiers) :
    TSyntax ``Lean.Parser.Command.declModifiers :=
  ⟨(List.range extra.raw.getNumArgs).foldl (init := mods.raw) fun m i =>
    if extra.raw[i].isNone then m else m.setArg i extra.raw[i]⟩

/-- The visibility of `mods`, for the generated declarations. Rebuilt from the syntax: reusing the
user's keyword, or `elabModifiers`, would warn that it is redundant. -/
meta def visibilityOf (mods : TSyntax ``Lean.Parser.Command.declModifiers) :
    CommandElabM (TSyntax ``Lean.Parser.Command.declModifiers) :=
  match mods.raw[2].getOptional? with
  | some v => if v.isOfKind ``Lean.Parser.Command.private then `(declModifiers| private)
    else `(declModifiers| public)
  | none => `(declModifiers|)

/-! ## The laws of `FixpointBanach` -/

/-- The laws of `Iris.BI.Lib.FixpointBanach`, restated for each guarded fixpoint. -/
meta def guardedLemmas : List (Name × Name) :=
  [(`persistent, ``fixpoint_persistent), (`affine, ``fixpoint_affine),
   (`absorbing, ``fixpoint_absorbing), (`persistent_absorbing, ``fixpoint_persistent_absorbing),
   (`persistent_affine, ``fixpoint_persistent_affine), (`plain, ``fixpoint_plain),
   (`plain_absorbing, ``fixpoint_plain_absorbing), (`plain_affine, ``fixpoint_plain_affine)]

/-- Restate the `FixpointBanach` laws for `declName` (with `nBinders` arguments), reading
everything off `name.eq_fixpoint`. The laws are about `fixpoint (conj name.pre)`, which is
`uncurry name` by `fixpoint_conj`. Laws with missing instances (`plain` without `Sbi`) are
skipped. -/
meta def emitGuardedLemmas (declName : Name) (nBinders : Nat) : TermElabM Unit := do
  let info ← getConstInfo (declName ++ `eq_fixpoint)
  -- `name.eq_fixpoint params {inst} binders : name params binders = fixpoint name.pre binders`,
  -- where `params` are the section variables `name` takes.
  let nParams := (← forallTelescope info.type fun xs _ => pure xs.size) - 1 - nBinders
  forallBoundedTelescope info.type nParams fun params rest => do
  let .forallE _ inhTy _ _ := rest | throwError "iguarded: unexpected{indentExpr rest}"
  let_expr Inhabited sig := inhTy | throwError "iguarded: unexpected{indentExpr inhTy}"
  let inh ← synthInstance inhTy
  let eqFix := mkAppN (Lean.mkConst info.name (info.levelParams.map mkLevelParam)) (params.push inh)
  -- `name params = fixpoint name.pre`, by `funext` over the binders.
  let (fn, fixPre, eqPre) ← forallTelescope (← inferType eqFix) fun xs eq => do
    let some (_, lhs, rhs) := eq.eq? | throwError "iguarded: unexpected{indentExpr eq}"
    let proof ← xs.foldrM (init := mkAppN eqFix xs) fun x p => do
      mkAppM ``funext #[← mkLambdaFVars #[x] p]
    return (lhs.stripArgsN xs.size, rhs.stripArgsN xs.size, proof)
  let_expr fixpoint _ _ _ pre preContractive := fixPre
    | throwError "iguarded: unexpected{indentExpr fixPre}"
  let eqPre ← mkExpectedTypeHint eqPre (← mkEq fn fixPre)
  let T ← Tupling.ofCurried sig
  let (neU, neC) := (← T.neUncurry, ← T.neCurry)
  let G ← T.conj pre
  let contractive ← mkAppOptM ``contractive_conj
    #[sig, ← mkArrow T.A T.prop, none, none, pre, preContractive, T.uncurry, T.curry, neU, neC]
  for (suffix, lemma) in guardedLemmas do
    -- Applying the law synthesizes its instances, which may be missing.
    let some general ← observing? (mkAppOptM lemma #[T.prop, none, T.A, G, contractive])
      | continue
    let before ← instantiateMVars (← inferType general)
    let some fixpoint := before.find? (·.isAppOfArity ``fixpoint 5)
      | throwError "iguarded: no fixpoint in{indentExpr before}"
    let_expr fixpoint _ _ inhTuples _ _ := fixpoint | unreachable!
    -- `fixpoint (conj name.pre) = uncurry (fixpoint name.pre) = uncurry name`.
    let conj ← mkAppOptM ``fixpoint_conj #[sig, ← mkArrow T.A T.prop, none, none, none, none, inh,
      inhTuples, pre, preContractive, T.uncurry, T.curry, neU, neC,
      ← pointwiseRfl sig (fun a => pure (T.curry.beta #[T.uncurry.beta #[a]])) pure]
    let eq ← mkExpectedTypeHint
      (← mkEqTrans (← mkEqSymm conj) (← mkCongrArg T.uncurry (← mkEqSymm eqPre)))
      (← mkEq fixpoint (T.uncurry.beta #[fn]))
    let (type, proof) ← T.restate general fixpoint eq fn
    emitThm (declName ++ suffix) info.levelParams (← mkForallFVars params type)
      (← mkLambdaFVars params proof)

/-! ## The command -/

/-- Check that `sig`, the type of `name`, is an inhabited COFE: its approximations form a CCPO. -/
meta def checkGuardedType (name : Ident) (ty sig : Term) : CommandElabM Unit :=
  -- Implicit arguments such as `α` in `(x : α)` are bound automatically, as in a declaration.
  runTermElabM fun _ => Term.withAutoBoundImplicit do
    -- Report errors in the type as such, not as a missing instance.
    let sigE ← withoutErrToSorry <| elabType sig
    synthesizeSyntheticMVarsNoPostponing
    for (cls, inst) in [("IsCOFE", ← `((inferInstance : Iris.IsCOFE $sig))),
        ("Inhabited", ← `((inferInstance : Inhabited $sig)))] do
      let ok ← observing? do
        discard <| withoutErrToSorry <| elabTerm inst none
        synthesizeSyntheticMVarsNoPostponing
      if ok.isNone then
        throwErrorAt ty "iguarded: the type of `{name}`, `{← instantiateMVars sigE}`, must be a \
          COFE with a default point, but there is no `{cls}` instance"

/-- The number of arguments that `binders` bind. -/
meta def binderCount (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) : Nat :=
  binders.foldl (init := 0) fun n b =>
    if b.raw.isOfKind ``Lean.Parser.Term.instBinder then n + 1 else n + b.raw[1].getNumArgs

/-- Reject what the generated syntax does not support: dotted names, unnamed or defaulted
arguments, and explicit section variables. The last check is syntactic and conservative: it also
rejects such a name bound inside the body. -/
meta def checkGuardedInput (name : Ident)
    (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (ty body : Term) :
    CommandElabM Unit := do
  unless name.getId.isAtomic do
    throwErrorAt name "iguarded: the name must be atomic; open a namespace instead"
  for b in binders do
    if b.raw.isOfKind ``Lean.Parser.Term.explicitBinder && !b.raw[3].isNone then
      throwErrorAt b "iguarded: arguments cannot have default values"
    for x in b.raw[1].getArgs do
      if x.isOfKind ``Lean.Parser.Term.hole then throwErrorAt x "iguarded: name every argument"
  -- The names the command uses (`m` for `m.succ`), apart from its binders.
  let bound : NameSet := binders.foldl (init := {}) fun acc b =>
    b.raw[1].getArgs.foldl (init := acc) fun acc x => if x.isIdent then acc.insert x.getId else acc
  let mut used : NameSet := {}
  for stx in [ty.raw, body.raw] ++ binders.toList.map (·.raw) do
    for s in stx.topDown do
      if s.isIdent && !bound.contains s.getId.getRoot then used := used.insert s.getId.getRoot
  for b in (← getScope).varDecls do
    unless b.raw.isOfKind ``Lean.Parser.Term.explicitBinder do continue
    for x in b.raw[1].getArgs do
      if x.isIdent && used.contains x.getId then
        throwErrorAt name "iguarded: explicit section variables, such as `{x.getId}`, are not \
          supported; make them implicit, or arguments"

/-- Elaborate `iguarded name binders : ty := body`, as syntax. It emits
* `name.pre := fun name binders => body` and `name.pre.contractive`,
* `name.approx := lift name.pre name.approx`, by `partial_fixpoint`,
* `name.impl`, a `partial def` that `name` is implemented by, if it compiles (else `name` is
  noncomputable),
* `name := get name.approx`, `name.unfold`, and `name.eq_fixpoint` (for any default point),
* the `FixpointBanach` laws, such as `name.persistent`. -/
meta def elabGuarded (mods : TSyntax ``Lean.Parser.Command.declModifiers) (name : Ident)
    (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (ty body : Term)
    (contractive : Option (TSyntax `contractiveClause)) : CommandElabM Unit := do
  checkGuardedInput name binders ty body
  let tac ← match contractive with
    | some clause =>
      let `(contractiveClause| contractive_by $tac) := clause | throwUnsupportedSyntax
      pure tac
    | none => withRef name do
      defaultTactic `iguarded `contractive_by `iris.fixpoint.contractiveDefault
        (← `(tactic| iguarded_contractive_default)) "contractiveness"
  let vis ← visibilityOf mods
  -- `name.pre` and `name.approx` share `name`'s visibility and `noncomputable`.
  let userNoncomputable := !mods.raw[4].isNone
  let noncomputableMods ← `(declModifiers| noncomputable)
  let auxMods := if userNoncomputable then addModifiers vis noncomputableMods else vis
  let suffixed (s : Name) := mkIdentFrom name (name.getId ++ s)
  let (pre, approx) := (suffixed `pre, suffixed `approx)
  let (contractiveName, unfold) := (suffixed (`pre ++ `contractive), suffixed `unfold)
  let impl := suffixed `impl
  let args ← liftMacroM <| binderArgs binders
  let funBinders : TSyntaxArray ``Lean.Parser.Term.funBinder := binders.map (⟨·.raw⟩)
  let lam (e : Term) : CommandElabM Term :=
    if binders.isEmpty then pure e else `(fun $funBinders* => $e)
  let app (f : Term) : CommandElabM Term := if args.isEmpty then pure f else `($f $args*)
  let sig ← if binders.isEmpty then pure ty else `(∀ $binders*, $ty)
  checkGuardedType name ty sig
  -- Exposed, so that other modules can unfold it for the laws.
  let preMods ← addAttribute auxMods (← `(Lean.Parser.Term.attrInstance| expose))
  elabCommand (← `(command|
    $preMods:declModifiers def $pre : $sig → $sig := fun ($name : $sig) => $(← lam body)))
  elabCommand (← `(command|
    $vis:declModifiers instance $contractiveName:ident :
        Iris.OFE.Contractive ($pre : $sig → $sig) where
      distLater_dist := by $tac))
  elabCommand (← `(command|
    $auxMods:declModifiers def $approx : Iris.Approx $sig := Iris.Approx.lift $pre $approx
    partial_fixpoint monotonicity Iris.Approx.lift_mono _))
  -- `Approx.get` is noncomputable, so compiled code runs the recursion directly, if there are
  -- arguments. `partial def` may fail to see that the type is inhabited.
  let compiled ← if userNoncomputable || binders.isEmpty then pure false else
    tryElabCommand (← `(command|
      $(addModifiers vis (← `(declModifiers| partial))):declModifiers def $impl $binders* : $ty :=
        $pre $(← lam (← app impl)) $args*))
  let nameMods ← if compiled then
      addAttribute mods (← `(Lean.Parser.Term.attrInstance| implemented_by $impl:ident))
    else pure (addModifiers mods noncomputableMods)
  elabCommand (← `(command|
    $nameMods:declModifiers def $name $binders* : $ty := Iris.Approx.get $approx $args*))
  -- Use the full name from here on, as `protected` requires.
  let declName ← resolveDeclared name
  let self : Term := mkCIdentFrom name declName
  -- With implicit binders, `name` is passed as `fun {x} => name (x := x)`.
  let approxEq := mkIdentFrom name (name.getId ++ `approx ++ `eq_1)
  let explicit := binders.all (·.raw.isOfKind ``Lean.Parser.Term.explicitBinder)
  let selfFn ← if explicit then `(($self : $sig)) else lam (← `(($(← app self) : $ty)))
  elabTheorem (← `(command|
    $vis:declModifiers theorem $unfold $binders* :
        $(← app self) = $pre $selfFn $args* :=
      congrArg (fun f => f $args*) (Iris.Approx.lift_fix_get $pre (Eq.symm $approxEq))))
  elabTheorem (← `(command|
    $vis:declModifiers theorem $(suffixed `eq_fixpoint) {inhabited : Inhabited ($sig)} $binders* :
        $(← app self) = (@Iris.fixpoint _ _ inhabited ($pre : $sig → $sig) _ : $sig) $args* :=
      congrArg (fun f => f $args*)
        (Iris.Approx.get_eq_fixpoint (α := $sig) $pre (Eq.symm $approxEq))))
  -- From here on, `name` is only reached through `unfold` and `eq_fixpoint`.
  elabCommand (← `(command| attribute [irreducible] $(mkCIdentFrom name declName):ident))
  liftTermElabM do emitGuardedLemmas declName (binderCount binders)

/-- Guarded Iris fixpoint of a body contractive in the recursive function. -/
elab mods:declModifiers "iguarded " name:ident binders:bracketedBinder* " : " ty:term
    " := " body:term contractive:(contractiveClause)? : command =>
  elabGuarded mods name binders ty body contractive

end Iris.Fixpoint
