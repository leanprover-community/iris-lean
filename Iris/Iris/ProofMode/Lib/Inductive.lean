/-
Copyright (c) 2026 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public meta import Iris.ProofMode.Lib.Fixpoint

namespace Iris

open Lean Elab Command Meta Term

/-- Syntax category for `iinductive` constructors. -/
declare_syntax_cat iinductiveConstructor
syntax "| " declModifiers ident fixpointBinder* " : " term : iinductiveConstructor

meta partial def iinductivePeelArrows (t : Term) : Array Term × Term :=
  match t with
  | `($dom → $cod) =>
    let (doms, cod') := iinductivePeelArrows cod
    (#[dom] ++ doms, cod')
  | _ => (#[], t)

meta partial def iinductivePeelWands (t : Term) : Array Term × Term :=
  match t with
  | `($dom -∗ $cod) =>
    let (doms, cod') := iinductivePeelWands cod
    (#[dom] ++ doms, cod')
  | _ => (#[], t)

meta partial def iinductiveCountNameArgs (name : Name) (t : Term) : Nat :=
  match t with
  | `($dom -∗ $cod) =>
    let count := iinductiveCountNameArgs name cod
    count + if let ⟨.node _ ``Parser.Term.app l⟩ := dom then if l[0]!.getId == name then 1 else 0 else 0
  | _ =>
    if let ⟨.node _ ``Parser.Term.app l⟩ := t then if l[0]!.getId == name then 1 else 0 else 0

meta partial def iinductivePeelInterleaved (t : Term) : Array Term × Array Term × Term :=
  let (arrowDoms, rest) := iinductivePeelArrows t
  let (wandDoms, rest') := iinductivePeelWands rest
  if arrowDoms.isEmpty && wandDoms.isEmpty then
    (#[], #[], t)
  else
    let (pures, resources, cod) := iinductivePeelInterleaved rest'
    (arrowDoms ++ pures, wandDoms ++ resources, cod)

meta def iinductiveAppArgs (t : Term) : Array Term :=
  match t with
  | `($_:ident $args*) => args
  | _ => #[]

-- Helper function to avoid additional `⌜False⌝`/`emp` terms from naive folding
private meta def combine (default : Term) (f : Term → Term → CommandElabM Term) (ts : Array Term) : CommandElabM Term :=
  if ts.isEmpty then return default
  else ts.foldlM f ts[0]! (start := 1)

meta def elabIInductiveDef (mods : TSyntax ``Lean.Parser.Command.declModifiers) (name : Ident)
    (binders : Array (TSyntax `fixpointBinder)) (type : Term) (ctors : Array (TSyntax `iinductiveConstructor))
    (monoBy : Option (TSyntax `fixpointMonotoneClause)) (neBy : Option (TSyntax `fixpointNonexpClause))
    : CommandElabM Unit := do
  let (args, iProp) := iinductivePeelArrows type

  let argIds ← args.mapM fun a => mkFreshIdent a
  let argBinders ← (argIds.zip args).mapM fun (i, t) => `(fixpointBinder| ($i : $t))

  let mut disjuncts : Array Term := #[]
  for ctor in ctors do
    let `(iinductiveConstructor| | $_:declModifiers $cName:ident
        $cBinders:fixpointBinder* : $cTy:term) := ctor
      | throwUnsupportedSyntax

    let mut existBinders : Array (Ident × Term) := #[]
    for b in cBinders do
      match b with
      | `(fixpointBinder| ($ids* : $t)) =>
        if t != iProp then
          for id in ids do
            existBinders := existBinders.push (id, t)
      | _ => throwUnsupportedSyntax

    let (pureAssumptions, resourceAssumptions, codomain) := iinductivePeelInterleaved cTy
    let codomainArgs := iinductiveAppArgs codomain
    if codomainArgs.size != argIds.size then
      throwErrorAt cName
        "iinductive: constructor '{cName.getId}' concludes in {codomainArgs.size} indices, expected {argIds.size}"

    -- pure assumptions and argument equalities
    let pureConjuncts ← pureAssumptions.mapM fun p => `(⌜$p⌝)
    let equalities ← (argIds.zip codomainArgs).mapM fun (x, e) => `(⌜$x = $e⌝)

    let mut disjunct ← combine (← `(emp)) (fun a t => `($a ∗ $t))
      (resourceAssumptions ++ pureConjuncts ++ equalities)

    for (id, t) in existBinders.reverse do
      let bid ← `(binderIdent| $id:ident)
      disjunct ← `(∃ ($bid : $t), $disjunct)

    disjuncts := disjuncts.push disjunct

  let disjunction ← combine (← `(⌜False⌝)) (fun a t => `($a ∨ $t)) disjuncts
  let defBody ← `(iprop($disjunction))
  let defBinders := binders ++ argBinders

  let declDef ← `(command|
    $mods:declModifiers fix $name:ident $defBinders* : $iProp := $defBody $[$monoBy]? $[$neBy]?)
  elabCommand declDef

  let mut selector : Array (TSyntax `tactic) := #[]

  for _ in ctors[1:] do selector := selector.push (← `(tactic| ileft))

  for ctor in ctors do
    let `(iinductiveConstructor| | $cMods:declModifiers $cName:ident
        $cBinders:fixpointBinder* : $cTy:term) := ctor | continue

    let mut names : Array Ident := #[]
    let mut types : Array Term := #[]
    for b in cBinders do
      match b with
      | `(fixpointBinder| ($ids* : $t)) =>
        for id in ids do
          names := names.push id
          types := types.push t
      | _ => continue

    let mut tacs : Array (TSyntax `tactic) := #[]

    tacs := tacs.push (← `(tactic| repeat iintro _))

    let occs := iinductiveCountNameArgs name.getId cTy
    let uLem := mkIdentFrom name (name.getId ++ `unfold)
    tacs := tacs.push (← `(tactic| rw (occs := [$(Syntax.mkNumLit (toString occs))]) [$uLem:ident]))

    let preDef := mkIdentFrom name (name.getId ++ `pre)
    tacs := tacs.push (← `(tactic| unfold $preDef))

    tacs := tacs ++ selector

    for name in names do
      tacs := tacs.push (← `(tactic| iexists $name))

    tacs := tacs.push (← `(tactic| simp))

    tacs := tacs.push (← `(tactic| iframe))

    let tac ← `(tacticSeq| $tacs*)

    let ctorBinds ← (names.zip types).mapM fun (i, t) => `(bracketedBinder| ($i : $t))
    let ctorName := mkIdentFrom name (name.getId ++ cName.getId)
    let ctorDef ← `(command|
      $cMods:declModifiers theorem $ctorName:ident $ctorBinds* : $cTy := by $tac)
    elabCommand ctorDef

    if selector.toList.getLast! == (← `(tactic| iright)) then
      selector := selector.pop.pop.push (← `(tactic| iright))
    else
      selector := selector.pop.push (← `(tactic| iright))

/-- Inductive predicate definition via the least fixpoint. -/
elab mods:declModifiers "iinductive " name:ident binders:fixpointBinder*
    monoPf:(fixpointMonotoneClause)? nePf:(fixpointNonexpClause)?
    " : " type:term " where " ctors:iinductiveConstructor* : command =>
  elabIInductiveDef mods name binders type ctors monoPf nePf
