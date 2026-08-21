/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Init
public import Iris.Std.DelabRule
public import Iris.Std.Notation

/-!
# Telescopes

A telescope is a list of types in which every type may depend on the values of the preceding
ones. Telescopes let a single binder stand for an arbitrary, statically unknown number of
dependent binders; `Iris.BI.tforall` and `Iris.BI.texist` use them to express `∀`/`∃` over such
a block of binders.
-/

@[expose] public section

namespace Iris.Std
open Iris.Std Lean PrettyPrinter Delaborator SubExpr

universe u v

/-- A telescope: a list of types where every type may depend on the values of the preceding
ones. -/
inductive Tele : Type (u + 1) where
  | nil : Tele
  | cons {X : Type u} (binder : X → Tele) : Tele

namespace Tele

/-- Conversion between a telescope and a nested dependent pair -/
def Arg : Tele.{u} → Type u
  | .nil => PUnit
  | .cons b => (x : _) × (b x).Arg

@[match_pattern] abbrev Arg.nil : Arg.{u} .nil := ⟨⟩

@[match_pattern] abbrev Arg.cons {b : X → Tele.{u}} (x : X) (xs : (b x).Arg) :
    (Tele.cons b).Arg := ⟨x, xs⟩

def Fun : (TT : Tele.{u}) → (TT.Arg → Type v) → Type (max u v)
  | .nil, T => ULift (T .nil)
  | .cons b, T => (x : _) → (b x).Fun fun xs => T (.cons x xs)

/-- The type of non-dependent telescopic functions from `TT` to `T`. -/
notation:25 TT:26 " -t> " T:25 => Tele.Fun TT fun _ => T

/-- Apply a telescopic function to a telescope argument. -/
def app : {TT : Tele.{u}} → {T : TT.Arg → Type v} → TT.Fun T → (xs : TT.Arg) → T xs
  | .nil, _, F, _ => ULift.down F
  | .cons _, _, F, .cons x xs => app (F x) xs

/-- Turn a function on telescope arguments into a telescopic function. -/
def bind : {TT : Tele.{u}} → {T : TT.Arg → Type v} → ((xs : TT.Arg) → T xs) → TT.Fun T
  | .nil, _, F => .up (F .nil)
  | .cons _, _, F => fun x => bind fun xs => F (.cons x xs)

theorem app_bind {TT : Tele.{u}} {T : TT.Arg → Type v} (F : (xs : TT.Arg) → T xs)
    (xs : TT.Arg) : app (bind F) xs = F xs := by
  induction TT with | nil => rfl | cons b ih => exact ih xs.1 _ xs.2

/-! ### Syntax helpers -/

/-- Convert standard `explicitBinders` into the corresponding binders of a `fun` expression. -/
private meta def explicitBindersToFunBinders (binders : TSyntax ``Lean.explicitBinders) :
    MacroM (Array (TSyntax ``Lean.Parser.Term.funBinder)) := do
  let mkBinder (x : Syntax) (ty? : Option Term) :
      TSyntax ``Lean.Parser.Term.funBinder :=
    ⟨Lean.Elab.Term.mkExplicitBinder ⟨x⟩ (ty?.getD (Lean.mkHole x))⟩
  let binders := binders.raw[0]
  if binders.getKind == ``Lean.unbracketedExplicitBinders then
    let ty? : Option Term := if binders[1].isNone then none else some ⟨binders[1][1]⟩
    return binders[0].getArgs.map fun binder => mkBinder binder[0] ty?
  else if binders.getArgs.all (·.getKind == ``Lean.bracketedExplicitBinders) then
    return binders.getArgs.flatMap fun binder =>
      binder[1].getArgs.map fun x => mkBinder x[0] (some ⟨binder[3]⟩)
  else
    Macro.throwError "unexpected explicit binder"

/-- Expand an optional binder group into a literal telescope. -/
meta def expandLiteral (binders? : Option (TSyntax ``Lean.explicitBinders)) : MacroM Term := do
  -- The universe of the empty telescope is not otherwise determined.
  let some binders := binders? | return ← `((Tele.nil : Tele.{0}))
  return ⟨← Lean.expandExplicitBinders ``Tele.cons binders (← `(Tele.nil))⟩

/-- Expand a body over the fields of a literal telescope into a function on its packed argument. -/
meta def expandFun (TT : Term) (binders? : Option (TSyntax ``Lean.explicitBinders))
    (body : Term) : MacroM Term := do
  let some binders := binders?
    | return ← `(Tele.app (TT := $TT) (ULift.up $body))
  let binders ← explicitBindersToFunBinders binders
  `(Tele.app (TT := $TT) (fun $binders:funBinder* => ULift.up $body))

/-- The number of fields in a literal telescope, or `none` if the expression is not one. -/
partial def literalArity? (e : Expr) : Option Nat :=
  if e.isConstOf ``Tele.nil then
    some 0
  else if e.isAppOfArity ``Tele.cons 2 then
    match e.appArg! with
    | .lam _ _ body _ => (literalArity? body).map (· + 1)
    | _ => none
  else
    none

/-- Descend through the binders and `ULift.up` of a function consumed by `Tele.app`. -/
private meta partial def withFunBinders {X : Type} (n : Nat) (names? : Option (Array Name))
    (acc : Array Ident) (k : Array Ident → DelabM X) : DelabM X := do
  if acc.size < n then
    unless (← getExpr).isLambda do failure
    match names? with
    | some names =>
      let x := names[acc.size]!
      withBindingBody x <| withFunBinders n names? (acc.push (mkIdent x)) k
    | none => withBindingBodyUnusedName fun x => withFunBinders n names? (acc.push ⟨x⟩) k
  else
    unless (← getExpr).isAppOfArity ``ULift.up 2 do failure
    withNaryArg 1 (k acc)

/-- Descend into a `Tele.app` function. The continuation runs under all binder scopes, allowing
another telescopic function to be nested. -/
private meta def withFunCore {X : Type} (n : Nat) (names? : Option (Array Name))
    (k : Array Ident → DelabM X) : DelabM X := do
  if let some names := names? then guard (names.size == n)
  unless (← getExpr).isAppOfArity ``Tele.app 3 do failure
  withNaryArg 2 (withFunBinders n names? #[] k)

/-- Descend into a `Tele.app` function, assigning fresh names to its telescope fields. -/
meta def withFun {X : Type} (n : Nat) (k : Array Ident → DelabM X) : DelabM X :=
  withFunCore n none k

/-- Descend into a `Tele.app` function, reusing `names` for its telescope fields. -/
meta def withFunUsing {X : Type} (n : Nat) (names : Array Name)
    (k : Array Ident → DelabM X) : DelabM X :=
  withFunCore n (some names) k

/-- Wrap a function on a packed telescope argument in `Tele.app ∘ Tele.bind`. -/
abbrev lam {TT : Tele.{u}} {T : TT.Arg → Type v} (F : (xs : TT.Arg) → T xs) :
    (xs : TT.Arg) → T xs := app (bind F)

/-- `λ.. x₁ … xₙ, body` binds packed telescope arguments, wrapping each lambda in
`Tele.app ∘ Tele.bind`. -/
macro:max "λ.." xs:explicitBinders ", " body:term : term => do
  return ⟨← expandExplicitBinders ``lam xs body⟩

/-- Delaborate nested `Tele.lam` expressions as `λ.. x …, ...`. -/
@[app_delab Iris.Std.Tele.lam]
meta def delabLam : Delab :=
  delabQuant 3 pure
    (fun x rest body => `(λ.. $x:ident $[$rest:ident]*, $body))
    (fun | `(λ.. $y:ident $[$ys:ident]*, $body) => some (y, ys, body) | _ => none)

/-- Collapse a non-dependent telescopic function into a single value, using `step` to introduce
one binder at a time. -/
def fold {B : Type v} (step : (A : Type u) → (A → B) → B) : {TT : Tele.{u}} → (TT -t> B) → B
  | .nil, f => ULift.down f
  | .cons _, f => step _ fun x => fold step (f x)

/-- Telescopic universal quantification at `Prop`. -/
def tforall : {TT : Tele.{u}} → (TT.Arg → Prop) → Prop
  | .nil,    Ψ => Ψ .nil
  | .cons _, Ψ => ∀ x, tforall fun xs => Ψ (.cons x xs)

/-- Telescopic existential quantification at `Prop`. -/
def texist : {TT : Tele.{u}} → (TT.Arg → Prop) → Prop
  | .nil,    Ψ => Ψ .nil
  | .cons _, Ψ => ∃ x, texist fun xs => Ψ (.cons x xs)

/-- Telescopic universal quantification. -/
macro "∀.." xs:explicitBinders ", " P:term : term => do
  return ⟨← expandExplicitBinders ``tforall xs P⟩

/-- Telescopic existential quantification. -/
macro "∃.." xs:explicitBinders ", " P:term : term => do
  return ⟨← expandExplicitBinders ``texist xs P⟩

/-- A delaborator for the telescopic universal quantifier. -/
@[app_delab Iris.Std.Tele.tforall]
meta def delabPropTforall : Delab :=
  delabQuant 2 pure
    (fun x rest body => `(∀.. $x:ident $[$rest:ident]*, $body))
    (fun | `(∀.. $y:ident $[$z:ident]*, $Ψ) => some (y, z, Ψ) | _ => none)

/-- A delaborator for the telescopic existential quantifier. -/
@[app_delab Iris.Std.Tele.texist]
meta def delabPropTexist : Delab := do
  delabQuant 2 pure
    (fun x rest body => `(∃.. $x:ident $[$rest:ident]*, $body))
    (fun | `(∃.. $y:ident $[$z:ident]*, $Ψ) => some (y, z, Ψ) | _ => none)

theorem tforall_forall {TT : Tele} (Ψ : TT.Arg → Prop) : tforall Ψ ↔ ∀ x, Ψ x := by
  induction TT with
  | nil =>
    constructor
    · exact fun h _ => h
    · exact fun h => h .nil
  | cons b ih =>
    constructor
    · exact fun h x => (ih x.fst _).mp (h x.fst) x.snd
    · exact fun h x => (ih x _).mpr fun xs => h ⟨x, xs⟩

theorem texist_exist {TT : Tele} (Ψ : TT.Arg → Prop) : texist Ψ ↔ ∃ x, Ψ x := by
  induction TT with
  | nil =>
    constructor
    · exact fun h => ⟨.nil, h⟩
    · exact fun ⟨_, h⟩ => h
  | cons b ih =>
    constructor
    · exact fun ⟨x, h⟩ => let ⟨xs, h⟩ := (ih x _).mp h; ⟨⟨x, xs⟩, h⟩
    · exact fun ⟨x, h⟩ => ⟨x.fst, (ih x.fst _).mpr ⟨x.snd, h⟩⟩

end Tele

end Iris.Std
