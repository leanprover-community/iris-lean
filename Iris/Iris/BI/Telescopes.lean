/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.BI.DerivedLaws
public import Iris.BI.DerivedLawsLater
public import Iris.BI.Extensions
public import Iris.Std.Telescopes
public meta import Iris.Std.DelabRule
public meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris.BI
open Iris.Std Lean PrettyPrinter Delaborator

/-- Telescopic universal quantification: quantify over every binder of the telescope `TT`. -/
@[rocq_alias bi_tforall]
def tforall [BI PROP] {TT : Tele} (Ψ : TT.Arg → PROP) : PROP :=
  Tele.fold (fun _ => BIBase.forall) (Tele.bind Ψ)

/-- Telescopic existential quantification: quantify over every binder of the telescope `TT`. -/
@[rocq_alias bi_texist]
def texist [BI PROP] {TT : Tele} (Ψ : TT.Arg → PROP) : PROP :=
  Tele.fold (fun _ => BIBase.exists) (Tele.bind Ψ)

/-- Telescopic universal quantification. -/
macro "∀.." xs:explicitBinders ", " P:term : term => do
  return ⟨← expandExplicitBinders ``tforall xs P⟩

/-- Telescopic existential quantification. -/
macro "∃.." xs:explicitBinders ", " P:term : term => do
  return ⟨← expandExplicitBinders ``texist xs P⟩

macro_rules
  | `(iprop(∀.. $xs, $Ψ)) => do expandExplicitBinders ``tforall xs (← ``(iprop($Ψ)))
  | `(iprop(∃.. $xs, $Ψ)) => do expandExplicitBinders ``texist xs (← ``(iprop($Ψ)))

/-- A delaborator for the telescopic universal quantifier. -/
@[app_delab Iris.BI.tforall]
meta def delabBITforall : Delab := do
  let e ← SubExpr.getExpr
  if e.appArg!.isLambda then
    -- Print nested applications (e.g. `tforall (fun x => tforall (fun y => Ψ))` as `∀.. x y, Ψ x y`)
    SubExpr.withAppArg <| withBindingBodyUnusedName fun x => do
      let x : TSyntax `ident := ⟨x⟩
      match ← unpackIprop (← delab) with
      | `(∀.. $y:ident $[$z:ident]*, $Ψ) =>
        `(iprop(∀.. $x:ident $y:ident $[$z:ident]*, $Ψ))
      | body => `(iprop(∀.. $x:ident, $body))
  else
    -- Print `tforall Ψ` as `∀.. x, Ψ x`
    let Ψ := e.appArg!
    let dom := (← Meta.inferType Ψ).bindingDomain!
    -- Rename the binder if `Ψ` already refers a binder of the same name to avoid capture
    let n ← getUnusedName `x Ψ
    Meta.withLocalDeclD n dom fun _ => do
      let f ← SubExpr.withAppArg delab
      let x := mkIdent n
      `(iprop(∀.. $x:ident, $f $x))

/-- A delaborator for the telescopic existential quantifier. -/
@[app_delab Iris.BI.texist]
meta def delabBITexist : Delab := do
  let e ← SubExpr.getExpr
  if e.appArg!.isLambda then
    -- Print nested applications (e.g. `texist (fun x => texist (fun y => Ψ))` as `∃.. x y, Ψ x y`)
    SubExpr.withAppArg <| withBindingBodyUnusedName fun x => do
      let x : TSyntax `ident := ⟨x⟩
      match ← unpackIprop (← delab) with
      | `(∃.. $y:ident $[$z:ident]*, $Ψ) =>
        `(iprop(∃.. $x:ident $y:ident $[$z:ident]*, $Ψ))
      | body => `(iprop(∃.. $x:ident, $body))
  else
    -- Print `texist Ψ` as `∃.. x, Ψ x`
    let Ψ := e.appArg!
    let dom := (← Meta.inferType Ψ).bindingDomain!
    -- Rename the binder if `Ψ` already refers a binder of the same name to avoid capture
    let n ← getUnusedName `x Ψ
    Meta.withLocalDeclD n dom fun _ => do
      let f ← SubExpr.withAppArg delab
      let x := mkIdent n
      `(iprop(∃.. $x:ident, $f $x))

section Telescopes
variable [BI PROP] {TT : Tele}

@[simp] theorem tforall_nil (Ψ : Tele.Arg .nil → PROP) : tforall Ψ = Ψ .nil := rfl

@[simp] theorem tforall_cons {b : X → Tele} (Ψ : (Tele.cons b).Arg → PROP) :
    tforall Ψ = iprop(∀ x, tforall fun xs => Ψ (.cons x xs)) := rfl

@[simp] theorem texist_nil (Ψ : Tele.Arg .nil → PROP) : texist Ψ = Ψ .nil := rfl

@[simp] theorem texist_cons {b : X → Tele} (Ψ : (Tele.cons b).Arg → PROP) :
    texist Ψ = iprop(∃ x, texist fun xs => Ψ (.cons x xs)) := rfl

@[rocq_alias bi_tforall_forall]
theorem tforall_forall (Ψ : TT.Arg → PROP) : tforall Ψ ⊣⊢ ∀ x, Ψ x := by
  induction TT with
  | nil =>
    rw [tforall_nil]
    exact ⟨forall_intro fun _ => .rfl, forall_elim Tele.Arg.nil⟩
  | cons b ih =>
    rw [tforall_cons]
    constructor
    · refine forall_intro fun (.cons x xs) => ?_
      exact (forall_elim x).trans ((ih x _).mp.trans (forall_elim xs))
    · refine forall_intro fun x => ?_
      refine .trans ?_ (ih x _).mpr
      exact forall_intro fun ys => forall_elim (Ψ := Ψ) (.cons x ys)

@[rocq_alias bi_texist_exist]
theorem texist_exist (Ψ : TT.Arg → PROP) : texist Ψ ⊣⊢ ∃ x, Ψ x := by
  induction TT with
  | nil =>
    rw [texist_nil]
    exact ⟨exists_intro Tele.Arg.nil, exists_elim fun _ => .rfl⟩
  | cons b ih =>
    rw [texist_cons]
    constructor
    · refine exists_elim fun x => (ih x _).mp.trans ?_
      exact exists_elim fun ys => exists_intro (Ψ := Ψ) (.cons x ys)
    · refine exists_elim fun (.cons x xs) => ?_
      refine .trans ?_ (exists_intro x)
      exact (exists_intro (Ψ := fun ys => Ψ (.cons x ys)) xs).trans (ih x _).mpr

@[rocq_alias bi_tforall_ne]
theorem tforall_ne {Φ Ψ : TT.Arg → PROP} (h : ∀ x, Φ x ≡{n}≡ Ψ x) :
    tforall Φ ≡{n}≡ tforall Ψ := by
  rw [(tforall_forall Φ).to_eq, (tforall_forall Ψ).to_eq]
  exact forall_ne h

theorem tforall_congr {Φ Ψ : TT.Arg → PROP} (h : ∀ x, Φ x ⊣⊢ Ψ x) :
    tforall Φ ⊣⊢ tforall Ψ :=
  calc tforall Φ
    _ ⊣⊢ ∀ x, Φ x := tforall_forall Φ
    _ ⊣⊢ ∀ x, Ψ x := forall_congr h
    _ ⊣⊢ tforall Ψ := (tforall_forall Ψ).symm

#rocq_ignore bi_tforall_proper "Use `tforall_congr`."

@[rocq_alias bi_texist_ne]
theorem texist_ne {Φ Ψ : TT.Arg → PROP} (h : ∀ x, Φ x ≡{n}≡ Ψ x) :
    texist Φ ≡{n}≡ texist Ψ := by
  rw [(texist_exist Φ).to_eq, (texist_exist Ψ).to_eq]
  exact exists_ne h

theorem texist_congr {Φ Ψ : TT.Arg → PROP} (h : ∀ x, Φ x ⊣⊢ Ψ x) :
    texist Φ ⊣⊢ texist Ψ :=
  calc texist Φ
    _ ⊣⊢ ∃ x, Φ x := texist_exist Φ
    _ ⊣⊢ ∃ x, Ψ x := exists_congr h
    _ ⊣⊢ texist Ψ := (texist_exist Ψ).symm

#rocq_ignore bi_texist_proper "Use `texist_congr`."

@[rocq_alias bi_tforall_absorbing]
instance tforall_absorbing (Ψ : TT.Arg → PROP) [∀ x, Absorbing (Ψ x)] :
    Absorbing (∀.. x, Ψ x) := by
  rw [(tforall_forall Ψ).to_eq]
  infer_instance

@[rocq_alias bi_tforall_persistent]
instance tforall_persistent [BIPersistentlyForall PROP] (Ψ : TT.Arg → PROP)
    [∀ x, Persistent (Ψ x)] : Persistent (∀.. x, Ψ x) := by
  rw [(tforall_forall Ψ).to_eq]
  infer_instance

@[rocq_alias bi_texist_affine]
instance texist_affine (Ψ : TT.Arg → PROP) [∀ x, Affine (Ψ x)] : Affine (∃.. x, Ψ x) := by
  rw [(texist_exist Ψ).to_eq]
  infer_instance

@[rocq_alias bi_texist_absorbing]
instance texist_absorbing (Ψ : TT.Arg → PROP) [∀ x, Absorbing (Ψ x)] :
    Absorbing (∃.. x, Ψ x) := by
  rw [(texist_exist Ψ).to_eq]
  infer_instance

@[rocq_alias bi_texist_persistent]
instance texist_persistent (Ψ : TT.Arg → PROP) [∀ x, Persistent (Ψ x)] :
    Persistent (∃.. x, Ψ x) := by
  rw [(texist_exist Ψ).to_eq]
  infer_instance

@[rocq_alias bi_tforall_timeless]
instance tforall_timeless (Ψ : TT.Arg → PROP) [∀ x, Timeless (Ψ x)] :
    Timeless (∀.. x, Ψ x) := by
  rw [(tforall_forall Ψ).to_eq]
  infer_instance

@[rocq_alias bi_texist_timeless]
instance texist_timeless (Ψ : TT.Arg → PROP) [∀ x, Timeless (Ψ x)] :
    Timeless (∃.. x, Ψ x) := by
  rw [(texist_exist Ψ).to_eq]
  infer_instance

end Telescopes

end Iris.BI
