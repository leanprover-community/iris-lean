/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.HeapLang.ProofMode
public import Iris.HeapLang.TransfiniteDerived

/-! # Proof mode tactics for heap_lang in Transfinite Iris

This file ports the tactics of `theories/heap_lang/proofmode.v` of Transfinite Iris for the
weakest preconditions of Transfinite Iris: `wp`, `swp`, `rwp`, `rswp` (and the time-credit
weakest precondition `tcwp`, which is an abbreviation for `rwp`).

The tactics are generic: a goal `Δ ⊢ W e Φ` is handled whenever the partial application `W` (the
goal without its last two arguments, the expression and the postcondition) has an instance of
`HLWp W W'`, which provides the bind and pure-step rules; `W'` is the weakest precondition after a
program step (`wp` for `swp k`, `rwp` for `rswp k`). The value rule is `HLWpValue W`.

The tactics are prefixed with `t` (for transfinite): `twp_bind`, `twp_pure`, `twp_pures`,
`twp_rec`, `twp_let`, ..., `twp_value_head`, `twp_finish`, `twp_expr_simp`, `twp_apply` and
`twp_smart_apply`. They behave like their upstream counterparts `wp_*` in
`Iris.HeapLang.ProofMode`, except that `twp_value_head` produces the goal `Φ v` (no fancy update,
as in Transfinite Iris).
-/

namespace Iris.Transfinite

open Iris Iris.BI Iris.HeapLang ProgramLogic Language

section Classes

universe u v

variable {SI : Type v} [Iris.SIdx SI]
local stepindex SI

/-- The bind and pure-step rules of a heap_lang weakest precondition `W`, abstracted over the
expression and the postcondition. `W'` is the weakest precondition after a program step.

A pure step of `n` program steps is possible if `pureOk n`, and costs `laters n` laters. -/
public class HLWp {PROP : Type u} [BI PROP] (W : Exp → (Val → PROP) → PROP)
    (W' : outParam (Exp → (Val → PROP) → PROP)) where
  /-- Whether binding requires the focused expression not to be a value. -/
  bindNonVal : Bool
  bind (K : List ECtxItem) (e : Exp) (Φ : Val → PROP) :
    (bindNonVal = false ∨ ToVal.toVal e = none) →
    W e (fun v => W' (fill K (v : Exp)) Φ) ⊢ W (fill K e) Φ
  pureOk : Nat → Bool
  laters : Nat → Nat
  pure {φ : Prop} {n : Nat} {e₁ e₂ : Exp} (Φ : Val → PROP) :
    PureExec φ n e₁ e₂ → φ → pureOk n = true → ▷^[laters n] W' e₂ Φ ⊢ W e₁ Φ

/-- The value rule of a heap_lang weakest precondition `W`. -/
public class HLWpValue {PROP : Type u} [BI PROP] (W : Exp → (Val → PROP) → PROP) where
  value (v : Val) (Φ : Val → PROP) : Φ v ⊢ W (v : Exp) Φ

variable {GF : BundledGFunctors} {s : Stuckness} {E : CoPset}

public instance hlwp_wp [ι : IrisGS Exp GF] :
    HLWp (Iris.Transfinite.wp (ι := ι) s E) (Iris.Transfinite.wp (ι := ι) s E) where
  bindNonVal := false
  bind K _ _ _ := Iris.Transfinite.wp_bind (fill K)
  pureOk _ := true
  laters n := n
  pure _ h hφ _ := by haveI := h; exact Iris.Transfinite.wp_pure_step_later hφ

public instance hlwpValue_wp [ι : IrisGS Exp GF] :
    HLWpValue (Iris.Transfinite.wp (ι := ι) s E) where
  value v _ := Iris.Transfinite.wp_value v

public instance hlwp_swp [ι : IrisGS Exp GF] {k : Nat} :
    HLWp (swp (ι := ι) k s E) (Iris.Transfinite.wp (ι := ι) s E) where
  bindNonVal := true
  bind K _ _ h := swp_bind (fill K) (h.resolve_left (by decide))
  pureOk n := n != 0
  laters n := n
  pure {_ n _ _} _ h hφ hn := by
    obtain _ | n := n
    · cases hn
    · haveI := h; exact swp_pure_step_later k hφ

public instance hlwp_rwp {A : Type _} [src : Source GF A] [ι : RefIrisGS Exp GF] :
    HLWp (rwp (src := src) (ι := ι) s E) (rwp (src := src) (ι := ι) s E) where
  bindNonVal := false
  bind K _ _ _ := rwp_bind (fill K)
  pureOk _ := true
  laters _ := 0
  pure _ h hφ _ := by haveI := h; exact rwp_pure_step hφ

public instance hlwpValue_rwp {A : Type _} [src : Source GF A] [ι : RefIrisGS Exp GF] :
    HLWpValue (rwp (src := src) (ι := ι) s E) where
  value v _ := rwp_value' v

public instance hlwp_rswp {A : Type _} [src : Source GF A] [ι : RefIrisGS Exp GF] {k : Nat} :
    HLWp (rswp (src := src) (ι := ι) k s E) (rwp (src := src) (ι := ι) s E) where
  bindNonVal := true
  bind K _ _ h := rswp_bind (fill K) (h.resolve_left (by decide))
  pureOk n := n == 1
  laters _ := k
  pure {_ n _ _} _ h hφ hn := by
    obtain rfl : n = 1 := by simpa using hn
    haveI := h; exact rswp_pure_step_later hφ

/-! ## Tactic lemmas -/

variable {PROP : Type u} [BI PROP] {W W' : Exp → (Val → PROP) → PROP}

public theorem tac_twp_expr_simp {Δ : PROP} {e e' : Exp} {Φ : Val → PROP}
    (h : Δ ⊢ W e' Φ) (heq : e = e') : Δ ⊢ W e Φ := heq ▸ h

public theorem tac_twp_value [inst : HLWpValue W] {Δ : PROP} {v : Val} {Φ : Val → PROP}
    (h : Δ ⊢ Φ v) : Δ ⊢ W (v : Exp) Φ :=
  h.trans (inst.value v Φ)

public theorem tac_twp_bind [inst : HLWp W W'] {Δ : PROP} {K : List ECtxItem} {e : Exp}
    {Φ : Val → PROP} (he : inst.bindNonVal = false ∨ ToVal.toVal e = none)
    (h : Δ ⊢ W e (fun v => W' (fill K (v : Exp)) Φ)) : Δ ⊢ W (fill K e) Φ :=
  h.trans (inst.bind K e Φ he)

public theorem tac_twp_pure [inst : HLWp W W'] {Δ Δ' : PROP} {K : List ECtxItem} {e₁ e₂ : Exp}
    {φ : Prop} {n : Nat} {Φ : Val → PROP} (hexec : PureExec φ n e₁ e₂) (hφ : φ)
    (hn : inst.pureOk n = true) (hΔ : Δ ⊢ ▷^[inst.laters n] Δ')
    (h : Δ' ⊢ W' (fill K e₂) Φ) : Δ ⊢ W (fill K e₁) Φ :=
  hΔ.trans ((laterN_mono _ h).trans
    (inst.pure Φ (EctxLanguage.pureExec_fill (K := K) φ n hexec) hφ hn))

end Classes

end Iris.Transfinite

namespace Iris.ProofMode

open Lean hiding Expr
open Meta Elab Tactic Qq
open Iris.HeapLang Iris.BI Iris.Transfinite

/-- A goal `Δ ⊢ W e Φ` for a transfinite heap_lang weakest precondition `W`. -/
public structure TWpGoal where
  {u : Level}
  {prop : Q(Type u)}
  {vsi : Level}
  {si : Q(Type vsi)}
  {isi : Q(Iris.SIdx $si)}
  {bi : Q(@BI $si $isi $prop)}
  {ehyps : Q($prop)}
  hyps : Hyps bi ehyps
  W : Q(Exp → (Val → $prop) → $prop)
  e : Q(Exp)
  Φ : Q(Val → $prop)

/-- Split a goal `W e Φ` into `W`, `e` and `Φ`. -/
public meta def parseTWp? {u : Level} (prop : Q(Type u)) (goal : Q($prop)) :
    MetaM (Option (Q(Exp → (Val → $prop) → $prop) × Q(Exp) × Q(Val → $prop))) := do
  let goal ← instantiateMVars goal
  let args := goal.getAppArgs
  if args.size < 2 then return none
  let e := args[args.size - 2]!
  let Φ := args[args.size - 1]!
  unless ← isDefEq (← inferType e) q(Exp) do return none
  let W := mkAppN goal.getAppFn (args.extract 0 (args.size - 2))
  return some (W, e, Φ)

public meta def ProofModeM.runTacticTWp {α} (tacName : Name)
    (k : MVarId → TWpGoal → ProofModeM α) : TacticM α :=
  ProofModeM.runTactic tacName fun mvar {prop, bi, hyps, goal, ..} => do
    let some (W, e, Φ) ← parseTWp? prop goal
      | throwIPMError "The goal {goal} must be a transfinite weakest precondition"
    k mvar { hyps, W, e, Φ }

section
variable {u : Level} {prop : Q(Type u)} {vsi : Level} {si : Q(Type vsi)}
  {isi : Q(Iris.SIdx $si)} {bi : Q(@BI $si $isi $prop)}

/-- Find the weakest precondition `W'` after a step, i.e. an instance of `HLWp W W'`. -/
public meta def synthHLWp (W : Q(Exp → (Val → $prop) → $prop)) :
    ProofModeM ((W' : Q(Exp → (Val → $prop) → $prop)) × Q(@HLWp $si $isi $prop $bi $W $W')) := do
  let W' : Q(Exp → (Val → $prop) → $prop) ← mkFreshExprMVarQ q(Exp → (Val → $prop) → $prop)
  let some inst ← ProofModeM.trySynthInstanceQ q(@HLWp $si $isi $prop $bi $W $W')
    | throwIPMError "{W} is not a transfinite weakest precondition (no `HLWp` instance)"
  have W'' : Q(Exp → (Val → $prop) → $prop) := ← instantiateMVars W'
  have : $W'' =Q $W' := ⟨⟩
  return ⟨W'', inst⟩

public meta def iTWpValueHead {ehyps : Q($prop)} (hyps : Hyps bi ehyps)
    (W : Q(Exp → (Val → $prop) → $prop)) (e : Q(Exp)) (Φ : Q(Val → $prop)) :
    ProofModeM (Option Q($ehyps ⊢ $W $e $Φ)) := do
  let ~q(ProgramLogic.ToVal.ofVal $v) := e | return none
  let some inst ← ProofModeM.trySynthInstanceQ q(@HLWpValue $si $isi $prop $bi $W) | return none
  have goal : Q($prop) := Expr.headBeta q($Φ $v)
  have : $goal =Q $Φ $v := ⟨⟩
  let pf ← addBIGoal hyps goal
  return some q(tac_twp_value (inst := $inst) $pf)

public meta def iTWpFinish {ehyps : Q($prop)} (hyps : Hyps bi ehyps)
    (W : Q(Exp → (Val → $prop) → $prop)) (e : Q(Exp)) (Φ : Q(Val → $prop)) :
    ProofModeM Q($ehyps ⊢ $W $e $Φ) := do
  let ⟨e', pfeq⟩ ← iWpExprSimp e
  let nextPf ← (← iTWpValueHead hyps W e' Φ).getDM (addBIGoal hyps q($W $e' $Φ))
  return q(tac_twp_expr_simp $nextPf $pfeq)

/-- Bind the evaluation context `K` in the goal `W (K[e']) Φ`; `k` proves the new goal. -/
public meta def iTWpBindCore (ehyps : Q($prop))
    (W : Q(Exp → (Val → $prop) → $prop)) (e : Q(Exp)) (Φ : Q(Val → $prop))
    (K : Q(List ECtxItem)) (e' : Q(Exp)) (k : (A : Q($prop)) → ProofModeM Q($ehyps ⊢ $A)) :
    ProofModeM Q($ehyps ⊢ $W (ProgramLogic.fill $K $e') $Φ) := do
  match K with
  | ~q([]) => k q($W $e $Φ)
  | _ =>
    let ⟨W', inst⟩ ← synthHLWp (bi := bi) W
    let Φ' : Q(Val → $prop) ←
      Qq.withLocalDeclDQ `v q(Val) fun v => do
        mkLambdaFVars #[v] <| Expr.headBeta q($W' $(← HeapLang.fill K q(.ofVal $v)) $Φ)
    have _ : $Φ' =Q (fun v : Val => $W' (ProgramLogic.fill $K (v : Exp)) $Φ) := ⟨⟩
    -- the side condition `bindNonVal = false ∨ toVal e' = none`
    let he : Q(@HLWp.bindNonVal $si $isi $prop $bi $W $W' $inst = false ∨ ProgramLogic.ToVal.toVal $e' = none) ←
      if ← isDefEq q(@HLWp.bindNonVal $si $isi $prop $bi $W $W' $inst) q(false) then
        mkAppOptM ``Or.inl #[none, q(ProgramLogic.ToVal.toVal $e' = none), ← mkEqRefl q(false)]
      else if ← isDefEq q(ProgramLogic.ToVal.toVal $e') q((none : Option Val)) then
        mkAppOptM ``Or.inr #[q(@HLWp.bindNonVal $si $isi $prop $bi $W $W' $inst = false), none,
          ← mkEqRefl q((none : Option Val))]
      else
        throwIPMError "cannot bind a value: {e'}"
    let pf ← k q($W $e' $Φ')
    return q(tac_twp_bind (inst := $inst) $he $pf)

/-- Take a pure step in the goal `W e Φ`, as found by `findPureExec` in an evaluation context
of `e`. Returns the new context, weakest precondition `W'` and expression. -/
public meta def iTWpPure {ehyps : Q($prop)} (hyps : Hyps bi ehyps)
    (W : Q(Exp → (Val → $prop) → $prop)) (e : Q(Exp)) (Φ : Q(Val → $prop))
    (failOnUnsolved : Bool)
    (findPureExec : (e₁ : Q(Exp)) →
      ProofModeM ((φ : Q(Prop)) × (n : Q(Nat)) × (e₂ : Q(Exp)) ×
        Q(ProgramLogic.Language.PureExec $φ $n $e₁ $e₂))) :
    ProofModeM ((ehyps' : Q($prop)) × Hyps bi ehyps' ×
      (W' : Q(Exp → (Val → $prop) → $prop)) × (e' : Q(Exp)) ×
      Q(($ehyps' ⊢ $W' $e' $Φ) → $ehyps ⊢ $W $e $Φ)) := do
  let ⟨W', inst⟩ ← synthHLWp (bi := bi) W
  let some {result := ⟨φ, n, e₂, hexec⟩, K, e' := e₁, ..} ←
    findECtx (α := ((_ : Q(Prop)) × (_ : Q(Nat)) × (_ : Q(Exp)) × Lean.Expr)) e fun _ e₁ => do
      let r@⟨_, n, _, _⟩ ← findPureExec e₁
      -- check that the weakest precondition allows this pure step
      have n : Q(Nat) := n
      guard <| ← isDefEq q(@HLWp.pureOk $si $isi $prop $bi $W $W' $inst $n) q(true)
      return r
  | throwIPMError "Cannot find expression to evaluate"
  have hexec : Q(ProgramLogic.Language.PureExec $φ $n $e₁ $e₂) := hexec
  have hn : Q(@HLWp.pureOk $si $isi $prop $bi $W $W' $inst $n = true) := ← mkEqRefl q(true)
  have lat : Q(Nat) := ← Meta.reduce q(@HLWp.laters $si $isi $prop $bi $W $W' $inst $n)
  have : $lat =Q @HLWp.laters $si $isi $prop $bi $W $W' $inst $n := ⟨⟩
  let ⟨_, hyps', pf⟩ ← iModAction (bi1 := bi) hyps q(modality_laterN $lat)
  let ⟨inner, .up _⟩ ← HeapLang.fillQ K e₂
  let hφ ← iSolveSidecondition φ (failOnUnsolved := failOnUnsolved)
  return ⟨_, hyps', W', inner,
    q(fun nextPf => tac_twp_pure (inst := $inst) $hexec $hφ $hn $pf nextPf)⟩

end

elab "twp_value_head" : tactic =>
  ProofModeM.runTacticTWp `twp_value_head fun mvar { hyps, W, e, Φ, .. } => do
    let some pf ← iTWpValueHead hyps W e Φ
      | throwIPMError s!"the expression is not a value"
    mvar.assign pf

elab "twp_expr_simp" : tactic =>
  ProofModeM.runTacticTWp `twp_expr_simp fun mvar { hyps, W, e, Φ, .. } => do
    let ⟨e', pfeq⟩ ← iWpExprSimp e
    let pf ← addBIGoal hyps q($W $e' $Φ)
    mvar.assign q(tac_twp_expr_simp $pf $pfeq)

elab "twp_finish" : tactic =>
  ProofModeM.runTacticTWp `twp_finish fun mvar { hyps, W, e, Φ, .. } => do
    mvar.assign (← iTWpFinish hyps W e Φ)

elab "twp_bind" colGt ppSpace focus:hl_exp:10 : tactic =>
  ProofModeM.runTacticTWp `twp_bind fun mvar { bi, ehyps, hyps, W, e, Φ, .. } => do
    let focus ← elabTermEnsuringTypeQ (← `(hl($focus))) q(HeapLang.Exp)
    let some {K, e', ..} ← findECtx e fun _ e => do
      guard <| ← isDefEq e focus
    | throwIPMError s!"Cannot unify {← ppExpr focus} with any possible evaluation context"
    mvar.assign <| ← iTWpBindCore (bi := bi) ehyps W e Φ K e' (addBIGoal hyps)

elab "twp_pure" failOnUnsolved:("+!failOnUnsolved")? colGt ppSpace focus:hl_exp:10 : tactic =>
  ProofModeM.runTacticTWp `twp_pure fun mvar { hyps, W, e, Φ, .. } => do
    let focus ← elabTermEnsuringTypeQ (← `(hl($focus))) q(HeapLang.Exp)
    let ⟨_, hyps', W', e', pf⟩ ← iTWpPure hyps W e Φ failOnUnsolved.isSome fun e₁ => do
      guard <| ← isDefEq e₁ focus
      findAnyPureExec e₁
    let pf' ← iTWpFinish hyps' W' e' Φ
    mvar.assign <| q($pf $pf')

macro "twp_pure" : tactic => `(tactic| twp_pure _)
macro "twp_pure" "+!failOnUnsolved" : tactic => `(tactic| twp_pure +!failOnUnsolved _)

/-- Reduce all pure redexes at the head of the transfinite weakest precondition, then simplify
the resulting expression and strip the weakest precondition if it has become a value. -/
macro "twp_pures" : tactic =>
  `(tactic| first
    | (twp_pure +!failOnUnsolved; repeat twp_pure +!failOnUnsolved)
    | twp_finish)

/-- Beta-reduce the innermost application, unfolding a head hidden behind a definition. -/
elab "twp_rec" : tactic =>
  ProofModeM.runTacticTWp `twp_rec fun mvar { hyps, W, e, Φ, .. } => do
    let ⟨_, hyps', W', e', pf⟩ ← iTWpPure hyps W e Φ (failOnUnsolved := false) fun e₁ => do
      let ~q(Exp.app (Exp.ofVal $f) (Exp.ofVal $a)) := e₁ | failure
      let f' : Q(Val) ← whnf f
      let ~q(Val.rec_ $fb $xb $body) := f' | failure
      have : $f' =Q $f := ⟨⟩
      let e₂ := q(Exp.subst $xb $a (Exp.subst $fb $f $body))
      return ⟨_, _, e₂, q(instPureExecBeta)⟩
    let pf' ← iTWpFinish hyps' W' e' Φ
    mvar.assign <| q($pf $pf')

macro "twp_if" : tactic => `(tactic | twp_pure (if _ then _ else _))
macro "twp_if_true" : tactic => `(tactic | twp_pure (if #true then _ else _))
macro "twp_if_false" : tactic => `(tactic | twp_pure (if #false then _ else _))
macro "twp_unop" : tactic => `(tactic | twp_pure (&(Exp.unop _ _)))
macro "twp_binop" : tactic => `(tactic | twp_pure (&(Exp.binop _ _ _)))
macro "twp_op" : tactic => `(tactic | first | twp_unop | twp_binop)
macro "twp_lam" : tactic => `(tactic | twp_rec)
macro "twp_let" : tactic => `(tactic | (twp_pure (rec _ &(.named _) := _); twp_pure (_ _)))
macro "twp_seq" : tactic => `(tactic | (twp_pure (rec _ _ := _); twp_pure (_ _)))
macro "twp_proj" : tactic => `(tactic | first | twp_pure (fst(_)) | twp_pure (snd(_)))
macro "twp_case" : tactic => `(tactic | twp_pure (&(Exp.case _ _ _)))
macro "twp_inj" : tactic => `(tactic | first | twp_pure (injl(_)) | twp_pure (injr(_)))
macro "twp_pair" : tactic => `(tactic | twp_pure ((_, _)))
macro "twp_closure" : tactic => `(tactic | twp_pure (rec &_ &_ := _))
macro "twp_match" : tactic => `(tactic | (twp_case; twp_closure; twp_pure (_ _)))

/-! ## The `twp_apply` tactics -/

/-- Indicates whether `twp_apply` or `twp_smart_apply` is used. -/
inductive TWpApplyKind where
  | apply
  | smartApply

meta partial def iTWpApplyCore {u : Level} {prop : Q(Type u)} {vsi : Level} {si : Q(Type vsi)}
    {isi : Q(Iris.SIdx $si)} {bi : Q(@BI $si $isi $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (W : Q(Exp → (Val → $prop) → $prop)) (e : Q(Exp))
    (Φ : Q(Val → $prop)) (pmt : PMTerm) (wpApplyKind : TWpApplyKind) :
    ProofModeM Q($ehyps ⊢ $W $e $Φ) := do
  let ⟨_, hypsP, p, A, posePf⟩ ← iHave hyps q($W $e $Φ) pmt true
  let lemIVar ← mkFreshIVarId (isTrue p)
  let ⟨ehyps0, hyps0, addPf⟩ := Hyps.add bi .anonymous lemIVar p A hypsP
  -- the current state: context, weakest precondition, expression and proof prefix
  let mut st : (ehypsC : Q($prop)) × Hyps bi ehypsC × (WC : Q(Exp → (Val → $prop) → $prop)) ×
      (eC : Q(Exp)) × Q(($ehypsC ⊢ $WC $eC $Φ) → $ehyps ⊢ $W $e $Φ) :=
    ⟨ehyps0, hyps0, W, e, q(fun pf => $posePf ($(addPf).mp.trans pf))⟩
  let failed ← addMessageContext m!"cannot apply {A}"
  repeat
    let ⟨_, hypsC, WC, eC, prefixPf⟩ := st
    let ⟨ehypsR, hypsR, _, A', p', _, remPf⟩ := Hyps.remove (rp := true) hypsC lemIVar
    let applied ←
      findECtx (α := Q($ehypsR ∗ □?$p' $A' ⊢ $WC $eC $Φ)) eC fun K e' => do
        iTWpBindCore (bi := bi) _ WC eC Φ K e' (iApply hypsR p' A' ·)
    if let some {result := pf, ..} := applied then
      return q($prefixPf <| $(remPf).mp.trans $pf)
    match wpApplyKind with
    | .apply => throwIPMError failed
    | .smartApply =>
      try
        let ⟨_, hypsN, WN, eN, purePf⟩ ←
          iTWpPure hypsC WC eC Φ (failOnUnsolved := true) findAnyPureExec
        let ⟨eN', pfeq⟩ ← iWpExprSimp eN
        st := ⟨_, hypsN, WN, eN', q(fun pf => $prefixPf ($purePf (tac_twp_expr_simp pf $pfeq)))⟩
      catch err =>
        if err.isInterrupt || err.isMaxHeartbeat then throw err
        throwIPMError failed

meta def twpApplyRaw (tacName : Name) (wpApplyKind : TWpApplyKind) (pmt : TSyntax `pmTerm) :
    TacticM Unit := do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  ProofModeM.runTacticTWp tacName fun mvar { hyps, W, e, Φ, .. } => do
    mvar.assign (← iTWpApplyCore hyps W e Φ pmt wpApplyKind)

elab "twp_apply_raw" colGt pmt:pmTerm : tactic =>
  twpApplyRaw `twp_apply .apply pmt
elab "twp_smart_apply_raw" colGt pmt:pmTerm : tactic =>
  twpApplyRaw `twp_smart_apply .smartApply pmt
/-- Strip a leading `▷` and simplify expressions in the goals an application produced. -/
macro "twp_apply_post" : tactic => `(tactic| ((try inext) <;> (try twp_expr_simp)))

/-- `twp_apply lem` is `wp_apply lem` for the transfinite weakest preconditions. -/
syntax (name := twpApply) "twp_apply " colGt pmTerm
  (" with" (colGt ppSpace introPat)+)? : tactic

macro_rules
  | `(tactic| twp_apply $pmt:pmTerm $[with $pats*]?) => do
    let t : TSyntax `tactic ←
      if let some pats := pats then
        `(tactic| focusLastIrisGoal (iintro $pats*))
      else
        `(tactic| skip)
    `(tactic| focus (((twp_apply_raw $pmt) <;> twp_apply_post); $t:tactic))

/-- `twp_smart_apply lem` is `wp_smart_apply lem` for the transfinite weakest preconditions. -/
syntax (name := twpSmartApply) "twp_smart_apply " colGt pmTerm
  (" with" (colGt ppSpace introPat)+)? : tactic

macro_rules
  | `(tactic| twp_smart_apply $pmt:pmTerm $[with $pats*]?) => do
    let t : TSyntax `tactic ←
      if let some pats := pats then
        `(tactic| focusLastIrisGoal (iintro $pats*))
      else
        `(tactic| skip)
    `(tactic| focus (((twp_smart_apply_raw $pmt) <;> twp_apply_post); $t:tactic))

end Iris.ProofMode
