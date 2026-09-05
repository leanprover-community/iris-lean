/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Vistrup, Markus de Medeiros
-/

module

public import Iris.HeapLang.Semantics
public import Iris.HeapLang.Instances
public import Iris.HeapLang.Notation
public import Iris.ProgramLogic.EctxiLanguage
public import Iris.ProgramLogic.Adequacy
public import Iris.Std.PartialMap

@[expose] public section
namespace Iris.HeapLang

open _root_.Iris.Std Iris.ProgramLogic Iris.ProgramLogic.Language Iris.ProgramLogic.PrimStep
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage
open FromMathlib
open Language.Notation EctxLanguage.Notation

/-! ## Erasure functions -/

@[rocq_alias heap_lang.erase_base_lit]
def eraseBaseLit : BaseLit → BaseLit
  | .prophecy _ => .poison
  | l => l

/-- Erasure of `Resolve` translates it into a projection out of a triple. -/
@[rocq_alias heap_lang.erase_resolve]
def eraseResolve (e0 e1 e2 : Exp) : Exp :=
  hl(fst(fst(((&e0, &e1), &e2))))

/-- The erased form of `NewProph` — a stuck-free expression that reduces to `#.poison`. -/
@[rocq_alias heap_lang.erased_new_proph]
def erasedNewProph : Exp :=
  hl(v(λ _, #.poison) #())

mutual
  @[rocq_alias heap_lang.erase_expr]
  def eraseExpr : Exp → Exp
    | .val v => .val (eraseVal v)
    | .var x => .var x
    | .rec_ f x e => .rec_ f x (eraseExpr e)
    | .app e1 e2 => .app (eraseExpr e1) (eraseExpr e2)
    | .unop op e => .unop op (eraseExpr e)
    | .binop op e1 e2 => .binop op (eraseExpr e1) (eraseExpr e2)
    | .if e0 e1 e2 => .if (eraseExpr e0) (eraseExpr e1) (eraseExpr e2)
    | .pair e1 e2 => .pair (eraseExpr e1) (eraseExpr e2)
    | .fst e => .fst (eraseExpr e)
    | .snd e => .snd (eraseExpr e)
    | .injL e => .injL (eraseExpr e)
    | .injR e => .injR (eraseExpr e)
    | .case e0 e1 e2 => .case (eraseExpr e0) (eraseExpr e1) (eraseExpr e2)
    | .fork e => .fork (eraseExpr e)
    | .allocN e1 e2 => .allocN (eraseExpr e1) (eraseExpr e2)
    | .free e => .free (eraseExpr e)
    | .load e => .load (eraseExpr e)
    | .xchg e1 e2 => .xchg (eraseExpr e1) (eraseExpr e2)
    | .store e1 e2 => .store (eraseExpr e1) (eraseExpr e2)
    | .cmpXchg e0 e1 e2 => .cmpXchg (eraseExpr e0) (eraseExpr e1) (eraseExpr e2)
    | .faa e1 e2 => .faa (eraseExpr e1) (eraseExpr e2)
    | .newProph => erasedNewProph
    | .resolve e0 e1 e2 => eraseResolve (eraseExpr e0) (eraseExpr e1) (eraseExpr e2)
  @[rocq_alias heap_lang.erase_val]
  def eraseVal : Val → Val
    | .lit l => .lit (eraseBaseLit l)
    | .rec_ f x e => .rec_ f x (eraseExpr e)
    | .pair v1 v2 => .pair (eraseVal v1) (eraseVal v2)
    | .injL v => .injL (eraseVal v)
    | .injR v => .injR (eraseVal v)
end

@[rocq_alias heap_lang.erase_ectx_item]
def eraseECtxItem : ECtxItem → List ECtxItem
  | .appL v2          => [.appL (eraseVal v2)]
  | .appR e1          => [.appR (eraseExpr e1)]
  | .unOp op          => [.unOp op]
  | .binOpL op v2     => [.binOpL op (eraseVal v2)]
  | .binOpR op e1     => [.binOpR op (eraseExpr e1)]
  | .if e1 e2         => [.if (eraseExpr e1) (eraseExpr e2)]
  | .pairL v2         => [.pairL (eraseVal v2)]
  | .pairR e1         => [.pairR (eraseExpr e1)]
  | .fst              => [.fst]
  | .snd              => [.snd]
  | .injL             => [.injL]
  | .injR             => [.injR]
  | .case e1 e2       => [.case (eraseExpr e1) (eraseExpr e2)]
  | .allocNL v2       => [.allocNL (eraseVal v2)]
  | .allocNR e1       => [.allocNR (eraseExpr e1)]
  | .free             => [.free]
  | .load             => [.load]
  | .storeL v2        => [.storeL (eraseVal v2)]
  | .storeR e1        => [.storeR (eraseExpr e1)]
  | .xchgL v2         => [.xchgL (eraseVal v2)]
  | .xchgR e1         => [.xchgR (eraseExpr e1)]
  | .cmpXchgL v1 v2   => [.cmpXchgL (eraseVal v1) (eraseVal v2)]
  | .cmpXchgM e0 v2   => [.cmpXchgM (eraseExpr e0) (eraseVal v2)]
  | .cmpXchgR e0 e1   => [.cmpXchgR (eraseExpr e0) (eraseExpr e1)]
  | .faaL v2          => [.faaL (eraseVal v2)]
  | .faaR e1          => [.faaR (eraseExpr e1)]
  | .resolveL K v1 v2 => eraseECtxItem K ++ [.pairL (eraseVal v1), .pairL (eraseVal v2), .fst, .fst]
  | .resolveM e0 v2   => [.pairR (eraseExpr e0), .pairL (eraseVal v2), .fst, .fst]
  | .resolveR e0 e1   => [.pairR (.pair (eraseExpr e0) (eraseExpr e1)), .fst, .fst]

@[rocq_alias heap_lang.erase_ectx]
def eraseECtx (K : List ECtxItem) : List ECtxItem := K.flatMap eraseECtxItem

@[rocq_alias heap_lang.erase_tp]
def eraseTp (tp : List Exp) : List Exp := tp.map eraseExpr

@[rocq_alias heap_lang.erase_heap]
def eraseHeap (h : HeapF (Option Val)) : HeapF (Option Val) :=
  Iris.Std.PartialMap.map (fun (ov : Option Val) => eraseVal <$> ov) h

@[rocq_alias heap_lang.erase_state]
def eraseState (σ : State) : State := { heap := eraseHeap σ.heap, usedProphId := ∅ }

@[rocq_alias heap_lang.erase_cfg]
def eraseCfg (ρ : List Exp × State) : List Exp × State := (eraseTp ρ.1, eraseState ρ.2)


/-- `erase_simp` unfolds the erasure functions at a location -/
local macro "erase_simp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp
      [eraseExpr, eraseVal, eraseBaseLit, erasedNewProph, eraseResolve,
       eraseECtx, eraseECtxItem, ECtxItem.fill] $[$loc]?)

@[simp] theorem eraseExpr_val (v : Val) : eraseExpr (.val v) = .val (eraseVal v) := rfl

@[simp] theorem eraseExpr_ofVal (v : Val) : eraseExpr (.ofVal v) = .ofVal (eraseVal v) := rfl

@[rocq_alias heap_lang.erase_ectx_app]
theorem eraseECtx_append (K K' : List ECtxItem) :
    eraseECtx (K ++ K') = eraseECtx K ++ eraseECtx K' := by
  simp [eraseECtx, List.flatMap_append]

@[rocq_alias heap_lang.erase_not_val]
theorem toVal_erase_none {e : Exp} (h : toVal e = none) : toVal (eraseExpr e) = none := by
  cases e <;> simp_all [ToVal.toVal, eraseExpr, erasedNewProph, eraseResolve]

private theorem eraseExpr_eq_val {e : Exp} {v : Val}
    (h : eraseExpr e = hl(v(&v))) : ∃ w, e = hl(v(&w)) ∧ eraseVal w = v := by
  cases e <;> erase_simp at h <;> cases h
  exact ⟨_, rfl, rfl⟩

@[rocq_alias heap_lang.erase_to_val]
theorem toVal_erase_some {e : Exp} {v : Val} (h : toVal (eraseExpr e) = some v) :
    ∃ v', toVal e = some v' ∧ eraseVal v' = v := by
  obtain ⟨w, rfl, hew⟩ := eraseExpr_eq_val (coe_of_toVal_eq_some h).symm
  exact ⟨w, rfl, hew⟩

@[rocq_alias heap_lang.erase_expr_subst]
theorem eraseExpr_substStr (x : String) (v : Val) (e : Exp) :
    eraseExpr (e.substStr x v) = (eraseExpr e).substStr x (eraseVal v) := by
  induction e using Exp.rec (motive_2 := fun _ => True) with
  | val w => rfl
  | var x' => by_cases h : x == x' <;> simp [Exp.substStr, eraseExpr, h]
  | rec_ f x' e ih =>
    simp only [Exp.substStr, eraseExpr]
    by_cases h : .named x != f && .named x != x' <;> simp [h, ih]
  | resolve _ _ _ ih0 ih1 ih2 => simp [Exp.substStr, eraseExpr, eraseResolve, ih0, ih1, ih2]
  | newProph => rfl
  | _ => simp_all [Exp.substStr, eraseExpr]

@[rocq_alias heap_lang.erase_expr_subst']
theorem eraseExpr_subst (x : Binder) (v : Val) (e : Exp) :
    eraseExpr (e.subst x v) = (eraseExpr e).subst x (eraseVal v) := by
  cases x with
  | anon => simp [Exp.subst]
  | named s => exact eraseExpr_substStr s v e

#rocq_ignore heap_lang.erase_val_subst'
  "`Exp.substStr` leaves `.val w` untouched, so this is the `| val w => rfl` case of `eraseExpr_substStr`."

/-! ## Erasure and evaluation contexts -/

theorem fill_snoc (K : List ECtxItem) (Ki : ECtxItem) (e : Exp) :
    fill (K ++ [Ki]) e = Ki.fill (fill K e) := by
  simp [fill_append, fill_cons, fill_nil, fillItem]

theorem eraseECtxItem_fill (Ki : ECtxItem) (e : Exp) :
    eraseExpr (Ki.fill e) = fill (eraseECtxItem Ki) (eraseExpr e) := by
  induction Ki generalizing e <;>
    simp_all [ECtxItem.fill, eraseECtxItem, eraseExpr, eraseResolve, fill_append, fillItem]

@[rocq_alias heap_lang.erase_ectx_expr]
theorem eraseECtx_fill (K : List ECtxItem) (e : Exp) :
    eraseExpr (fill K e) = fill (eraseECtx K) (eraseExpr e) := by
  induction K using List.reverseRec with
  | nil => simp [eraseECtx]
  | append_singleton Ks Ki ih =>
    rw [fill_snoc, eraseECtxItem_fill, eraseECtx_append, fill_append, ih]
    simp [eraseECtx]

/-! ## Erasure and comparison safety -/

@[simp] theorem eraseBaseLit_isUnboxed (l : BaseLit) :
    (eraseBaseLit l).isUnboxed = l.isUnboxed := by
  cases l <;> rfl

@[rocq_alias heap_lang.val_is_unboxed_erased, simp]
theorem eraseVal_isUnboxed (v : Val) : (eraseVal v).isUnboxed = v.isUnboxed := by
  cases v <;> try rfl
  all_goals (rename_i w; cases w <;> simp [eraseVal, Val.isUnboxed])

@[rocq_alias heap_lang.vals_compare_safe_erase, simp]
theorem eraseVal_compareSafe (v1 v2 : Val) :
    (eraseVal v1).compareSafe (eraseVal v2) = v1.compareSafe v2 := by
  simp [Val.compareSafe]

private theorem eraseBaseLit_inj_of_unboxed {l1 l2 : BaseLit}
    (h : l1.isUnboxed = true ∨ l2.isUnboxed = true)
    (heq : eraseBaseLit l1 = eraseBaseLit l2) : l1 = l2 := by
  cases l1 <;> cases l2 <;> simp_all [eraseBaseLit, BaseLit.isUnboxed]

/-- Comparison-safe erased values are equal iff the originals are.  This is the
key lemma for handling `CmpXchg` and the `eq` binary operation. -/
@[rocq_alias heap_lang.erase_val_inj_iff]
theorem eraseVal_inj_iff {v1 v2 : Val} (h : v1.compareSafe v2 = true) :
    eraseVal v1 = eraseVal v2 ↔ v1 = v2 := by
  refine ⟨fun heq => ?_, congrArg _⟩
  simp only [Val.compareSafe, Bool.or_eq_true] at h
  cases v1 <;> cases v2 <;> simp_all [Val.isUnboxed, eraseVal] <;>
    first
      | exact eraseBaseLit_inj_of_unboxed h heq
      | (rename_i w1 w2
         cases w1 <;> cases w2 <;> simp_all [eraseVal]
         exact eraseBaseLit_inj_of_unboxed h heq)

/-! ## Erasure and operator evaluation -/

@[rocq_alias heap_lang.un_op_eval_erase]
theorem UnOp.eval_erase {op : UnOp} {v v' : Val} :
    op.eval (eraseVal v) = some v' ↔
      ∃ w, op.eval v = some w ∧ eraseVal w = v' := by
  cases op <;> cases v <;>
    first
      | (rename_i l; cases l <;> simp [UnOp.eval, eraseVal, eraseBaseLit])
      | simp [UnOp.eval, eraseVal, eraseBaseLit]

/-- Helper: `.eq` is the only `BinOp` that depends on comparison safety. -/
private theorem BinOp.eq_eval_erase {v1 v2 v' : Val} :
    BinOp.eval .eq (eraseVal v1) (eraseVal v2) = some v' ↔
      ∃ w, BinOp.eval .eq v1 v2 = some w ∧ eraseVal w = v' := by
  simp only [BinOp.eval]
  by_cases h : v1.compareSafe v2 = true
  · have hbeq : (eraseVal v1 == eraseVal v2) = (v1 == v2) :=
      decide_eq_decide.mpr (eraseVal_inj_iff h)
    simp [h, hbeq, eraseVal, eraseBaseLit]
  · simp [h]

/-- An erased literal came from some literal, whose erasure it is. -/
private theorem eraseVal_eq_lit {v : Val} {l : BaseLit}
    (h : eraseVal v = hl_val(#l)) : ∃ l', v = hl_val(#l') ∧ eraseBaseLit l' = l := by
  cases v <;> erase_simp at h <;> cases h
  exact ⟨_, rfl, rfl⟩

/-- Erasure rewrites only prophecy literals, and only to `poison`, so any other
erased literal came from that very literal. -/
private theorem eraseVal_eq_lit_of_ne_poison {v : Val} {l : BaseLit}
    (hne : l ≠ .poison) (h : eraseVal v = hl_val(#l)) : v = hl_val(#l) := by
  obtain ⟨l', rfl, hb⟩ := eraseVal_eq_lit h
  cases l' <;> simp_all [eraseBaseLit]

/-- Auxiliary lemma capturing that comparable literals stay comparable under erasure. -/
@[rocq_alias heap_lang.bin_op_eval_erase]
theorem BinOp.eval_erase {op : BinOp} {v1 v2 v' : Val} :
    op.eval (eraseVal v1) (eraseVal v2) = some v' ↔
      ∃ w, op.eval v1 v2 = some w ∧ eraseVal w = v' := by
  by_cases hne : op = .eq
  · subst hne; exact BinOp.eq_eval_erase
  · cases op <;> (try exact absurd rfl hne) <;>
    match v1, v2 with
    | .lit l1, .lit l2 =>
      cases l1 <;> cases l2 <;>
        simp [eraseVal, eraseBaseLit, BinOp.eval, BinOp.evalInt, BinOp.evalBool, BinOp.evalLoc]
    | .lit _, .rec_ .. | .lit _, .pair .. | .lit _, .injL _ | .lit _, .injR _
    | .rec_ .., _ | .pair .., _ | .injL _, _ | .injR _, _ =>
      simp [eraseVal, BinOp.eval]

/-! ## Erasure of the heap -/

@[rocq_alias heap_lang.lookup_erase_heap, simp]
theorem lookup_eraseHeap (h : HeapF (Option Val)) (l : Loc) :
    PartialMap.get? (eraseHeap h) l = (PartialMap.get? h l).map (eraseVal <$> ·) :=
  Iris.Std.LawfulPartialMap.get?_map

@[rocq_alias heap_lang.lookup_erase_heap_None]
theorem lookup_eraseHeap_none (h : HeapF (Option Val)) (l : Loc) :
    PartialMap.get? (eraseHeap h) l = none ↔ PartialMap.get? h l = none := by
  rw [lookup_eraseHeap]; cases PartialMap.get? h l <;> simp

#rocq_ignore heap_lang.erase_heap_insert_Some "Use Iris.Std.LawfulPartialMap.map_insert"
#rocq_ignore heap_lang.erase_heap_insert_None "Use Iris.Std.LawfulPartialMap.map_insert"

@[simp] theorem eraseState_get? (σ : State) (l : Loc) :
    (eraseState σ).get? l = (σ.get? l).map (fun ov => eraseVal <$> ov) := by
  simp [State.get?, eraseState]

theorem eraseState_get?_none (σ : State) (l : Loc) :
    (eraseState σ).get? l = none ↔ σ.get? l = none := by
  simp [State.get?, eraseState]

/-- Erasure commutes with `initHeap`. -/
@[rocq_alias heap_lang.erase_state_init, simp]
theorem eraseState_initHeap (σ : State) (l : Loc) (n : Int) (v : Option Val) :
    eraseState (σ.initHeap l n v) = (eraseState σ).initHeap l n (eraseVal <$> v) := by
  refine State.mk.injEq .. |>.mpr ⟨?_, rfl⟩
  refine Std.LawfulPartialMap.equiv_iff_eq |>.mp fun k => ?_
  simp only [lookup_eraseHeap, get?_foldl_insert]
  split <;> simp [eraseState, lookup_eraseHeap]

#rocq_ignore heap_lang.fmap_heap_array "Use `get?_foldl_insert` and `lookup_eraseHeap` directly"
#rocq_ignore heap_lang.erase_heap_array "Inlined in `eraseState_initHeap`"

/-! ## Erased base step corresponds to an original base step

When the erased program takes a base step producing `(e2, σ2, efs)`, then the original program
takes some base step whose result erases to `(e2, σ2, efs)`. -/
@[rocq_alias heap_lang.base_steps_to_erasure_of]
def BaseStepsToErasureOf (e1 : Exp) (σ1 : State) (e2 : Exp) (σ2 : State) (efs : List Exp) : Prop :=
  ∃ κ' e2' σ2' efs',
    BaseStep e1 σ1 κ' e2' σ2' efs' ∧ eraseExpr e2' = e2 ∧ eraseState σ2' = σ2 ∧ eraseTp efs' = efs

/-- Ithe erased heap has `some (some v)` `l`, then the original heap has some `(some ov')` at `l`
with `eraseVal ov' = v`. -/
private theorem eraseState_get?_some_some {σ : State} {l : Loc} {v : Val}
    (hget : (eraseState σ).get? l = some (some v)) :
    ∃ ov', σ.get? l = some (some ov') ∧ eraseVal ov' = v := by
  rw [eraseState_get?] at hget
  obtain ⟨ov, hov, hev⟩ := Option.map_eq_some_iff.mp hget
  obtain ⟨ov', rfl, hev'⟩ := Option.map_eq_some_iff.mp hev
  exact ⟨ov', hov, hev'⟩

#rocq_ignore heap_lang.erased_base_step_base_step_rec "Proved inline in the `betaS` arm of `erased_baseStep_baseStep`"

@[rocq_alias heap_lang.erased_base_step_base_step_NewProph]
private theorem erased_baseStep_baseStep_NewProph (σ : State) :
    BaseStepsToErasureOf hl(newProph()) σ hl(#.poison) (eraseState σ) [] := by
  obtain ⟨pf, Hpf⟩ := Std.List.fresh σ.usedProphId.toList
  refine ⟨_, _, _, _, .newProphS σ pf (Hpf ∘ Std.ExtTreeSet.mem_toList.mpr), rfl, ?_, rfl⟩
  simp [eraseState]

@[rocq_alias heap_lang.erased_base_step_base_step_AllocN]
private theorem erased_baseStep_baseStep_AllocN (n : Int) (v : Val) (σ : State) (l : Loc)
    (hpos : 0 < n) (hnone : ∀ i, 0 ≤ i → i < n → (eraseState σ).get? (l + i) = none) :
    BaseStepsToErasureOf hl(allocn(#n, v(&v))) σ hl(#l)
      ((eraseState σ).initHeap l n (some (eraseVal v))) [] := by
  refine ⟨_, _, _, _, .allocNS n v σ l hpos fun i hi0 hin =>
    (eraseState_get?_none σ (l + i)).mp (hnone i hi0 hin), rfl, ?_, rfl⟩
  rw [eraseState_initHeap]; rfl

@[rocq_alias heap_lang.erased_base_step_base_step_Free]
private theorem erased_baseStep_baseStep_Free (l : Loc) (v : Val) (σ : State)
    (hget : (eraseState σ).get? l = some (some v)) :
    BaseStepsToErasureOf hl(free(#l)) σ hl(#()) ((eraseState σ).initHeap l 1 none) [] :=
  have ⟨ov', horig, _⟩ := eraseState_get?_some_some hget
  ⟨_, _, _, _, .freeS l ov' σ horig, rfl, by simp, rfl⟩

@[rocq_alias heap_lang.erased_base_step_base_step_Load]
private theorem erased_baseStep_baseStep_Load (l : Loc) (σ : State) (v : Val)
    (hget : (eraseState σ).get? l = some (some v)) :
    BaseStepsToErasureOf hl(! #l) σ hl(v(&v)) (eraseState σ) [] :=
  have ⟨ov', horig, hev⟩ := eraseState_get?_some_some hget
  ⟨_, _, _, _, .loadS l ov' σ horig, by simp [hev], rfl, rfl⟩

@[rocq_alias heap_lang.erased_base_step_base_step_Xchg]
private theorem erased_baseStep_baseStep_Xchg (l : Loc) (v w : Val) (σ : State)
    (hget : (eraseState σ).get? l = some (some v)) :
    BaseStepsToErasureOf hl(xchg(#l, v(&w))) σ hl(v(&v))
      ((eraseState σ).initHeap l 1 (some (eraseVal w))) [] :=
  have ⟨ov', horig, hev⟩ := eraseState_get?_some_some hget
  ⟨_, _, _, _, .xchgS l ov' w σ horig, by simp [hev], by simp, rfl⟩

@[rocq_alias heap_lang.erased_base_step_base_step_Store]
private theorem erased_baseStep_baseStep_Store (l : Loc) (v w : Val) (σ : State)
    (hget : (eraseState σ).get? l = some (some v)) :
    BaseStepsToErasureOf hl(#l ← v(&w)) σ hl(#())
      ((eraseState σ).initHeap l 1 (some (eraseVal w))) [] :=
  have ⟨ov', horig, _⟩ := eraseState_get?_some_some hget
  ⟨_, _, _, _, .storeS l ov' w σ horig, rfl, by simp, rfl⟩

@[rocq_alias heap_lang.erased_base_step_base_step_CmpXchg]
private theorem erased_baseStep_baseStep_CmpXchg (l : Loc) (v w : Val) (σ : State)
    (vl : Val) (b : Bool) (hget : (eraseState σ).get? l = some (some vl))
    (hvl : vl.compareSafe (eraseVal v) = true) (hb : decide (vl = eraseVal v) = b) :
    BaseStepsToErasureOf hl(cmpXchg(#l, v(&v), v(&w))) σ hl(v((&vl, #b)))
      (if b then (eraseState σ).initHeap l 1 (some (eraseVal w)) else eraseState σ) [] := by
  obtain ⟨ov', horig, rfl⟩ := eraseState_get?_some_some hget
  have hcs' : ov'.compareSafe v = true := by rwa [← eraseVal_compareSafe]
  exact ⟨_, _, _, _,
    .cmpXchgS l v w ov' σ b horig hcs' (by rw [← hb, decide_eq_decide.mpr (eraseVal_inj_iff hcs')]),
    rfl, by split <;> simp, rfl⟩

@[rocq_alias heap_lang.erased_base_step_base_step_FAA]
private theorem erased_baseStep_baseStep_FAA (l : Loc) (n m : Int) (σ : State)
    (hget : (eraseState σ).get? l = some (some hl_val(#n))) :
    BaseStepsToErasureOf hl(faa(#l, #m)) σ hl(#n)
      ((eraseState σ).initHeap l 1 (some hl_val(#(n + m)))) [] := by
  obtain ⟨ov', horig, hev⟩ := eraseState_get?_some_some hget
  obtain rfl := eraseVal_eq_lit_of_ne_poison (by simp) hev
  exact ⟨_, _, _, _, .faaS l n m σ horig, by rfl,
    by simp [eraseVal, eraseBaseLit], rfl⟩

/-- `peel1 h` inverts one erasure equation `eraseExpr e = <erased shape>`,
recursing through conjunctions, and substitutes the result away. -/
local syntax "peel1 " ident : tactic
local macro_rules
  | `(tactic| peel1 $h) =>
    `(tactic|
      first
        | (obtain ⟨hx, hy⟩ := $h; peel1 hx; peel1 hy)
        | (obtain ⟨w, he, hv⟩ := eraseExpr_eq_val $h
           subst he
           first
             | subst hv
             | (have hl := eraseVal_eq_lit_of_ne_poison (by simp) hv; subst hl)
             | (cases w <;> erase_simp at hv <;> peel1 hv))
        | skip)

/-- If the erased program makes a base step, so does the original program. -/
@[rocq_alias heap_lang.erased_base_step_base_step]
theorem erased_baseStep_baseStep {e1 : Exp} {σ1 : State} {κ : List Observation} {e2 : Exp}
    {σ2 : State} {efs : List Exp} (h : BaseStep (eraseExpr e1) (eraseState σ1) κ e2 σ2 efs) :
    BaseStepsToErasureOf e1 σ1 e2 σ2 efs := by
  generalize heq1 : eraseExpr e1 = e1e at h
  cases h with
  | betaS f x e0 v2 e' σ heq =>
    cases e1 <;> erase_simp at heq1
    case app ef ea =>
      peel1 heq1
      exact ⟨_, _, _, _, .betaS _ _ _ _ _ σ1 rfl, by
        simp [heq, eraseExpr_subst, eraseVal], rfl, rfl⟩
    case newProph =>
      obtain ⟨hf, ha⟩ := heq1
      obtain ⟨_, _, _, _, hs, he2, hσ, hef⟩ := erased_baseStep_baseStep_NewProph σ1
      cases hf; cases ha; subst heq
      exact ⟨_, _, _, _, hs, he2, hσ, hef⟩
  | _ =>
    cases e1 <;> erase_simp at heq1
    peel1 heq1
    all_goals first
      | (obtain ⟨w, hw, hwe⟩ := UnOp.eval_erase.mp ‹_›
         exact ⟨_, _, _, _, .unOpS _ _ w _ hw, by simp [hwe], rfl, rfl⟩)
      | (obtain ⟨w, hw, hwe⟩ := BinOp.eval_erase.mp ‹_›
         exact ⟨_, _, _, _, .binOpS _ _ _ w _ hw, by simp [hwe], rfl, rfl⟩)
      | exact erased_baseStep_baseStep_Free _ _ _ ‹_›
      | exact erased_baseStep_baseStep_Load _ _ _ ‹_›
      | exact erased_baseStep_baseStep_Store _ _ _ _ ‹_›
      | exact erased_baseStep_baseStep_Xchg _ _ _ _ ‹_›
      | exact erased_baseStep_baseStep_FAA _ _ _ _ ‹_›
      | exact erased_baseStep_baseStep_AllocN _ _ _ _ ‹_› ‹_›
      | exact erased_baseStep_baseStep_CmpXchg _ _ _ _ _ _ ‹_› ‹_› ‹_›
      | exact ⟨_, _, _, _, by constructor, by first | rfl | erase_simp, rfl, rfl⟩

/-- A primitive step in the original program can be matched (up to a number of deterministic pure
steps in the erased program) by a step in the erased program. -/
@[rocq_alias heap_lang.prim_step_matched_by_erased_steps]
def PrimStepMatchedByErasedSteps (e1 : Exp) (σ1 : State) (e2 : Exp)
    (σ2 : State) (efs : List Exp) : Prop :=
  ∃ e2' σ2' κ' efs' e2'',
    PrimStep.primStep (e1, σ1) κ' (e2', σ2', efs') ∧
      Relation.ReflTransGen PurePrimStep e2 e2'' ∧
      eraseExpr e2' = e2'' ∧ eraseState σ2' = σ2 ∧ eraseTp efs' = efs

@[rocq_alias heap_lang.prim_step_matched_by_erased_steps_ectx]
theorem PrimStepMatchedByErasedSteps.fill_ctx (K : List ECtxItem) {e1 : Exp}
    {σ1 : State} {e2 : Exp} {σ2 : State} {efs : List Exp}
    (h : PrimStepMatchedByErasedSteps e1 σ1 e2 σ2 efs) :
    PrimStepMatchedByErasedSteps (fill K e1) σ1
      (fill (eraseECtx K) e2) σ2 efs := by
  obtain ⟨e2', σ2', κ', efs', e2'', hstep, hpure, hex, hst, htp⟩ := h
  exact ⟨fill K e2', σ2', κ', efs', fill (eraseECtx K) e2'', fill_primStep K hstep,
    ReflTransGen_pureStep_fill (K := (fill (eraseECtx K) ·)) hpure,
    by rw [← hex, eraseECtx_fill], hst, htp⟩

/-! ### Helper lemmas for the induction on context length -/

/-- Any expression whose `toVal` is `none` filled into a context is not a value. -/
private theorem fill_not_val_ne_val {K : List ECtxItem} {e' : Exp} (w : Val)
    (hnv : toVal e' = none) : fill K e' ≠ (.val w : Exp) := by
  intro hw; simpa [hw, ToVal.toVal] using fill_not_val (K := K) hnv

/-- A single evaluation-context frame can be stripped from a `NotStuck` obligation. -/
private theorem notStuck_of_frame {Ki : ECtxItem} {e : Exp} {σ : State}
    (h : PrimStep.NotStuck (Ki.fill e, σ)) : PrimStep.NotStuck (e, σ) :=
  Language.Context.notStuck_fill_inv (K := fill [Ki]) (by simpa [fillItem] using h)

/-- Peel the outermost frame off an evaluation context: either the context is
empty, or it is `K' ++ [Ki]` and the expression is `Ki` filled with `fill K' e'`. -/
theorem fill_eq_snoc {e e' : Exp} {K : List ECtxItem} (heq : e = fill K e') :
    (K = [] ∧ e' = e) ∨ ∃ K' Ki, K = K' ++ [Ki] ∧ e = Ki.fill (fill K' e') := by
  cases K using FromMathlib.List.reverseRec with
  | nil => exact .inl ⟨rfl, heq.symm⟩
  | append_singleton Ks Ki _ => rw [fill_snoc] at heq; exact .inr ⟨Ks, Ki, rfl, heq⟩

/-- Inversion for a `Fst` head atop an evaluation context: either the context is
empty, or its outermost frame is `.fst`. -/
theorem fill_eq_fst {X e' : Exp} {K : List ECtxItem} (heq : hl(fst(&X)) = fill K e') :
    (K = [] ∧ e' = hl(fst(&X))) ∨ ∃ K', K = K' ++ [.fst] ∧ X = fill K' e' := by
  rcases fill_eq_snoc heq with h | ⟨Ks, Ki, rfl, hf⟩
  · exact .inl h
  · cases Ki with
    | fst => simp only [ECtxItem.fill, Exp.fst.injEq] at hf; exact .inr ⟨Ks, rfl, hf⟩
    | _ => simp only [ECtxItem.fill] at hf; cases hf

/-- Inversion for a `Pair` head atop an evaluation context: either the context is
empty, or its outermost frame is `.pairL` (hole left, right side already a value)
or `.pairR` (hole right). -/
theorem fill_eq_pair {X Y e' : Exp} {K : List ECtxItem} (heq : hl((&X, &Y)) = fill K e') :
    (K = [] ∧ e' = hl((&X, &Y)))
    ∨ (∃ K' v, K = K' ++ [.pairL v] ∧ Y = .ofVal v ∧ X = fill K' e')
    ∨ (∃ K', K = K' ++ [.pairR X] ∧ Y = fill K' e') := by
  rcases fill_eq_snoc heq with h | ⟨Ks, Ki, rfl, hf⟩
  · exact .inl h
  · cases Ki with
    | pairL v =>
      simp only [ECtxItem.fill, Exp.pair.injEq] at hf
      exact .inr (.inl ⟨Ks, v, rfl, hf.2, hf.1⟩)
    | pairR e0 =>
      simp only [ECtxItem.fill, Exp.pair.injEq] at hf
      obtain ⟨rfl, h2⟩ := hf
      exact .inr (.inr ⟨Ks, rfl, h2⟩)
    | _ => simp only [ECtxItem.fill] at hf; cases hf

/-- Inversion for the erased `Resolve` shape `Resolve e0 (val v1) (val v2)` atop a
context whose hole `e'` is a non-value: either the context is empty, or its
outermost frame is a `.resolveL`. -/
theorem fill_eq_resolve {e0 : Exp} {v1 v2 : Val} {K : List ECtxItem} {e' : Exp}
    (hnv : toVal e' = none) (heq : hl(resolve(&e0, v(&v1), v(&v2))) = fill K e') :
    (K = [] ∧ e' = hl(resolve(&e0, v(&v1), v(&v2))))
    ∨ ∃ K' Ki, K = K' ++ [ECtxItem.resolveL Ki v1 v2] ∧ e0 = Ki.fill (fill K' e') := by
  rcases fill_eq_snoc heq with h | ⟨Ks, Ki, rfl, hf⟩
  · exact .inl h
  · cases Ki with
    | resolveL ctx' u1 u2 =>
      simp only [ECtxItem.fill, Exp.resolve.injEq] at hf
      obtain ⟨h0, ⟨_⟩, ⟨_⟩⟩ := hf; exact .inr ⟨Ks, ctx', rfl, h0⟩
    | resolveM =>
      simp only [ECtxItem.fill, Exp.resolve.injEq] at hf
      exact absurd hf.2.1.symm (fill_not_val_ne_val _ hnv)
    | resolveR =>
      simp only [ECtxItem.fill, Exp.resolve.injEq] at hf
      exact absurd hf.2.2.symm (fill_not_val_ne_val _ hnv)
    | _ => simp only [ECtxItem.fill] at hf; cases hf

/-- Simplified version of `fill_eq_resolve` which drops the residual equation. -/
@[rocq_alias heap_lang.fill_to_resolve]
theorem fill_to_resolve {e0 : Exp} {v1 v2 : Val} {K : List ECtxItem} {e' : Exp}
    (hnv : toVal e' = none) (heq : hl(resolve(&e0, v(&v1), v(&v2))) = fill K e') :
    K = [] ∨ ∃ K' Ki, K = K' ++ [ECtxItem.resolveL Ki v1 v2] :=
  (fill_eq_resolve hnv heq).imp And.left fun ⟨K', Ki, hK, _⟩ => ⟨K', Ki, hK⟩

open Lean Elab Tactic Meta in
local elab "fill_frame" : tactic => do
  let ctors := (← getConstInfoInduct ``ECtxItem).ctors
  let tgt ← instantiateMVars (← getMainTarget)
  let some ki := tgt.find? fun e =>
      match e.getAppFn with
      | .const c _ => ctors.contains c
      | _ => false
    | throwError "fill_frame: no evaluation-context frame in the goal"
  let .const c _ := ki.getAppFn | throwError "fill_frame: unexpected frame"
  let hole ← `(term| _)
  let holes := Array.replicate ki.getAppArgs.size hole
  let stx ← `(term| $(mkIdent c):ident $holes*)
  evalTactic (← `(tactic| exact ⟨$stx, _, rfl, by erase_simp, by simp_all⟩))

/-- Inversion for an erased evaluation-context frame: if `eraseExpr e1` is the
frame `Ki` filled with a non-value hole `X`, then `e1` itself decomposes into an
original frame erasing to `Ki`, unless `Ki = .fst` and `e1` is a `Resolve` (whose
erasure `.fst (.fst ((_, _), _))` also presents a `.fst` head). -/
theorem erase_eq_fill_item {e1 X : Exp} {Ki : ECtxItem} (hnv : toVal X = none)
    (heq : eraseExpr e1 = Ki.fill X) :
    (∃ Ki_orig einner, e1 = Ki_orig.fill einner
        ∧ eraseECtxItem Ki_orig = [Ki] ∧ eraseExpr einner = X)
    ∨ (Ki = .fst ∧ ∃ r0 r1 r2, e1 = hl(resolve(&r0, &r1, &r2))) := by
  cases Ki <;> cases e1 <;>
    simp_all [eraseExpr, erasedNewProph, eraseResolve, ECtxItem.fill] <;>
    peel1 heq <;>
    first
      | fill_frame
      | simp [ToVal.toVal] at hnv

#rocq_ignore heap_lang.is_Resolve "The second disjunct of `erase_eq_fill_item`. "
#rocq_ignore heap_lang.is_Resolve_dec "Decidability is unused. "

/-- A single pure step, taken from a `PureExec` instance under the evaluation
context `K`. -/
private theorem pureStepIn (K : List ECtxItem) {e1 e2 : Exp} [h : PureExec True 1 e1 e2] :
    fill K e1 -ᵖ->* fill K e2 := by
  cases h.pureExec trivial with
  | tail _ hrfl hstep => cases hrfl; exact ReflTransGen_pureStep_fill _ (.single hstep)

/-- `Fst (Fst ((v0, v1), v2))` reduces to `v0` by four pure steps. -/
@[rocq_alias heap_lang.projs_pure_steps]
theorem projs_pure_steps (v0 v1 v2 : Val) :
    Relation.ReflTransGen PurePrimStep (eraseResolve hl(v(&v0)) hl(v(&v1)) hl(v(&v2))) hl(v(&v0)) :=
  calc eraseResolve hl(v(&v0)) hl(v(&v1)) hl(v(&v2))
    _ -ᵖ->* hl(fst(fst((v((&v0, &v1)), v(&v2))))) := pureStepIn [.pairL v2, .fst, .fst]
    _ -ᵖ->* hl(fst(fst(v(((&v0, &v1), &v2))))) := pureStepIn [.fst, .fst]
    _ -ᵖ->* hl(fst(v((&v0, &v1)))) := pureStepIn [.fst]
    _ -ᵖ->* hl(v(&v0)) := pureStepIn []

/-- Pushing a `.resolveL` frame at the end of a context into the `Resolve` node it names. -/
private theorem fill_snoc_resolveL (K : List ECtxItem) (Ki : ECtxItem) (v1 v2 : Val) (e : Exp) :
    fill (K ++ [ECtxItem.resolveL Ki v1 v2]) e =
      hl(resolve(&(fill (K ++ [Ki]) e), v(&v1), v(&v2))) := by
  simp [fillItem, ECtxItem.fill]

private theorem fill_resolve_frames (Ks : List ECtxItem) (a b : Val) (e : Exp) :
    fill (Ks ++ [ECtxItem.pairL a] ++ [ECtxItem.pairL b] ++ [ECtxItem.fst] ++ [ECtxItem.fst]) e =
      eraseResolve (fill Ks e) hl(v(&a)) hl(v(&b)) := by
  simp [fill_append, fillItem, ECtxItem.fill, eraseResolve]

/-- Pure steps in the first component of an erased `Resolve`. -/
private theorem fill_resolve_frames_pureSteps {e e' : Exp} {Ks : List ECtxItem} (a b : Val)
    (h : fill Ks e -ᵖ->* e') :
    fill (Ks ++ [ECtxItem.pairL a] ++ [ECtxItem.pairL b] ++ [ECtxItem.fst] ++ [ECtxItem.fst]) e
      -ᵖ->* eraseResolve e' hl(v(&a)) hl(v(&b)) := by
  rw [fill_resolve_frames]
  exact ReflTransGen_pureStep_fill
    (fill [ECtxItem.pairL a, ECtxItem.pairL b, ECtxItem.fst, ECtxItem.fst]) h

private theorem notStuck_resolve_inv {e0 : Exp} {v1 v2 : Val} {σ : State}
    (hns : PrimStep.NotStuck (hl(resolve(&e0, v(&v1), v(&v2))), σ)) :
    PrimStep.NotStuck (e0, σ) ∧
      ((∃ (p : ProphId), ∃ w σ' κ efs, v1 = hl_val(#p) ∧ σ.usedProphId.contains p ∧
          BaseStep e0 σ κ hl(v(&w)) σ' efs)
        ∨ (toVal e0 = none ∧ ∀ e2 σ2 κ efs, ¬ BaseStep e0 σ κ e2 σ2 efs)) := by
  rcases hns with hval | ⟨_, _, _, _, hstep⟩
  · simp [ToVal.toVal] at hval
  generalize heq : hl(resolve(&e0, v(&v1), v(&v2))) = ee at hstep
  rcases hstep with @⟨f1, f2, K, bs⟩
  have hnv : toVal f1 = none := EctxItemLanguage.val_stuck bs
  rcases fill_eq_resolve hnv heq with ⟨rfl, rfl⟩ | ⟨K', ctx, rfl, hfe⟩
  · cases bs with
    | resolveS p _ _ _ _ _ _ _ bs_inner hused =>
      exact ⟨.inr ⟨_, _, _, _, .ofBaseStep [] bs_inner⟩, .inl ⟨p, _, _, _, _, rfl, hused, bs_inner⟩⟩
  subst hfe
  refine ⟨.inr ⟨_, _, _, _, .ofBaseStep' (K' ++ [ctx]) ?_ rfl bs⟩,
    .inr ⟨by cases ctx <;> simp [ECtxItem.fill, ToVal.toVal], fun _ _ _ _ hb => ?_⟩⟩
  · rw [fill_snoc]
  · have hval : (toVal (fill K' f1)).isSome := EctxItemLanguage.base_ctx_step_val hb
    simp [fill_not_val hnv] at hval

/-- `Resolve` applied to three values has no base step. -/
@[rocq_alias heap_lang.Resolve_3_vals_base_stuck]
theorem Resolve_3_vals_base_stuck (v0 v1 v2 : Val) (σ : State)
    (κ : List Observation) (e : Exp) (σ' : State) (efs : List Exp) :
    ¬ BaseStep hl(resolve(v(&v0), v(&v1), v(&v2))) σ κ e σ' efs := by
  intro h; cases h with | resolveS _ _ _ _ _ _ _ _ hstep _ => cases hstep

/-- `Resolve` on three values is not `NotStuck`. -/
@[rocq_alias heap_lang.Resolve_3_vals_unsafe]
theorem Resolve_3_vals_unsafe (v0 v1 v2 : Val) (σ : State) :
    ¬ PrimStep.NotStuck (hl(resolve(v(&v0), v(&v1), v(&v2))), σ) := by
  intro hns
  rcases (notStuck_resolve_inv hns).2 with ⟨_, _, _, _, _, _, _, bs⟩ | ⟨hnv, _⟩
  · cases bs
  · simp [ToVal.toVal] at hnv

private theorem baseStep_pair_inv {X Y e2 : Exp} {σ σ2 : State}
    {κ : List Observation} {efs : List Exp} (h : BaseStep hl((&X, &Y)) σ κ e2 σ2 efs) :
    ∃ x y : Val, X = hl(v(&x)) ∧ Y = hl(v(&y)) := by
  cases h; exact ⟨_, _, rfl, rfl⟩

private theorem exists_val_of_baseStep_val {e e2 : Exp} {v : Val} {σ σ' σ2 σ2' : State}
    {κ κ' : List Observation} {efs efs' : List Exp}
    (h : BaseStep e σ κ e2 σ2 efs) (hv : BaseStep e σ' κ' hl(v(&v)) σ2' efs') :
    ∃ w, e2 = hl(v(&w)) := by
  cases h <;> try exact ⟨_, rfl⟩
  all_goals cases hv <;> first | exact ⟨_, rfl⟩ | exact ⟨v, by grind⟩

private theorem resolve_baseStep_inv {e e2 : Exp} {v1 v2 : Val} {σ σ2 : State}
    {κ : List Observation} {efs : List Exp}
    (hns : PrimStep.NotStuck (hl(resolve(&e, v(&v1), v(&v2))), σ)) (h : BaseStep e σ κ e2 σ2 efs) :
    ∃ (p : ProphId), ∃ w, v1 = hl_val(#p) ∧ σ.usedProphId.contains p ∧ e2 = hl(v(&w)) := by
  rcases (notStuck_resolve_inv hns).2 with ⟨p, _, _, _, _, rfl, hused, bs⟩ | ⟨_, hno⟩
  · obtain ⟨w, hw⟩ := exists_val_of_baseStep_val h bs; exact ⟨p, w, rfl, hused, hw⟩
  · exact absurd h (hno _ _ _ _)

private theorem PrimStepMatchedByErasedSteps.fill_item (Ki : ECtxItem) {e0 e2' : Exp}
    {K : List ECtxItem} {σ1 σ2 : State} {efs : List Exp}
    (h : PrimStepMatchedByErasedSteps e0 σ1 (fill K e2') σ2 efs) :
    PrimStepMatchedByErasedSteps (Ki.fill e0) σ1 (fill (K ++ eraseECtxItem Ki) e2') σ2 efs := by
  simpa [eraseECtx, fill_append, fillItem] using h.fill_ctx [Ki]

private theorem resolve_pairL_primStepMatched {r0 e2' : Exp} {w1 w2 : Val}
    {Ks : List ECtxItem} {σ1 σ2 : State} {efs : List Exp}
    (hns : PrimStep.NotStuck (hl(resolve(&r0, v(&w1), v(&w2))), σ1))
    (hm : PrimStepMatchedByErasedSteps r0 σ1 (fill Ks e2') σ2 efs) :
    PrimStepMatchedByErasedSteps hl(resolve(&r0, v(&w1), v(&w2))) σ1
      (fill (Ks ++ [ECtxItem.pairL (eraseVal w1)] ++ [ECtxItem.pairL (eraseVal w2)]
                ++ [ECtxItem.fst] ++ [ECtxItem.fst]) e2') σ2 efs := by
  obtain ⟨e_next, σ', κ', efs', _, hstep, hpure, rfl, hσ, hef⟩ := hm
  obtain @⟨f1, f2, K, hb⟩ := hstep
  cases K using FromMathlib.List.reverseRec with
  | nil =>
    obtain ⟨p, v, rfl, hused, rfl⟩ := resolve_baseStep_inv hns hb
    exact ⟨hl(v(&v)), σ', κ' ++ [(p, (v, w2))], efs', hl(v(&(eraseVal v))),
      .ofBaseStep [] (.resolveS p v f1 σ1 w2 σ' κ' efs' hb hused),
      (fill_resolve_frames_pureSteps _ _ hpure).trans (projs_pure_steps _ _ _), rfl, hσ, hef⟩
  | append_singleton Krest Ktop _ =>
    refine ⟨hl(resolve(&(fill (Krest ++ [Ktop]) f2), v(&w1), v(&w2))), σ', κ', efs', _,
      ?_, fill_resolve_frames_pureSteps _ _ hpure, rfl, hσ, hef⟩
    rw [← fill_snoc_resolveL Krest Ktop w1 w2 f1, ← fill_snoc_resolveL Krest Ktop w1 w2 f2]
    exact .ofBaseStep _ hb

/-- Helper for the `Resolve r0 r1 r2` sub-case of `erased_primStep_primStep` a `Ki = .fst` frame. -/
private theorem resolve_fst_primStepMatched {r0 r1 r2 : Exp} {Ks : List ECtxItem} {e1' e2' : Exp}
    {σ1 σ2 : State} {κ : List Observation} {efs : List Exp}
    (bstep : BaseStep e1' (eraseState σ1) κ e2' σ2 efs)
    (hns : PrimStep.NotStuck (hl(resolve(&r0, &r1, &r2)), σ1))
    (heq_e : hl(fst(((&(eraseExpr r0), &(eraseExpr r1)), &(eraseExpr r2)))) = fill Ks e1')
    (IHapp : ∀ {K' : List ECtxItem} {e0 : Exp}, K'.length ≤ Ks.length →
      eraseExpr e0 = fill K' e1' → PrimStep.NotStuck (e0, σ1) →
      PrimStepMatchedByErasedSteps e0 σ1 (fill K' e2') σ2 efs) :
    PrimStepMatchedByErasedSteps hl(resolve(&r0, &r1, &r2)) σ1
      (fill (Ks ++ [ECtxItem.fst]) e2') σ2 efs := by
  rcases fill_eq_fst heq_e with ⟨rfl, rfl⟩ | ⟨Ks', rfl, hfst⟩
  · cases bstep
  rcases fill_eq_pair hfst with ⟨rfl, rfl⟩ | ⟨Ks'', v2, rfl, hv2, hpair⟩ | ⟨Ks'', rfl, hhole⟩
  · cases bstep
  · obtain ⟨w2, rfl, rfl⟩ := eraseExpr_eq_val hv2
    rcases fill_eq_pair hpair with ⟨rfl, rfl⟩ | ⟨Ks''', v1, rfl, hv1, hhole⟩ | ⟨Ks''', rfl, hhole⟩
    · obtain ⟨_, _, h0, h1⟩ := baseStep_pair_inv bstep
      obtain ⟨_, rfl, _⟩ := eraseExpr_eq_val h0
      obtain ⟨_, rfl, _⟩ := eraseExpr_eq_val h1
      exact absurd hns (Resolve_3_vals_unsafe _ _ _ _)
    · obtain ⟨w1, rfl, rfl⟩ := eraseExpr_eq_val hv1
      exact resolve_pairL_primStepMatched hns
        (IHapp (by simp) hhole (notStuck_resolve_inv hns).1)
    · simpa [eraseECtxItem, ECtxItem.fill] using
        (IHapp (by simp) hhole (notStuck_of_frame (Ki := .resolveM r0 w2) hns)).fill_item
          (.resolveM r0 w2)
  · simpa [eraseECtxItem, ECtxItem.fill] using
      (IHapp (by simp) hhole (notStuck_of_frame (Ki := .resolveR r0 r1) hns)).fill_item
        (.resolveR r0 r1)

/-- Every primitive step of the erased program is matched by a primitive step
in the original program, possibly followed by some deterministic pure steps
in the erased program. -/
@[rocq_alias heap_lang.erased_prim_step_prim_step]
theorem erased_primStep_primStep {e1 : Exp} {σ1 : State} {κ : List Observation} {e2 : Exp}
    {σ2 : State} {efs : List Exp}
    (h : PrimStep.primStep (eraseExpr e1, eraseState σ1) κ (e2, σ2, efs))
    (hns : PrimStep.NotStuck (e1, σ1)) : PrimStepMatchedByErasedSteps e1 σ1 e2 σ2 efs := by
  generalize heq_e : eraseExpr e1 = ee at h
  rcases h with @⟨e1', e2', K, bstep⟩
  generalize hlen : K.length = len
  induction len using Nat.strongRecOn generalizing K e1 with
  | _ len IHlen =>
    cases K using FromMathlib.List.reverseRec with
    | nil =>
      simp only [fill_nil] at heq_e; subst heq_e
      obtain ⟨κ', e2orig, σ2orig, efsorig, bs, he2, hσ, hef⟩ := erased_baseStep_baseStep bstep
      exact ⟨e2orig, σ2orig, κ', efsorig, e2', primStep_of_baseStep bs, .refl, he2, hσ, hef⟩
    | append_singleton Ks Ki revIH =>
      rw [fill_snoc] at heq_e
      have hnv_inner : toVal (fill Ks e1') = none := fill_not_val (EctxItemLanguage.val_stuck bstep)
      rw [List.length_append, List.length_cons, List.length_nil] at hlen
      have IHapp : ∀ {K' : List ECtxItem} {e0 : Exp}, K'.length ≤ Ks.length →
          eraseExpr e0 = fill K' e1' → PrimStep.NotStuck (e0, σ1) →
          PrimStepMatchedByErasedSteps e0 σ1 (fill K' e2') σ2 efs := by
        intro K' e0 hlk he0 hns0
        exact IHlen K'.length (Nat.lt_of_le_of_lt hlk (by omega)) hns0 he0 rfl
      clear hlen IHlen revIH
      rcases erase_eq_fill_item hnv_inner heq_e with
        ⟨Ki_orig, einner, rfl, hek, hi⟩ | ⟨rfl, r0, r1, r2, rfl⟩
      · rw [← hek]
        exact (IHapp (Nat.le_refl _) hi (notStuck_of_frame hns)).fill_item Ki_orig
      · erase_simp at heq_e
        exact resolve_fst_primStepMatched bstep hns heq_e IHapp

#rocq_ignore heap_lang.non_resolve_prim_step_matched_by_erased_steps_ectx_item
  "Proved in place in the first branch of the `erase_eq_fill_item`"
#rocq_ignore heap_lang.prim_step_matched_by_erased_steps_ectx_item
  "Proved in place in the `append_singleton` branch of `erased_primStep_primStep`; its `Resolve` half is `resolve_fst_primStepMatched`."

/-- Every base step in the original program is matched by at least one
primitive step in the erased program (whose result may differ by a bounded
number of deterministic pure steps). -/
@[rocq_alias heap_lang.base_step_erased_prim_step]
theorem baseStep_erased_primStep {e1 : Exp} {σ1 : State} {κ : List Observation} {e2 : Exp}
    {σ2 : State} {efs : List Exp} (h : BaseStep e1 σ1 κ e2 σ2 efs) :
    ∃ e2' σ2' efs', PrimStep.primStep (eraseExpr e1, eraseState σ1) [] (e2', σ2', efs') := by
  induction h with
  | allocNS n v σ l hpos hnone =>
    refine ⟨_, _, _, primStep_of_baseStep (.allocNS n (eraseVal v) (eraseState σ) l hpos fun i hi0 hin => ?_)⟩
    rw [eraseState_get?, hnone i hi0 hin]; rfl
  | cmpXchgS l v1 v2 vl σ b hget hcs hb =>
    refine ⟨_, _, _, primStep_of_baseStep
      (.cmpXchgS l (eraseVal v1) (eraseVal v2) (eraseVal vl) (eraseState σ) b ?_ ?_ ?_)⟩
    · rw [eraseState_get?, hget]; rfl
    · rwa [eraseVal_compareSafe]
    · rwa [decide_eq_decide.mpr (eraseVal_inj_iff hcs)]
  | resolveS p v e σ w σ' κs ts hstep hused ih =>
    obtain ⟨e2', σ2', efs', hstep'⟩ := ih
    exact ⟨_, σ2', efs', fill_primStep
      [(.pairL hl_val(#.poison) : ECtxItem), .pairL (eraseVal w), .fst, .fst] hstep'⟩
  | _ =>
    exact ⟨_, _, _, primStep_of_baseStep (by
      erase_simp
      constructor <;>
        first
          | rfl
          | exact UnOp.eval_erase.mpr ⟨_, ‹_›, rfl⟩
          | exact BinOp.eval_erase.mpr ⟨_, ‹_›, rfl⟩
          | (simp [*] <;> rfl))⟩

#rocq_ignore heap_lang.base_step_erased_prim_step_un_op "Proved in place in the catch-all arm of `baseStep_erased_primStep`"
#rocq_ignore heap_lang.base_step_erased_prim_step_bin_op "Proved in place in the catch-all arm of `baseStep_erased_primStep`"
#rocq_ignore heap_lang.base_step_erased_prim_step_free "Proved in place in the catch-all arm of `baseStep_erased_primStep`"
#rocq_ignore heap_lang.base_step_erased_prim_step_load "Proved in place in the catch-all arm of `baseStep_erased_primStep`"
#rocq_ignore heap_lang.base_step_erased_prim_step_xchg "Proved in place in the catch-all arm of `baseStep_erased_primStep`"
#rocq_ignore heap_lang.base_step_erased_prim_step_store "Proved in place in the catch-all arm of `baseStep_erased_primStep`"
#rocq_ignore heap_lang.base_step_erased_prim_step_FAA "Proved in place in the catch-all arm of `baseStep_erased_primStep`"
#rocq_ignore heap_lang.base_step_erased_prim_step_allocN "Proved in place in the `| allocNS` arm of `baseStep_erased_primStep`."
#rocq_ignore heap_lang.base_step_erased_prim_step_CmpXchg "Proved in place in the `| cmpXchgS` arm of `baseStep_erased_primStep`."
#rocq_ignore heap_lang.base_step_erased_prim_step_resolve "Proved in place in the `| resolveS` arm of `baseStep_erased_primStep`."

/-- If the original expression is reducible, so is the erased one. -/
@[rocq_alias heap_lang.reducible_erased_reducible]
theorem reducible_erased_reducible {e : Exp} {σ : State} (h : PrimStep.Reducible (e, σ)) :
    PrimStep.Reducible (eraseExpr e, eraseState σ) := by
  obtain ⟨obs, e', σ', efs, ⟨bstep⟩⟩ := h
  rename_i e1 e2 K
  rw [eraseECtx_fill]
  obtain ⟨e2', σ2', efs', hstep⟩ := baseStep_erased_primStep bstep
  refine ⟨_, _, _, _, fill_primStep (eraseECtx K) hstep⟩

/-! ## Safety after pure steps in the erased thread pool -/

private theorem map_eq_append_cons {α β : Type _} {f : α → β} :
    ∀ {l : List α} {xs : List β} {y : β} {ys : List β},
      l.map f = xs ++ y :: ys →
      ∃ la a lb, l = la ++ a :: lb ∧ la.map f = xs ∧ f a = y ∧ lb.map f = ys
  | [], xs, y, ys, h => by simp at h
  | a :: l, [], y, ys, h => by
    simp only [List.map_cons, List.nil_append, List.cons.injEq] at h
    exact ⟨[], a, l, rfl, rfl, h.1, h.2⟩
  | a :: l, x :: xs, y, ys, h => by
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨la, a', lb, hl, hla, hfa, hlb⟩ := map_eq_append_cons h.2
    refine ⟨a :: la, a', lb, ?_, ?_, hfa, hlb⟩
    · simp [hl]
    · simp [List.map_cons, hla, h.1]

@[rocq_alias heap_lang.pure_step_tp_safe]
theorem pureStep_tp_safe {t1 t2 : List Exp} {e1 : Exp} {σ : State}
    (Ht2 : ∀ e2 ∈ t2, PrimStep.NotStuck (e2, σ))
    (Hpr : t1.Forall₂ (Relation.ReflTransGen PurePrimStep) (eraseTp t2))
    (Hmem : e1 ∈ t1) : PrimStep.NotStuck (e1, eraseState σ) := by
  obtain ⟨ps, ss, rfl⟩ := List.append_of_mem Hmem
  obtain ⟨l2, l2', hl2, hpr1, hpr2, hlen⟩ := List.exists_of_forall₂_append Hpr
  obtain ⟨e2, l2'', rfl, hpstep, _⟩ := List.exists_of_forall₂_cons hpr2
  obtain ⟨t2a, e2', t2b, rfl, _, rfl, _⟩ := map_eq_append_cons (f := eraseExpr) hl2
  have hns : PrimStep.NotStuck (e2', σ) := Ht2 e2' (by simp)
  rcases Relation.ReflTransGen.cases_head hpstep with heq | ⟨e', hpstep_first, _⟩
  · subst heq
    rcases hns with hval | hred
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hval
      obtain rfl := (coe_of_toVal_eq_some hv).symm
      exact .inl rfl
    · exact .inr (reducible_erased_reducible hred)
  · exact .inr (reducible_of_reducibleNoObs (hpstep_first.safe _))

/-! ## Top-level erasure theorem -/

private theorem pureSteps_refl (t : List Exp) : Language.PureSteps t t := by
  induction t with
  | nil => exact .nil
  | cons _ _ ih => exact .cons .refl ih

private theorem pureSteps_set {t t' : List Exp} (h : Language.PureSteps t t') {i : Nat}
    {e' eo' : Exp} (hpure : Relation.ReflTransGen PurePrimStep e' eo') :
    Language.PureSteps (t.set i e') (t'.set i eo') := by
  induction h generalizing i with
  | nil => exact .nil
  | @cons a b l1 l2 hab hl ih =>
    cases i with
    | zero => exact hl.cons hpure
    | succ k => exact ih.cons hab

/-- Inversion for an index lookup in an erased thread pool. -/
private theorem getElem?_eraseTp {t : List Exp} {i : Nat} {ei : Exp}
    (h : (eraseTp t)[i]? = some ei) : ∃ eo, t[i]? = some eo ∧ eraseExpr eo = ei := by
  rw [eraseTp, List.getElem?_map] at h
  exact Option.map_eq_some_iff.mp h

/-- The cut lemma for `erasure`. Any reachable erased configuration comes
from an original configuration whose erasure `pure_steps` up to it. -/
private theorem erasure_cut {e : Exp} {σ : State} {φ : Val → State → Prop}
    (Had : adequate .NotStuck e σ φ) {ρ2 : List Exp × State}
    (h : Relation.ReflTransGen Language.ErasedStep ([eraseExpr e], eraseState σ) ρ2) :
    ∃ (t2'' : List Exp) (σ2' : State),
      Relation.ReflTransGen Language.ErasedStep ([e], σ) (t2'', σ2') ∧
      ρ2.2 = eraseState σ2' ∧
      Language.PureSteps ρ2.1 (eraseTp t2'') := by
  induction h with
  | refl =>
    exact ⟨[e], σ, .refl, rfl, pureSteps_refl _⟩
  | @tail ρ_mid ρ2' _ hstep IH =>
    obtain ⟨t2, σ2⟩ := ρ2'
    obtain ⟨t2'', σ2', hos, hσ, hpr⟩ := IH
    obtain ⟨t3, σ3⟩ := ρ_mid
    simp only at hσ hpr
    rw [hσ] at hstep
    rcases Language.erasedStep_pureSteps hstep hpr with
      ⟨heqσ, hpstep⟩ | ⟨i, ei, eₜ, e', obs', hi1, hi2, rfl, hpstep⟩
    · exact ⟨t2'', σ2', hos, heqσ.symm, hpstep⟩
    · obtain ⟨eio, hlookup, rfl⟩ := getElem?_eraseTp hi2
      have heio_ns : PrimStep.NotStuck (eio, σ2') :=
        Had.adequate_not_stuck _ _ _ rfl hos (List.mem_of_getElem? hlookup)
      obtain ⟨e2', σ2next, κ_ignore, efs', e2'', hstep', hpure', herase, hst, htp⟩ :=
        erased_primStep_primStep hpstep heio_ns
      refine ⟨t2''.set i e2' ++ efs', σ2next, ?_, hst.symm, ?_⟩
      · exact hos.tail ⟨_, Language.step_update_of_getElem? _ _ hlookup hstep'⟩
      · simp only [eraseTp, List.map_append, List.map_set, ← htp]
        exact .append (pureSteps_set hpr (by rw [herase]; exact hpure')) (pureSteps_refl _)

/-- Erasure preserves adequacy. -/
@[rocq_alias heap_lang.erasure]
theorem erasure {e : Exp} {σ : State} {φ : Val → State → Prop} (Had : adequate .NotStuck e σ φ) :
    adequate .NotStuck (eraseExpr e) (eraseState σ)
      (fun v σ => ∃ v' σ', eraseVal v' = v ∧ eraseState σ' = σ ∧ φ v' σ') := by
  refine ⟨?_, ?_⟩
  · intro t2 σ2 v2 hreach
    obtain ⟨t2'', σ2', hos, hσ, hpr⟩ := erasure_cut (ρ2 := (_, _)) Had hreach
    obtain ⟨e_head, t2''_rest, htp_eq, hp_head, _⟩ := List.exists_of_forall₂_cons hpr
    obtain ⟨la, eo, lb, rfl, hla, herase_eo, hmap_rest⟩ :=
      map_eq_append_cons (xs := []) (by show List.map eraseExpr t2'' = _; simpa [eraseTp] using htp_eq)
    obtain rfl : la = [] := by simpa using hla
    subst herase_eo
    have hv := Language.ReflTransGen_purePrimStep_val hp_head
    obtain ⟨v', hv', hve⟩ := toVal_erase_some hv
    obtain rfl := (coe_of_toVal_eq_some hv').symm
    exact ⟨v', σ2', hve, hσ.symm, Had.adequate_result _ _ _ hos⟩
  · intro t2 σ2 e2 _ hreach hel
    obtain ⟨t2'', σ2', hos, rfl, hpr⟩ := erasure_cut Had hreach
    exact pureStep_tp_safe (fun e2' he2' => Had.adequate_not_stuck _ _ _ rfl hos he2') hpr hel

end Iris.HeapLang
