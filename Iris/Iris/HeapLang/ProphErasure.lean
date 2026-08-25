module

public import Iris.HeapLang.Semantics
public import Iris.HeapLang.Instances
public import Iris.HeapLang.Notation
public import Iris.ProgramLogic.EctxiLanguage
public import Iris.ProgramLogic.Adequacy
public import Iris.Std.PartialMap

@[expose] public section
namespace Iris.HeapLang

open Std Iris.ProgramLogic Iris.ProgramLogic.Language Iris.ProgramLogic.PrimStep
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage
open FromMathlib
open Language.Notation EctxLanguage.Notation

/-! ## Erasure functions -/

@[rocq_alias erase_base_lit]
def eraseBaseLit : BaseLit → BaseLit
  | .prophecy _ => .poison
  | l => l

/-- Erasure of `Resolve` translates it into a projection out of a triple. -/
@[rocq_alias erase_resolve]
def eraseResolve (e0 e1 e2 : Exp) : Exp :=
  .fst (.fst (.pair (.pair e0 e1) e2))

/-- The erased form of `NewProph` — a stuck-free expression that reduces to `#LitPoison`. -/
@[rocq_alias erased_new_proph]
def erasedNewProph : Exp :=
  .app (.ofVal (.rec_ .anon .anon (.ofVal (.lit .poison)))) (.ofVal (.lit .unit))

mutual
  @[rocq_alias erase_expr]
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
  @[rocq_alias erase_val]
  def eraseVal : Val → Val
    | .lit l => .lit (eraseBaseLit l)
    | .rec_ f x e => .rec_ f x (eraseExpr e)
    | .pair v1 v2 => .pair (eraseVal v1) (eraseVal v2)
    | .injL v => .injL (eraseVal v)
    | .injR v => .injR (eraseVal v)
end

@[rocq_alias erase_ectx_item]
def eraseECtxItem : ECtxItem → List ECtxItem
  | .appL v2         => [.appL (eraseVal v2)]
  | .appR e1         => [.appR (eraseExpr e1)]
  | .unOp op         => [.unOp op]
  | .binOpL op v2    => [.binOpL op (eraseVal v2)]
  | .binOpR op e1    => [.binOpR op (eraseExpr e1)]
  | .if e1 e2        => [.if (eraseExpr e1) (eraseExpr e2)]
  | .pairL v2        => [.pairL (eraseVal v2)]
  | .pairR e1        => [.pairR (eraseExpr e1)]
  | .fst             => [.fst]
  | .snd             => [.snd]
  | .injL            => [.injL]
  | .injR            => [.injR]
  | .case e1 e2      => [.case (eraseExpr e1) (eraseExpr e2)]
  | .allocNL v2      => [.allocNL (eraseVal v2)]
  | .allocNR e1      => [.allocNR (eraseExpr e1)]
  | .free            => [.free]
  | .load            => [.load]
  | .storeL v2       => [.storeL (eraseVal v2)]
  | .storeR e1       => [.storeR (eraseExpr e1)]
  | .xchgL v2        => [.xchgL (eraseVal v2)]
  | .xchgR e1        => [.xchgR (eraseExpr e1)]
  | .cmpXchgL v1 v2  => [.cmpXchgL (eraseVal v1) (eraseVal v2)]
  | .cmpXchgM e0 v2  => [.cmpXchgM (eraseExpr e0) (eraseVal v2)]
  | .cmpXchgR e0 e1  => [.cmpXchgR (eraseExpr e0) (eraseExpr e1)]
  | .faaL v2         => [.faaL (eraseVal v2)]
  | .faaR e1         => [.faaR (eraseExpr e1)]
  | .resolveL K v1 v2 =>
      eraseECtxItem K ++
        [.pairL (eraseVal v1), .pairL (eraseVal v2), .fst, .fst]
  | .resolveM e0 v2 =>
      [.pairR (eraseExpr e0), .pairL (eraseVal v2), .fst, .fst]
  | .resolveR e0 e1 =>
      [.pairR (.pair (eraseExpr e0) (eraseExpr e1)), .fst, .fst]

@[rocq_alias erase_ectx]
def eraseECtx (K : List ECtxItem) : List ECtxItem :=
  K.flatMap eraseECtxItem

@[rocq_alias erase_tp]
def eraseTp (tp : List Exp) : List Exp := tp.map eraseExpr

/-- Erase the values contained in a heap. -/
@[rocq_alias erase_heap]
def eraseHeap (h : HeapF (Option Val)) : HeapF (Option Val) :=
  Iris.Std.PartialMap.map (fun (ov : Option Val) => eraseVal <$> ov) h

@[rocq_alias erase_state]
def eraseState (σ : State) : State :=
  { heap := eraseHeap σ.heap, usedProphId := ∅ }

@[rocq_alias erase_cfg]
def eraseCfg (ρ : List Exp × State) : List Exp × State :=
  (eraseTp ρ.1, eraseState ρ.2)

/-! ## Local tactic macros

`erase_simp` unfolds the erasure functions at a location; used pervasively when
inverting or normalising `eraseExpr`/`eraseVal` terms. -/

local macro "erase_simp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp
      [eraseExpr, eraseVal, eraseBaseLit, erasedNewProph, eraseResolve,
       eraseECtx, eraseECtxItem, ECtxItem.fill] $[$loc]?)

/-! ## Simple structural lemmas -/

@[simp] theorem eraseExpr_val (v : Val) : eraseExpr (.val v) = .val (eraseVal v) := rfl
@[simp] theorem eraseExpr_ofVal (v : Val) : eraseExpr (.ofVal v) = .ofVal (eraseVal v) := rfl

@[rocq_alias erase_ectx_app]
theorem eraseECtx_append (K K' : List ECtxItem) :
    eraseECtx (K ++ K') = eraseECtx K ++ eraseECtx K' := by
  simp [eraseECtx, List.flatMap_append]

@[rocq_alias erase_not_val]
theorem toVal_erase_none {e : Exp} (h : toVal e = none) : toVal (eraseExpr e) = none := by
  cases e <;> simp_all [ToVal.toVal, eraseExpr, erasedNewProph, eraseResolve]

@[rocq_alias erase_to_val]
theorem toVal_erase_some {e : Exp} {v : Val}
    (h : toVal (eraseExpr e) = some v) :
    ∃ v', toVal e = some v' ∧ eraseVal v' = v := by
  cases e
  case val w =>
    refine ⟨w, rfl, ?_⟩
    show eraseVal w = v
    have : toVal (Exp.val (eraseVal w)) = some (eraseVal w) := rfl
    rw [eraseExpr, this] at h
    exact Option.some.inj h
  all_goals exact absurd h (by simp [ToVal.toVal, eraseExpr, erasedNewProph, eraseResolve])

/-! ## Erasure and substitution -/

@[rocq_alias erase_expr_subst]
theorem eraseExpr_substStr (x : String) (v : Val) (e : Exp) :
    eraseExpr (e.substStr x v) = (eraseExpr e).substStr x (eraseVal v) := by
  induction e using Exp.rec (motive_2 := fun _ => True) with
  | val w => rfl
  | var x' => by_cases h : x == x' <;> simp [Exp.substStr, eraseExpr, h]
  | rec_ f x' e ih =>
    simp only [Exp.substStr, eraseExpr]
    by_cases h : .named x != f && .named x != x'
    · simp [h, ih]
    · simp [h]
  | resolve _ _ _ ih0 ih1 ih2 =>
    simp [Exp.substStr, eraseExpr, eraseResolve, ih0, ih1, ih2]
  | newProph => rfl
  | _ => simp_all [Exp.substStr, eraseExpr]

@[rocq_alias erase_expr_subst']
theorem eraseExpr_subst (x : Binder) (v : Val) (e : Exp) :
    eraseExpr (e.subst x v) = (eraseExpr e).subst x (eraseVal v) := by
  cases x with
  | anon => simp [Exp.subst]
  | named s => exact eraseExpr_substStr s v e

/-! ## Erasure and evaluation contexts -/

theorem eraseECtxItem_fill (Ki : ECtxItem) (e : Exp) :
    eraseExpr (Ki.fill e) = fill (eraseECtxItem Ki) (eraseExpr e) := by
  induction Ki generalizing e with
  | resolveL K v1 v2 IH =>
    simp [ECtxItem.fill, eraseECtxItem, eraseExpr, eraseResolve,
          fill_append, IH, fillItem, ECtxItem.fill]
  | _ =>
    simp [ECtxItem.fill, eraseECtxItem, eraseExpr, eraseResolve,
          fillItem, ECtxItem.fill]

@[rocq_alias erase_ectx_expr]
theorem eraseECtx_fill (K : List ECtxItem) (e : Exp) :
    eraseExpr (fill K e) = fill (eraseECtx K) (eraseExpr e) := by
  induction K using FromMathlib.List.reverseRec with
  | nil => simp [eraseECtx]
  | append_singleton Ks Ki ih =>
    rw [fill_append, fill_cons, fill_nil,
        show fillItem Ki = Ki.fill from rfl,
        eraseECtxItem_fill, eraseECtx_append, fill_append, ih]
    simp [eraseECtx]

/-! ## Erasure and comparison safety -/

theorem eraseBaseLit_isUnboxed (l : BaseLit) :
    (eraseBaseLit l).isUnboxed = l.isUnboxed := by
  cases l <;> rfl

@[rocq_alias val_is_unboxed_erased]
theorem eraseVal_isUnboxed (v : Val) :
    (eraseVal v).isUnboxed = v.isUnboxed := by
  cases v with
  | lit l => simp [eraseVal, Val.isUnboxed, eraseBaseLit_isUnboxed]
  | injL v =>
    cases v <;> simp [eraseVal, Val.isUnboxed, eraseBaseLit_isUnboxed]
  | injR v =>
    cases v <;> simp [eraseVal, Val.isUnboxed, eraseBaseLit_isUnboxed]
  | _ => rfl

@[rocq_alias vals_compare_safe_erase]
theorem eraseVal_compareSafe (v1 v2 : Val) :
    (eraseVal v1).compareSafe (eraseVal v2) = v1.compareSafe v2 := by
  simp [Val.compareSafe, eraseVal_isUnboxed]

private theorem eraseBaseLit_inj_of_unboxed {l1 l2 : BaseLit}
    (h : l1.isUnboxed = true ∨ l2.isUnboxed = true)
    (heq : eraseBaseLit l1 = eraseBaseLit l2) : l1 = l2 := by
  cases l1 <;> cases l2 <;>
    simp_all [eraseBaseLit, BaseLit.isUnboxed]

/-- Comparison-safe erased values are equal iff the originals are.  This is the
key lemma for handling `CmpXchg` and the `eq` binary operation. -/
@[rocq_alias erase_val_inj_iff]
theorem eraseVal_inj_iff {v1 v2 : Val} (h : v1.compareSafe v2 = true) :
    eraseVal v1 = eraseVal v2 ↔ v1 = v2 := by
  refine ⟨fun heq => ?_, congrArg _⟩
  simp only [Val.compareSafe, Bool.or_eq_true] at h
  cases v1 <;> cases v2 <;>
    simp_all [Val.isUnboxed, eraseVal]
  · -- lit / lit
    exact eraseBaseLit_inj_of_unboxed h heq
  · -- injL / injL
    rename_i v1 v2
    cases v1 <;> cases v2 <;> simp_all [eraseVal]
    exact eraseBaseLit_inj_of_unboxed h heq
  · -- injR / injR
    rename_i v1 v2
    cases v1 <;> cases v2 <;> simp_all [eraseVal]
    exact eraseBaseLit_inj_of_unboxed h heq

/-! ## Erasure and operator evaluation -/

@[rocq_alias un_op_eval_erase]
theorem UnOp.eval_erase {op : UnOp} {v v' : Val} :
    op.eval (eraseVal v) = some v' ↔
      ∃ w, op.eval v = some w ∧ eraseVal w = v' := by
  cases op <;> cases v <;>
    first
      | (rename_i l; cases l <;>
         simp [UnOp.eval, eraseVal, eraseBaseLit] <;>
         constructor <;> rintro ⟨w, h1, h2⟩ <;> subst_vars <;> simp_all)
      | (simp [UnOp.eval, eraseVal] <;> intro h <;> exact absurd h (by simp))
      | simp [UnOp.eval, eraseVal, eraseBaseLit]

/-- Helper: `.eq` is the only `BinOp` that depends on comparison safety. -/
private theorem BinOp.eq_eval_erase {v1 v2 v' : Val} :
    BinOp.eval .eq (eraseVal v1) (eraseVal v2) = some v' ↔
      ∃ w, BinOp.eval .eq v1 v2 = some w ∧ eraseVal w = v' := by
  simp only [BinOp.eval, eraseVal_compareSafe]
  by_cases h : v1.compareSafe v2 = true
  · rw [if_pos h, if_pos h]
    have hbeq : (eraseVal v1 == eraseVal v2) = (v1 == v2) := by
      by_cases heq : v1 = v2
      · subst heq; simp
      · have hne : eraseVal v1 ≠ eraseVal v2 := fun he => heq ((eraseVal_inj_iff h).mp he)
        rw [beq_false_of_ne hne, beq_false_of_ne heq]
    rw [hbeq]
    constructor
    · intro hv
      refine ⟨.lit (.bool (v1 == v2)), rfl, ?_⟩
      have := Option.some.inj hv
      simp [eraseVal, eraseBaseLit, ← this]
    · rintro ⟨w, hw, hwe⟩
      have := Option.some.inj hw
      subst this; simp [eraseVal, eraseBaseLit] at hwe; simp [← hwe]
  · rw [if_neg h, if_neg h]
    simp only [if_true, reduceCtorEq, false_iff]
    rintro ⟨_, hw, _⟩; exact absurd hw (by simp)

/-- An erased literal came from some literal, whose erasure it is. -/
private theorem eraseVal_eq_lit {v : Val} {l : BaseLit}
    (h : eraseVal v = .lit l) : ∃ l', v = .lit l' ∧ eraseBaseLit l' = l := by
  cases v <;> simp [eraseVal] at h
  cases h; exact ⟨_, rfl, rfl⟩

/-- Erasure rewrites only prophecy literals, and only to `poison`, so any other
erased literal came from that very literal. -/
private theorem eraseVal_eq_lit_of_ne_poison {v : Val} {l : BaseLit}
    (hne : l ≠ .poison) (h : eraseVal v = .lit l) : v = .lit l := by
  obtain ⟨l', rfl, hb⟩ := eraseVal_eq_lit h
  cases l' <;> simp_all [eraseBaseLit]

/-- Two erased values reducing under a `plus`/`minus`/etc. `BinOp` must have
been literal-int values. -/
private theorem eraseVal_lit_lit_of_eq {v1 v2 : Val} {l1 l2 : BaseLit}
    (h1 : eraseVal v1 = .lit l1) (h2 : eraseVal v2 = .lit l2) :
    ∃ l1' l2', v1 = .lit l1' ∧ v2 = .lit l2' ∧
      eraseBaseLit l1' = l1 ∧ eraseBaseLit l2' = l2 := by
  cases v1 <;> simp [eraseVal] at h1
  cases v2 <;> simp [eraseVal] at h2
  exact ⟨_, _, rfl, rfl, h1, h2⟩

/-- The forward direction of `BinOp.eval_erase` for non-`.eq` ops. -/
private theorem BinOp.eval_erase_mp {op : BinOp} {v1 v2 v' : Val}
    (hne : op ≠ .eq)
    (h : op.eval (eraseVal v1) (eraseVal v2) = some v') :
    ∃ w, op.eval v1 v2 = some w ∧ eraseVal w = v' := by
  match v1, v2 with
  | .lit l1, .lit l2 =>
    cases op <;> (try exact absurd rfl hne) <;>
      cases l1 <;> cases l2 <;>
      simp [eraseVal, eraseBaseLit, BinOp.eval, BinOp.evalInt, BinOp.evalBool, BinOp.evalLoc] at h <;>
      (first
        | (subst h; exact ⟨_, rfl, by simp [eraseVal, eraseBaseLit]⟩)
        | (obtain ⟨_, _⟩ := h; exact ⟨_, rfl, by simp [eraseVal, eraseBaseLit]⟩))
  | .lit _, .rec_ .. | .lit _, .pair .. | .lit _, .injL _ | .lit _, .injR _
  | .rec_ .., _ | .pair .., _ | .injL _, _ | .injR _, _ =>
    cases op <;> (try exact absurd rfl hne) <;>
      simp [eraseVal, BinOp.eval] at h

/-- The backward direction of `BinOp.eval_erase` for non-`.eq` ops. -/
private theorem BinOp.eval_erase_mpr {op : BinOp} {v1 v2 v' : Val}
    (hne : op ≠ .eq)
    (h : ∃ w, op.eval v1 v2 = some w ∧ eraseVal w = v') :
    op.eval (eraseVal v1) (eraseVal v2) = some v' := by
  obtain ⟨w, hw, hwe⟩ := h
  match v1, v2 with
  | .lit l1, .lit l2 =>
    cases op <;> (try exact absurd rfl hne) <;>
      cases l1 <;> cases l2 <;>
      simp [BinOp.eval, BinOp.evalInt, BinOp.evalBool, BinOp.evalLoc] at hw <;>
      (subst hw; subst hwe; simp [eraseVal, eraseBaseLit, BinOp.eval, BinOp.evalInt, BinOp.evalBool, BinOp.evalLoc])
  | .lit _, .rec_ .. | .lit _, .pair .. | .lit _, .injL _ | .lit _, .injR _
  | .rec_ .., _ | .pair .., _ | .injL _, _ | .injR _, _ =>
    cases op <;> (try exact absurd rfl hne) <;>
      simp [BinOp.eval] at hw

/-- Auxiliary lemma capturing that comparable literals stay comparable under erasure. -/
@[rocq_alias bin_op_eval_erase]
theorem BinOp.eval_erase {op : BinOp} {v1 v2 v' : Val} :
    op.eval (eraseVal v1) (eraseVal v2) = some v' ↔
      ∃ w, op.eval v1 v2 = some w ∧ eraseVal w = v' := by
  by_cases hne : op = .eq
  · subst hne; exact BinOp.eq_eval_erase
  · exact ⟨BinOp.eval_erase_mp hne, BinOp.eval_erase_mpr hne⟩

/-! ## Erasure of the heap -/

@[rocq_alias lookup_erase_heap]
theorem lookup_eraseHeap (h : HeapF (Option Val)) (l : Loc) :
    PartialMap.get? (M := HeapF) (eraseHeap h) l =
      (PartialMap.get? (M := HeapF) h l).map (fun ov => eraseVal <$> ov) := by
  unfold eraseHeap
  exact Iris.Std.LawfulPartialMap.get?_map (M := HeapF)

@[rocq_alias lookup_erase_heap_None]
theorem lookup_eraseHeap_none (h : HeapF (Option Val)) (l : Loc) :
    PartialMap.get? (M := HeapF) (eraseHeap h) l = none ↔
      PartialMap.get? (M := HeapF) h l = none := by
  rw [lookup_eraseHeap]; cases PartialMap.get? (M := HeapF) h l <;> simp

/-- Lean-side polymorphic version of Rocq's `erase_heap_insert_Some` /
`erase_heap_insert_None`. -/
@[rocq_alias erase_heap_insert_Some]
theorem eraseHeap_insert (h : HeapF (Option Val)) (l : Loc) (v : Option Val) :
    eraseHeap (Std.insert (M := HeapF) h l v) =
      Std.insert (M := HeapF) (eraseHeap h) l (eraseVal <$> v) := by
  unfold eraseHeap
  exact Iris.Std.LawfulPartialMap.map_insert (M := HeapF)

theorem eraseState_get? (σ : State) (l : Loc) :
    (eraseState σ).get? l = (σ.get? l).map (fun ov => eraseVal <$> ov) := by
  simp [State.get?, eraseState, lookup_eraseHeap]

theorem eraseState_get?_none (σ : State) (l : Loc) :
    (eraseState σ).get? l = none ↔ σ.get? l = none := by
  simp [State.get?, eraseState, lookup_eraseHeap_none]

/-- Erasure commutes with `initHeap`. -/
@[rocq_alias erase_state_init]
theorem eraseState_initHeap (σ : State) (l : Loc) (n : Int) (v : Option Val) :
    eraseState (σ.initHeap l n v) =
      (eraseState σ).initHeap l n (eraseVal <$> v) := by
  refine State.mk.injEq .. |>.mpr ⟨?_, rfl⟩
  refine Std.LawfulPartialMap.equiv_iff_eq (M := HeapF) |>.mp fun k => ?_
  show PartialMap.get? (M := HeapF) (eraseHeap _) k = _
  rw [lookup_eraseHeap]
  have h1 : PartialMap.get? (M := HeapF) (σ.initHeap l n v).heap k
            = if (∃ i, i < n.toNat ∧ k = l + (i : Int)) then some v
              else PartialMap.get? (M := HeapF) σ.heap k := by
    show PartialMap.get? (M := HeapF) ((List.range n.toNat).foldl _ σ.heap) k = _
    exact get?_foldl_insert l v σ.heap n.toNat k
  have h2 : PartialMap.get? (M := HeapF) ((eraseState σ).initHeap l n (eraseVal <$> v)).heap k
            = if (∃ i, i < n.toNat ∧ k = l + (i : Int))
              then some (eraseVal <$> v)
              else PartialMap.get? (M := HeapF) (eraseState σ).heap k := by
    show PartialMap.get? (M := HeapF) ((List.range n.toNat).foldl _ (eraseHeap σ.heap)) k = _
    exact get?_foldl_insert l (eraseVal <$> v) (eraseHeap σ.heap) n.toNat k
  rw [h1, h2]
  by_cases hex : (∃ i, i < n.toNat ∧ k = l + (i : Int))
  · rw [if_pos hex, if_pos hex]; rfl
  · rw [if_neg hex, if_neg hex]
    show Option.map _ (PartialMap.get? (M := HeapF) σ.heap k)
         = PartialMap.get? (M := HeapF) (eraseHeap σ.heap) k
    rw [lookup_eraseHeap]

/-! ## Erased base step corresponds to an original base step

The Coq notion `base_steps_to_erasure_of` predicates that when the erased
program takes a base step producing `(e2, σ2, efs)`, then the original program
takes some base step whose result erases to `(e2, σ2, efs)`. -/
@[rocq_alias base_steps_to_erasure_of]
def BaseStepsToErasureOf (e1 : Exp) (σ1 : State) (e2 : Exp) (σ2 : State)
    (efs : List Exp) : Prop :=
  ∃ κ' e2' σ2' efs',
    BaseStep e1 σ1 κ' e2' σ2' efs' ∧
      eraseExpr e2' = e2 ∧ eraseState σ2' = σ2 ∧ eraseTp efs' = efs

/-! ### Inversion helpers for `eraseExpr = ...` and `eraseVal = ...`

These lemmas let us peel a layer of erasure off in a single step, matching
the Rocq
```
repeat match goal with
| H : _ = erase_expr ?e |- _ => destruct e; simplify_eq/=
| H : _ = erase_val ?v |- _ => destruct v; simplify_eq/=
end
```
pattern. Each returns an "original" constructor witness. -/

private theorem eraseExpr_eq_val {e : Exp} {v : Val}
    (h : eraseExpr e = .val v) : ∃ w, e = .val w ∧ eraseVal w = v := by
  cases e <;> simp [eraseExpr, erasedNewProph, eraseResolve] at h
  cases h; exact ⟨_, rfl, rfl⟩

private theorem eraseVal_eq_pair {v : Val} {v1 v2 : Val}
    (h : eraseVal v = .pair v1 v2) :
    ∃ w1 w2, v = .pair w1 w2 ∧ eraseVal w1 = v1 ∧ eraseVal w2 = v2 := by
  cases v <;> simp [eraseVal] at h
  obtain ⟨rfl, rfl⟩ := h; exact ⟨_, _, rfl, rfl, rfl⟩

private theorem eraseVal_eq_injL {v : Val} {v1 : Val}
    (h : eraseVal v = .injL v1) :
    ∃ w1, v = .injL w1 ∧ eraseVal w1 = v1 := by
  cases v <;> simp [eraseVal] at h
  cases h; exact ⟨_, rfl, rfl⟩

private theorem eraseVal_eq_injR {v : Val} {v1 : Val}
    (h : eraseVal v = .injR v1) :
    ∃ w1, v = .injR w1 ∧ eraseVal w1 = v1 := by
  cases v <;> simp [eraseVal] at h
  cases h; exact ⟨_, rfl, rfl⟩

private theorem eraseVal_eq_rec {v : Val} {f x : Binder} {e : Exp}
    (h : eraseVal v = .rec_ f x e) :
    ∃ e', v = .rec_ f x e' ∧ eraseExpr e' = e := by
  cases v <;> simp [eraseVal] at h
  obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨_, rfl, rfl⟩

/-- Peel an erased-heap lookup: if the erased heap has `some (some v)`
at `l`, then the original heap has some `(some ov')` at `l` with
`eraseVal ov' = v`. -/
private theorem eraseState_get?_some_some {σ : State} {l : Loc} {v : Val}
    (hget : (eraseState σ).get? l = some (some v)) :
    ∃ ov', σ.get? l = some (some ov') ∧ eraseVal ov' = v := by
  rw [eraseState_get?] at hget
  cases horig : σ.get? l with
  | none => rw [horig] at hget; simp at hget
  | some ov =>
    rw [horig] at hget
    cases ov with
    | none => simp at hget
    | some ov' =>
      simp at hget
      exact ⟨ov', rfl, hget⟩

/-! ### Per-case helpers matching Rocq `erased_base_step_base_step_*` -/

#rocq_ignore erased_base_step_base_step_rec
  "The beta/`rec` case is proved inline in the `betaS` arm of `erased_baseStep_baseStep`; no standalone lemma is needed."

@[rocq_alias erased_base_step_base_step_NewProph]
private theorem erased_baseStep_baseStep_NewProph (σ : State) :
    BaseStepsToErasureOf .newProph σ (.val (.lit .poison)) (eraseState σ) [] := by
  obtain ⟨pf, Hpf⟩ := Std.List.fresh σ.usedProphId.toList
  have Hpf_contains : ¬ σ.usedProphId.contains pf :=
    fun hc => Hpf (Std.ExtTreeSet.mem_toList.mpr hc)
  exact ⟨_, _, _, _, .newProphS σ pf Hpf_contains, rfl, by simp [eraseState], rfl⟩

@[rocq_alias erased_base_step_base_step_AllocN]
private theorem erased_baseStep_baseStep_AllocN (n : Int) (v : Val) (σ : State)
    (l : Loc) (hpos : 0 < n)
    (hnone : ∀ i, 0 ≤ i → i < n → (eraseState σ).get? (l + i) = none) :
    BaseStepsToErasureOf (.allocN (.val (.lit (.int n))) (.val v)) σ
      (.val (.lit (.loc l)))
      ((eraseState σ).initHeap l n (some (eraseVal v))) [] := by
  refine ⟨_, _, _, _, .allocNS n v σ l hpos (fun i hi0 hin => ?_), rfl, ?_, rfl⟩
  · have := hnone i hi0 hin
    rw [eraseState_get?] at this
    cases hget : σ.get? (l + i) with
    | none => rfl
    | some ov => rw [hget] at this; simp at this
  · rw [eraseState_initHeap]; rfl

@[rocq_alias erased_base_step_base_step_Free]
private theorem erased_baseStep_baseStep_Free (l : Loc) (v : Val) (σ : State)
    (hget : (eraseState σ).get? l = some (some v)) :
    BaseStepsToErasureOf (.free (.val (.lit (.loc l)))) σ
      (.val (.lit .unit))
      ((eraseState σ).initHeap l 1 none) [] := by
  obtain ⟨ov', horig, _⟩ := eraseState_get?_some_some hget
  refine ⟨_, _, _, _, .freeS l ov' σ horig, rfl, ?_, rfl⟩
  rw [eraseState_initHeap]; rfl

@[rocq_alias erased_base_step_base_step_Load]
private theorem erased_baseStep_baseStep_Load (l : Loc) (σ : State) (v : Val)
    (hget : (eraseState σ).get? l = some (some v)) :
    BaseStepsToErasureOf (.load (.val (.lit (.loc l)))) σ (.val v)
      (eraseState σ) [] := by
  obtain ⟨ov', horig, hev⟩ := eraseState_get?_some_some hget
  exact ⟨_, _, _, _, .loadS l ov' σ horig, by simp [hev], rfl, rfl⟩

@[rocq_alias erased_base_step_base_step_Xchg]
private theorem erased_baseStep_baseStep_Xchg (l : Loc) (v w : Val) (σ : State)
    (hget : (eraseState σ).get? l = some (some v)) :
    BaseStepsToErasureOf (.xchg (.val (.lit (.loc l))) (.val w)) σ (.val v)
      ((eraseState σ).initHeap l 1 (some (eraseVal w))) [] := by
  obtain ⟨ov', horig, hev⟩ := eraseState_get?_some_some hget
  refine ⟨_, _, _, _, .xchgS l ov' w σ horig, ?_, ?_, rfl⟩
  · simp [hev]
  · rw [eraseState_initHeap]; rfl

@[rocq_alias erased_base_step_base_step_Store]
private theorem erased_baseStep_baseStep_Store (l : Loc) (v w : Val) (σ : State)
    (hget : (eraseState σ).get? l = some (some v)) :
    BaseStepsToErasureOf (.store (.val (.lit (.loc l))) (.val w)) σ
      (.val (.lit .unit))
      ((eraseState σ).initHeap l 1 (some (eraseVal w))) [] := by
  obtain ⟨ov', horig, _⟩ := eraseState_get?_some_some hget
  refine ⟨_, _, _, _, .storeS l ov' w σ horig, rfl, ?_, rfl⟩
  rw [eraseState_initHeap]; rfl

@[rocq_alias erased_base_step_base_step_CmpXchg]
private theorem erased_baseStep_baseStep_CmpXchg (l : Loc) (v w : Val) (σ : State)
    (vl : Val) (b : Bool)
    (hget : (eraseState σ).get? l = some (some vl))
    (hvl : vl.compareSafe (eraseVal v) = true)
    (hb : decide (vl = eraseVal v) = b) :
    BaseStepsToErasureOf (.cmpXchg (.val (.lit (.loc l))) (.val v) (.val w)) σ
      (.val (.pair vl (.lit (.bool b))))
      (if b then (eraseState σ).initHeap l 1 (some (eraseVal w))
       else eraseState σ) [] := by
  obtain ⟨ov', horig, hev⟩ := eraseState_get?_some_some hget
  have hcs' : ov'.compareSafe v = true := by
    rw [← eraseVal_compareSafe, hev]; exact hvl
  have hb' : decide (ov' = v) = b := by
    rw [← hb, ← hev, decide_eq_decide.mpr (eraseVal_inj_iff hcs')]
  refine ⟨_, _, _, _, .cmpXchgS l v w ov' σ b horig hcs' hb', ?_, ?_, rfl⟩
  · subst hev; rfl
  · split
    · rw [eraseState_initHeap]; rfl
    · rfl

@[rocq_alias erased_base_step_base_step_FAA]
private theorem erased_baseStep_baseStep_FAA (l : Loc) (n m : Int) (σ : State)
    (hget : (eraseState σ).get? l = some (some (.lit (.int n)))) :
    BaseStepsToErasureOf (.faa (.val (.lit (.loc l))) (.val (.lit (.int m)))) σ
      (.val (.lit (.int n)))
      ((eraseState σ).initHeap l 1 (some (.lit (.int (n + m))))) [] := by
  obtain ⟨ov', horig, hev⟩ := eraseState_get?_some_some hget
  -- Original heap value erases to `.lit (.int n)`, hence was that literal.
  obtain rfl := eraseVal_eq_lit_of_ne_poison (by simp) hev
  refine ⟨_, _, _, _, .faaS l n m σ horig, ?_, ?_, rfl⟩
  · simp [eraseVal, eraseBaseLit]
  · rw [eraseState_initHeap]; rfl

/-- `peel1 h` inverts one erasure equation `eraseExpr e = <erased shape>`,
recursing through conjunctions, and substitutes the result away. -/
local syntax "peel1 " ident : tactic
local macro_rules
  | `(tactic| peel1 $h) =>
    `(tactic|
      first
        | (obtain ⟨hx, hy⟩ := $h; peel1 hx; peel1 hy)
        | (obtain ⟨_, he, hv⟩ := eraseExpr_eq_val $h
           subst he
           first
             | (have hl := eraseVal_eq_lit_of_ne_poison (by simp) hv; subst hl)
             | (obtain ⟨_, _, hp, hq, hr⟩ := eraseVal_eq_pair hv; subst hp hq hr)
             | (obtain ⟨_, hp, hq⟩ := eraseVal_eq_injL hv; subst hp hq)
             | (obtain ⟨_, hp, hq⟩ := eraseVal_eq_injR hv; subst hp hq)
             | (obtain ⟨_, hp, hq⟩ := eraseVal_eq_rec hv; subst hp hq)
             | subst hv
             | skip)
        | subst $h
        | skip)

/-- `erase_peel e at h`: split on `e`, normalise the erasure, then peel `h`. -/
local macro "erase_peel " e:Lean.Parser.Tactic.elimTarget " at " h:ident : tactic =>
  `(tactic| (cases $e <;> erase_simp at $h:ident; peel1 $h))

/-- `erase_solve e at h`: peel the erasure equation, then close the goal — with
the `BaseStep` constructor matching the recovered original expression, or with
the per-case helper lemma for the steps that also reason about the heap. -/
local macro "erase_solve " e:Lean.Parser.Tactic.elimTarget " at " h:ident : tactic =>
  `(tactic|
    (erase_peel $e at $h
     try first
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
       | exact ⟨_, _, _, _, by constructor, by first | rfl | simp [eraseVal], rfl, rfl⟩))


/-- If the erased program makes a base step, so does the original program.

Mirrors the Rocq proof: peel off a layer of erasure at each level of the
inverted `BaseStep`, then defer to the corresponding per-case helper. -/
@[rocq_alias erased_base_step_base_step]
theorem erased_baseStep_baseStep {e1 : Exp} {σ1 : State}
    {κ : List Observation} {e2 : Exp} {σ2 : State} {efs : List Exp}
    (h : BaseStep (eraseExpr e1) (eraseState σ1) κ e2 σ2 efs) :
    BaseStepsToErasureOf e1 σ1 e2 σ2 efs := by
  generalize heq1 : eraseExpr e1 = e1e at h
  generalize heqσ : eraseState σ1 = σ1e at h
  subst heqσ
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
    -- Every other base step erases structurally: peel, then re-apply the
    -- corresponding original step.
    erase_solve e1 at heq1

/-! ## The `prim_step_matched_by_erased_steps` relation

A primitive step in the original program can be matched (up to a number of
deterministic pure steps in the erased program) by a step in the erased
program. -/
@[rocq_alias prim_step_matched_by_erased_steps]
def PrimStepMatchedByErasedSteps (e1 : Exp) (σ1 : State) (e2 : Exp)
    (σ2 : State) (efs : List Exp) : Prop :=
  ∃ e2' σ2' κ' efs' e2'',
    PrimStep.primStep (e1, σ1) κ' (e2', σ2', efs') ∧
      Relation.ReflTransGen PurePrimStep e2 e2'' ∧
      eraseExpr e2' = e2'' ∧ eraseState σ2' = σ2 ∧ eraseTp efs' = efs

@[rocq_alias prim_step_matched_by_erased_steps_ectx]
theorem PrimStepMatchedByErasedSteps.fill_ctx (K : List ECtxItem) {e1 : Exp}
    {σ1 : State} {e2 : Exp} {σ2 : State} {efs : List Exp}
    (h : PrimStepMatchedByErasedSteps e1 σ1 e2 σ2 efs) :
    PrimStepMatchedByErasedSteps (fill K e1) σ1
      (fill (eraseECtx K) e2) σ2 efs := by
  obtain ⟨e2', σ2', κ', efs', e2'', hstep, hpure, hex, hst, htp⟩ := h
  refine ⟨fill K e2', σ2', κ', efs', fill (eraseECtx K) e2'', ?_, ?_, ?_, hst, htp⟩
  · exact fill_primStep K hstep
  · exact ReflTransGen_pureStep_fill (K := (fill (eraseECtx K) ·)) hpure
  · rw [← hex, eraseECtx_fill]

/-! ### Helper lemmas for the induction on context length -/

/-- Any expression whose `toVal` is `none` filled into a context is not a value. -/
private theorem fill_not_val_ne_val {K : List ECtxItem} {e' : Exp} (w : Val)
    (hnv : toVal e' = none) : fill K e' ≠ (.val w : Exp) := by
  intro hw
  have : toVal (fill K e') = toVal (Exp.val w) := by rw [hw]
  rw [fill_not_val (K := K) hnv] at this
  simp [ToVal.toVal] at this

/-- A single evaluation-context frame can be stripped from a `NotStuck` obligation. -/
private theorem notStuck_of_frame {Ki : ECtxItem} {e : Exp} {σ : State}
    (h : PrimStep.NotStuck (Ki.fill e, σ)) : PrimStep.NotStuck (e, σ) :=
  Language.Context.notStuck_fill_inv (K := fill [Ki])
    (by simpa [fill_cons, fill_nil, fillItem] using h)

/-- Peel the outermost frame off an evaluation context: either the context is
empty, or it is `K' ++ [Ki]` and the expression is `Ki` filled with `fill K' e'`. -/
theorem fill_eq_snoc {e e' : Exp} {K : List ECtxItem} (heq : e = fill K e') :
    (K = [] ∧ e' = e) ∨ ∃ K' Ki, K = K' ++ [Ki] ∧ e = Ki.fill (fill K' e') := by
  cases K using FromMathlib.List.reverseRec with
  | nil => exact .inl ⟨rfl, heq.symm⟩
  | append_singleton Ks Ki _ =>
    rw [fill_append, fill_cons, fill_nil,
        show fillItem Ki = Ki.fill from rfl] at heq
    exact .inr ⟨Ks, Ki, rfl, heq⟩

/-- Inversion for a `Fst` head atop an evaluation context: either the context is
empty, or its outermost frame is `.fst`. -/
theorem fill_eq_fst {X e' : Exp} {K : List ECtxItem} (heq : Exp.fst X = fill K e') :
    (K = [] ∧ e' = .fst X) ∨ ∃ K', K = K' ++ [.fst] ∧ X = fill K' e' := by
  rcases fill_eq_snoc heq with h | ⟨Ks, Ki, rfl, hf⟩
  · exact .inl h
  · cases Ki with
    | fst => simp only [ECtxItem.fill, Exp.fst.injEq] at hf; exact .inr ⟨Ks, rfl, hf⟩
    | _ => simp only [ECtxItem.fill] at hf; cases hf

/-- Inversion for a `Pair` head atop an evaluation context: either the context is
empty, or its outermost frame is `.pairL` (hole left, right side already a value)
or `.pairR` (hole right). -/
theorem fill_eq_pair {X Y e' : Exp} {K : List ECtxItem} (heq : Exp.pair X Y = fill K e') :
    (K = [] ∧ e' = .pair X Y)
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
    (hnv : toVal e' = none)
    (heq : Exp.resolve e0 (.val v1) (.val v2) = fill K e') :
    (K = [] ∧ e' = .resolve e0 (.val v1) (.val v2))
    ∨ ∃ K' Ki, K = K' ++ [ECtxItem.resolveL Ki v1 v2] ∧ e0 = Ki.fill (fill K' e') := by
  rcases fill_eq_snoc heq with h | ⟨Ks, Ki, rfl, hf⟩
  · exact .inl h
  · have hne : ∀ (w : Val), fill Ks e' ≠ (.val w : Exp) :=
      fun w => fill_not_val_ne_val w hnv
    cases Ki with
    | resolveL ctx' u1 u2 =>
      simp only [ECtxItem.fill, Exp.resolve.injEq] at hf
      obtain ⟨h0, ⟨_⟩, ⟨_⟩⟩ := hf
      exact .inr ⟨Ks, ctx', rfl, h0⟩
    | resolveM =>
      simp only [ECtxItem.fill, Exp.resolve.injEq] at hf
      exact absurd hf.2.1.symm (hne _)
    | resolveR =>
      simp only [ECtxItem.fill, Exp.resolve.injEq] at hf
      exact absurd hf.2.2.symm (hne _)
    | _ => simp only [ECtxItem.fill] at hf; cases hf

/-- The upstream form of `fill_eq_resolve`, which drops the residual equation. -/
@[rocq_alias fill_to_resolve]
theorem fill_to_resolve {e0 : Exp} {v1 v2 : Val} {K : List ECtxItem} {e' : Exp}
    (hnv : toVal e' = none)
    (heq : Exp.resolve e0 (.val v1) (.val v2) = fill K e') :
    K = [] ∨ ∃ K' Ki, K = K' ++ [ECtxItem.resolveL Ki v1 v2] :=
  (fill_eq_resolve hnv heq).imp And.left fun ⟨K', Ki, hK, _⟩ => ⟨K', Ki, hK⟩



/-- `fill_frame k` closes an `erase_eq_fill_item` goal by naming the original
frame `k`; the payloads and the two erasure obligations follow. -/
local macro "fill_frame " k:term : tactic =>
  `(tactic| exact ⟨$k, _, rfl, by simp_all [eraseECtxItem], by simp_all⟩)

open Lean Elab Tactic Meta in
/-- `fill_frame!` is `fill_frame` with the frame read off the goal: `eraseECtxItem`
preserves a frame's constructor, so the original frame is the erased one's
constructor applied to fresh holes. -/
local elab "fill_frame!" : tactic => do
  let ctors := (← getConstInfoInduct ``ECtxItem).ctors
  let tgt ← instantiateMVars (← getMainTarget)
  let some ki := tgt.find? fun e =>
      match e.getAppFn with
      | .const c _ => ctors.contains c
      | _ => false
    | throwError "fill_frame!: no evaluation-context frame in the goal"
  let .const c _ := ki.getAppFn | throwError "fill_frame!: unexpected frame"
  let n := (← getConstInfoCtor c).numFields
  let holes : Array (TSyntax `term) ← (Array.range n).mapM fun _ => `(term| _)
  let stx ← `(term| $(mkIdent c):ident $holes*)
  evalTactic (← `(tactic| fill_frame $stx))

/-- Inversion for an erased evaluation-context frame: if `eraseExpr e1` is the
frame `Ki` filled with a non-value hole `X`, then `e1` itself decomposes into an
original frame erasing to `Ki`, unless `Ki = .fst` and `e1` is a `Resolve` (whose
erasure `.fst (.fst ((_, _), _))` also presents a `.fst` head). -/
theorem erase_eq_fill_item {e1 X : Exp} {Ki : ECtxItem} (hnv : toVal X = none)
    (heq : eraseExpr e1 = Ki.fill X) :
    (∃ Ki_orig einner, e1 = Ki_orig.fill einner
        ∧ eraseECtxItem Ki_orig = [Ki] ∧ eraseExpr einner = X)
    ∨ (Ki = .fst ∧ ∃ r0 r1 r2, e1 = .resolve r0 r1 r2) := by
  cases Ki <;> cases e1 <;>
    simp_all [eraseExpr, erasedNewProph, eraseResolve, ECtxItem.fill] <;>
    peel1 heq <;>
    first
      | fill_frame!
      | simp [ToVal.toVal] at hnv

/-- A single pure step, taken from a `PureExec` instance under the evaluation
context `K`. -/
private theorem pureStepIn (K : List ECtxItem) {e1 e2 : Exp}
    (h : PureExec True 1 e1 e2) : fill K e1 -ᵖ->* fill K e2 := by
  cases h.pureExec trivial with
  | tail _ hrfl hstep => cases hrfl; exact ReflTransGen_pureStep_fill _ (.single hstep)

/-- `Fst (Fst ((v0, v1), v2))` reduces to `v0` by four pure steps. -/
@[rocq_alias projs_pure_steps]
theorem projs_pure_steps (v0 v1 v2 : Val) :
    Relation.ReflTransGen PurePrimStep
      (eraseResolve (.val v0) (.val v1) (.val v2)) (.val v0) :=
  calc eraseResolve (.val v0) (.val v1) (.val v2)
    _ -ᵖ->* hl(fst(fst((v((&v0, &v1)), v(&v2))))) :=
        pureStepIn [.pairL v2, .fst, .fst] instPureExecPair
    _ -ᵖ->* hl(fst(fst(v(((&v0, &v1), &v2))))) := pureStepIn [.fst, .fst] instPureExecPair
    _ -ᵖ->* hl(fst(v((&v0, &v1)))) := pureStepIn [.fst] instPureExecFst
    _ -ᵖ->* hl(v(&v0)) := pureStepIn [] instPureExecFst

/-- `Resolve` applied to three values has no base step. -/
@[rocq_alias Resolve_3_vals_base_stuck]
theorem Resolve_3_vals_base_stuck (v0 v1 v2 : Val) (σ : State)
    (κ : List Observation) (e : Exp) (σ' : State) (efs : List Exp) :
    ¬ BaseStep (.resolve (.val v0) (.val v1) (.val v2)) σ κ e σ' efs := by
  intro h
  cases h with
  | resolveS _ _ _ _ _ _ _ _ hstep _ =>
    -- inner base step of a value; impossible.
    cases hstep

/-- `Resolve` on three values is not `NotStuck`. -/
@[rocq_alias Resolve_3_vals_unsafe]
theorem Resolve_3_vals_unsafe (v0 v1 v2 : Val) (σ : State) :
    ¬ PrimStep.NotStuck ((.resolve (.val v0) (.val v1) (.val v2) : Exp), σ) := by
  intro hns
  rcases hns with hval | ⟨obs, e', σ', eₜ, hstep⟩
  · simp [ToVal.toVal] at hval
  · -- Break down the ContextStep manually.
    generalize heq_e : (Exp.resolve (.val v0) (.val v1) (.val v2)) = ee at hstep
    rcases hstep with @⟨e1, e2, K, bstep⟩
    have hnv : toVal e1 = none := EctxItemLanguage.val_stuck bstep
    rcases fill_eq_resolve hnv heq_e with ⟨rfl, rfl⟩ | ⟨Ks, ctx, rfl, hh⟩
    · exact Resolve_3_vals_base_stuck _ _ _ _ _ _ _ _ bstep
    · -- A `.resolveL` frame would force the non-value hole to be a value.
      have hval_inner : (toVal (ctx.fill (fill Ks e1))).isSome := by
        rw [← hh]; simp [ToVal.toVal]
      have hval_inner2 : (toVal (fill Ks e1)).isSome :=
        EctxItemLanguage.fillItem_val (Ki := ctx) _ hval_inner
      rw [fill_not_val (K := Ks) hnv] at hval_inner2; simp at hval_inner2

/-- Helper for the `Resolve r0 r1 r2` sub-case of `erased_primStep_primStep`
under a `Ki = .fst` frame.  This handles the "carve-out" for `Resolve`
expressions, whose erasure `.fst (.fst (.pair (.pair X0 X1) X2))` matches
a top-level `.fst` frame.  Mirrors the second half of Rocq's
`prim_step_matched_by_erased_steps_ectx_item`. -/
private theorem resolve_fst_primStepMatched {r0 r1 r2 : Exp}
    {Ks : List ECtxItem} {e1' e2' : Exp} {σ1 σ2 : State}
    {κ : List Observation} {efs : List Exp}
    (bstep : BaseStep e1' (eraseState σ1) κ e2' σ2 efs)
    (hns : PrimStep.NotStuck ((.resolve r0 r1 r2 : Exp), σ1))
    (heq_e :
      (Exp.fst (.pair (.pair (eraseExpr r0) (eraseExpr r1))
                      (eraseExpr r2))) =
      fill Ks e1')
    (IHapp : ∀ {K' : List ECtxItem} {e0 : Exp}, K'.length ≤ Ks.length →
      eraseExpr e0 = fill K' e1' → PrimStep.NotStuck (e0, σ1) →
      PrimStepMatchedByErasedSteps e0 σ1 (fill K' e2') σ2 efs) :
    PrimStepMatchedByErasedSteps (.resolve r0 r1 r2) σ1
      (fill (Ks ++ [ECtxItem.fst]) e2') σ2 efs := by
  -- Peel the outermost frame off `Ks`: it must be the `.fst` of the erasure.
  rcases fill_eq_fst heq_e with ⟨rfl, rfl⟩ | ⟨Ks', hKs, heq_fst⟩
  · -- `Ks = []`: the hole is the whole `.fst _`, which admits no base step.
    cases bstep
  · -- Outermost frame is `.fst`; replace `heq_e` by the residual equation.
    subst hKs
    replace heq_e := heq_fst
    -- Peel the next frame off `Ks'`: only `.pairL`/`.pairR` give a `.pair` head.
    rcases fill_eq_pair heq_e with ⟨rfl, rfl⟩ | ⟨Ks'', v_r2, hKs, hv2, hinner⟩ |
        ⟨Ks'', hKs, hi⟩
    · -- `Ks' = []`: the hole is the whole pair, which admits no base step.
      cases bstep
    · -- `.pairL v_r2`: the right component is already a value.
      subst hKs
      have hv2r : toVal (eraseExpr r2) = some v_r2 := by
        rw [hv2]; rfl
      obtain ⟨w_r2, hw_r2_some, hew_r2⟩ := toVal_erase_some hv2r
      have hr2eq : r2 = .val w_r2 := (coe_of_toVal_eq_some hw_r2_some).symm
      subst hr2eq
      -- Peel the next frame off `Ks''`: again only `.pairL`/`.pairR` fit.
      rcases fill_eq_pair hinner with ⟨rfl, rfl⟩ | ⟨Ks''', v_r1, hKs3, hv1, hi⟩ |
          ⟨Ks''', hKs3, hi⟩
      · -- `Ks'' = []`: both components must then be values, contradicting `hns`.
        have hstep_val :
            ∀ {X Y : Exp} {σ0 κ0 e2f σ2f efsf},
              BaseStep (Exp.pair X Y) σ0 κ0 e2f σ2f efsf →
              ∃ vx vy, X = .val vx ∧ Y = .val vy := by
          intro X Y _ _ _ _ _ hb; cases hb
          rename_i _σx vx vy
          exact ⟨vx, vy, rfl, rfl⟩
        have := hstep_val bstep
        obtain ⟨v0, v1, h0, h1⟩ := this
        have hv0 : toVal (eraseExpr r0) = some v0 := by rw [h0]; rfl
        have hv1 : toVal (eraseExpr r1) = some v1 := by rw [h1]; rfl
        obtain ⟨w_r0, hw_r0_some, _⟩ := toVal_erase_some hv0
        obtain ⟨w_r1, hw_r1_some, _⟩ := toVal_erase_some hv1
        have hr0eq : r0 = .val w_r0 := (coe_of_toVal_eq_some hw_r0_some).symm
        have hr1eq : r1 = .val w_r1 := (coe_of_toVal_eq_some hw_r1_some).symm
        subst hr0eq; subst hr1eq
        exact absurd hns (Resolve_3_vals_unsafe _ _ _ _)
      · -- `.pairL v_r1`: the right component is already a value.
        subst hKs3
        have hv1r : toVal (eraseExpr r1) = some v_r1 := by
          rw [hv1]; rfl
        obtain ⟨w_r1, hw_r1_some, hew_r1⟩ := toVal_erase_some hv1r
        have hr1eq : r1 = .val w_r1 := (coe_of_toVal_eq_some hw_r1_some).symm
        subst hr1eq
        -- Derive NotStuck for r0 by decomposing hns.
        have hns_r0 : PrimStep.NotStuck (r0, σ1) := by
          rcases hns with hval | ⟨obs_h, e'_h, σ'_h, eₜ_h, hstep_h⟩
          · simp [ToVal.toVal] at hval
          generalize heq_gen :
              (Exp.resolve r0 (.val w_r1) (.val w_r2)) = ee_h at hstep_h
          rcases hstep_h with @⟨he1_h, he2_h, K_h, bs_h⟩
          have hnv_h : toVal he1_h = none :=
            EctxItemLanguage.val_stuck bs_h
          rcases fill_eq_resolve hnv_h heq_gen with ⟨rfl, rfl⟩ |
              ⟨K_rest, ctx, rfl, hr0_eq⟩
          · -- Hole is the whole `Resolve`: its base step is a `resolveS`.
            cases bs_h with
            | resolveS _ _ _ _ _ _ _ _ bs_inner _ =>
              right
              exact ⟨_, _, _, _, BaseStep.ContextStep.ofBaseStep [] bs_inner⟩
          · -- Outermost frame is a `.resolveL`; push it into the step context.
            right
            refine ⟨_, _, _, _,
              BaseStep.ContextStep.ofBaseStep' (K_rest ++ [ctx])
                (by rw [fill_append, fill_cons, fill_nil,
                        show fillItem ctx = ctx.fill from rfl,
                        ← hr0_eq]) rfl bs_h⟩
        have hlk : Ks'''.length ≤
            (Ks''' ++ [ECtxItem.pairL v_r1] ++
             [ECtxItem.pairL v_r2] ++ [ECtxItem.fst]).length := by
          simp
        have hmatch := IHapp hlk hi hns_r0
        obtain ⟨e_r0_next, σ_r0, κ_r0, efs_r0, e_matched,
                hstep_r0, hpure_r0, hex_r0, hσ_r0, hef_r0⟩ := hmatch
        subst hew_r1
        subst hew_r2
        obtain @⟨inner_e1, inner_e2, K_r0, hbstep_r0⟩ := hstep_r0
        cases K_r0 using FromMathlib.List.reverseRec with
        | nil =>
          simp only [fill_nil] at hbstep_r0 hex_r0 hns
          have hns_info :
              ∃ (p : ProphId) (v_hns : Val) (σ_hns : State)
                (κs_hns : List Observation) (ts_hns : List Exp),
                w_r1 = .lit (.prophecy p) ∧
                σ1.usedProphId.contains p ∧
                BaseStep inner_e1 σ1 κs_hns (.val v_hns) σ_hns ts_hns := by
            rcases hns with hval | ⟨_, _, _, _, hstep_h⟩
            · simp [ToVal.toVal] at hval
            generalize heq_h :
                (Exp.resolve inner_e1 (.val w_r1) (.val w_r2)) = ee_h
                at hstep_h
            rcases hstep_h with @⟨he1_h, he2_h, K_h, bs_h⟩
            have hnv_h : toVal he1_h = none :=
              EctxItemLanguage.val_stuck bs_h
            rcases fill_eq_resolve hnv_h heq_h with ⟨rfl, rfl⟩ |
                ⟨K_rest, ctx, rfl, hr0_eq⟩
            · -- Hole is the whole `Resolve`: its base step is a `resolveS`.
              match bs_h with
              | BaseStep.resolveS p v _ _ _ _ κs_r ts_r bs_inner hused =>
                exact ⟨p, v, _, κs_r, ts_r, rfl, hused, bs_inner⟩
            · -- A `.resolveL` frame would force the hole to be a value.
              exfalso
              have hbs_ctx :
                  BaseStep (ctx.fill (fill K_rest he1_h)) σ1
                    κ_r0 inner_e2 σ_r0 efs_r0 := hr0_eq ▸ hbstep_r0
              have hval_isSome : (toVal (fill K_rest he1_h)).isSome :=
                EctxItemLanguage.base_ctx_step_val hbs_ctx
              rcases Option.isSome_iff_exists.mp hval_isSome with ⟨w, hw⟩
              rw [fill_not_val (K := K_rest) hnv_h] at hw; cases hw
          obtain ⟨p, v_hns, σ_hns, κs_hns, ts_hns, hwr1_eq, hused,
                  bs_inner_hns⟩ := hns_info
          subst hwr1_eq
          have hval_target : ∃ v : Val, inner_e2 = .val v := by
            cases hbstep_r0 with
            | recS => exact ⟨_, rfl⟩
            | pairS => exact ⟨_, rfl⟩
            | injLS => exact ⟨_, rfl⟩
            | injRS => exact ⟨_, rfl⟩
            | betaS _ _ _ _ _ _ h =>
              cases bs_inner_hns with
              | betaS _ _ _ _ _ _ h' => exact ⟨v_hns, h.trans h'.symm⟩
            | unOpS => exact ⟨_, rfl⟩
            | binOpS => exact ⟨_, rfl⟩
            | ifTrueS => cases bs_inner_hns with
              | ifTrueS => exact ⟨v_hns, rfl⟩
            | ifFalseS => cases bs_inner_hns with
              | ifFalseS => exact ⟨v_hns, rfl⟩
            | fstS => exact ⟨_, rfl⟩
            | sndS => exact ⟨_, rfl⟩
            | caseLS => cases bs_inner_hns
            | caseRS => cases bs_inner_hns
            | allocNS => exact ⟨_, rfl⟩
            | freeS => exact ⟨_, rfl⟩
            | loadS => exact ⟨_, rfl⟩
            | storeS => exact ⟨_, rfl⟩
            | xchgS => exact ⟨_, rfl⟩
            | cmpXchgS => exact ⟨_, rfl⟩
            | faaS => exact ⟨_, rfl⟩
            | forkS => exact ⟨_, rfl⟩
            | newProphS => exact ⟨_, rfl⟩
            | resolveS => exact ⟨_, rfl⟩
          obtain ⟨v_target, hv_target⟩ := hval_target
          subst hv_target
          refine ⟨.val v_target, σ_r0, κ_r0 ++ [(p, (v_target, w_r2))],
                  efs_r0, .val (eraseVal v_target), ?_, ?_, ?_,
                  hσ_r0, hef_r0⟩
          · exact BaseStep.ContextStep.ofBaseStep []
              (BaseStep.resolveS p v_target inner_e1 σ1 w_r2 σ_r0
                κ_r0 efs_r0 hbstep_r0 hused)
          · have hlift :=
              ReflTransGen_pureStep_fill
                (K := fill (Expr := Exp)
                       [ECtxItem.pairL (eraseVal (.lit (.prophecy p))),
                        ECtxItem.pairL (eraseVal w_r2),
                        ECtxItem.fst, ECtxItem.fst])
                hpure_r0
            have hLHS_eq :
                fill [ECtxItem.pairL (eraseVal (.lit (.prophecy p))),
                      ECtxItem.pairL (eraseVal w_r2),
                      ECtxItem.fst, ECtxItem.fst]
                     (fill Ks''' e2') =
                fill (Ks''' ++
                      [ECtxItem.pairL (eraseVal (.lit (.prophecy p)))]
                           ++ [ECtxItem.pairL (eraseVal w_r2)]
                           ++ [ECtxItem.fst] ++ [ECtxItem.fst]) e2' := by
              simp [fill_append, fill_cons, fill_nil, fillItem,
                    ECtxItem.fill]
            have he_matched :
                e_matched = .val (eraseVal v_target) := by
              rw [← hex_r0]; rfl
            rw [hLHS_eq, he_matched] at hlift
            have hproj :=
              projs_pure_steps (eraseVal v_target)
                (eraseVal (.lit (.prophecy p)))
                (eraseVal w_r2)
            simp only [fill_cons, fill_nil, fillItem, ECtxItem.fill]
              at hlift
            exact hlift.trans hproj
          · rfl
        | append_singleton K_r0_rest Ki_r0_top _ =>
          have hfill_eq :
              fill (K_r0_rest ++ [ECtxItem.resolveL Ki_r0_top w_r1 w_r2])
                inner_e1 =
              Exp.resolve
                (fill (K_r0_rest ++ [Ki_r0_top]) inner_e1)
                (.val w_r1) (.val w_r2) := by
            rw [fill_append, fill_cons, fill_nil,
                show fillItem (ECtxItem.resolveL Ki_r0_top w_r1 w_r2)
                  = (ECtxItem.resolveL Ki_r0_top w_r1 w_r2).fill from rfl,
                fill_append, fill_cons, fill_nil,
                show fillItem Ki_r0_top = Ki_r0_top.fill from rfl]
            rfl
          have hfill_eq2 :
              fill (K_r0_rest ++ [ECtxItem.resolveL Ki_r0_top w_r1 w_r2])
                inner_e2 =
              Exp.resolve
                (fill (K_r0_rest ++ [Ki_r0_top]) inner_e2)
                (.val w_r1) (.val w_r2) := by
            rw [fill_append, fill_cons, fill_nil,
                show fillItem (ECtxItem.resolveL Ki_r0_top w_r1 w_r2)
                  = (ECtxItem.resolveL Ki_r0_top w_r1 w_r2).fill from rfl,
                fill_append, fill_cons, fill_nil,
                show fillItem Ki_r0_top = Ki_r0_top.fill from rfl]
            rfl
          refine ⟨Exp.resolve
                    (fill (K_r0_rest ++ [Ki_r0_top]) inner_e2)
                    (.val w_r1) (.val w_r2),
                  σ_r0, κ_r0, efs_r0,
                  eraseExpr (Exp.resolve
                    (fill (K_r0_rest ++ [Ki_r0_top]) inner_e2)
                    (.val w_r1) (.val w_r2)),
                  ?_, ?_, rfl, hσ_r0, hef_r0⟩
          · have hs :=
              BaseStep.ContextStep.ofBaseStep
                (K := K_r0_rest ++ [ECtxItem.resolveL Ki_r0_top w_r1 w_r2])
                hbstep_r0
            rw [hfill_eq, hfill_eq2] at hs
            exact hs
          · have hlift :=
              ReflTransGen_pureStep_fill
                (K := fill (Expr := Exp)
                       [ECtxItem.pairL (eraseVal w_r1),
                        ECtxItem.pairL (eraseVal w_r2),
                        ECtxItem.fst, ECtxItem.fst])
                hpure_r0
            have hLHS_pure :
                fill [ECtxItem.pairL (eraseVal w_r1),
                      ECtxItem.pairL (eraseVal w_r2),
                      ECtxItem.fst, ECtxItem.fst]
                     (fill Ks''' e2') =
                fill (Ks''' ++ [ECtxItem.pairL (eraseVal w_r1)]
                           ++ [ECtxItem.pairL (eraseVal w_r2)]
                           ++ [ECtxItem.fst] ++ [ECtxItem.fst]) e2' := by
              simp [fill_append, fill_cons, fill_nil, fillItem,
                    ECtxItem.fill]
            have hRHS_pure :
                fill [ECtxItem.pairL (eraseVal w_r1),
                      ECtxItem.pairL (eraseVal w_r2),
                      ECtxItem.fst, ECtxItem.fst] e_matched =
                eraseExpr (Exp.resolve
                            (fill (K_r0_rest ++ [Ki_r0_top]) inner_e2)
                            (.val w_r1) (.val w_r2)) := by
              rw [← hex_r0]
              simp [eraseExpr, eraseResolve, fill_cons, fill_nil,
                    fillItem, ECtxItem.fill]
            rw [hLHS_pure, hRHS_pure] at hlift
            exact hlift
      · -- `.pairR`: the hole is in the left component `eraseExpr r0`.
        subst hKs3
        have hns_r1 : PrimStep.NotStuck (r1, σ1) :=
          notStuck_of_frame (Ki := .resolveM r0 w_r2) (by simpa [ECtxItem.fill] using hns)
        have hlk : Ks'''.length ≤
            (Ks''' ++ [ECtxItem.pairR (eraseExpr r0)] ++
             [ECtxItem.pairL v_r2] ++ [ECtxItem.fst]).length := by
          simp
        have hmatch := IHapp hlk hi hns_r1
        subst hew_r2
        simpa [eraseECtx, eraseECtxItem, List.flatMap_cons, List.flatMap_nil,
               fill_append, fill_cons, fill_nil, fillItem, ECtxItem.fill]
          using hmatch.fill_ctx [ECtxItem.resolveM r0 w_r2]
    · -- `.pairR`: the hole is in the right component `eraseExpr r2`.
      subst hKs
      have hns_r2 : PrimStep.NotStuck (r2, σ1) :=
        notStuck_of_frame (Ki := .resolveR r0 r1) (by simpa [ECtxItem.fill] using hns)
      have hlk : Ks''.length ≤ (Ks'' ++ [ECtxItem.pairR
                    (.pair (eraseExpr r0) (eraseExpr r1))] ++
                    [ECtxItem.fst]).length := by
        simp
      have hmatch := IHapp hlk hi hns_r2
      simpa [eraseECtx, eraseECtxItem, List.flatMap_cons, List.flatMap_nil,
             fill_append, fill_cons, fill_nil, fillItem, ECtxItem.fill]
        using hmatch.fill_ctx [ECtxItem.resolveR r0 r1]

/-- Every primitive step of the erased program is matched by a primitive step
in the original program, possibly followed by some deterministic pure steps
in the erased program.

The full proof is a delicate induction on the length of the surrounding
evaluation context, with special handling for `Resolve` expressions. -/
@[rocq_alias erased_prim_step_prim_step]
theorem erased_primStep_primStep {e1 : Exp} {σ1 : State}
    {κ : List Observation} {e2 : Exp} {σ2 : State} {efs : List Exp}
    (h : PrimStep.primStep (eraseExpr e1, eraseState σ1) κ (e2, σ2, efs))
    (hns : PrimStep.NotStuck (e1, σ1)) :
    PrimStepMatchedByErasedSteps e1 σ1 e2 σ2 efs := by
  -- Extract the underlying base step under a context K.
  generalize heq_e : eraseExpr e1 = ee at h
  rcases h with @⟨e1', e2', K, bstep⟩
  -- Strong induction on `K.length`, generalizing `e1`.
  generalize hlen : K.length = len
  induction len using Nat.strongRecOn generalizing K e1 with
  | _ len IHlen =>
    cases K using FromMathlib.List.reverseRec with
    | nil =>
      -- Base step directly in erased program.
      simp only [fill_nil] at heq_e
      subst heq_e
      obtain ⟨κ', e2orig, σ2orig, efsorig, bs, he2, hσ, hef⟩ :=
        erased_baseStep_baseStep bstep
      refine ⟨e2orig, σ2orig, κ', efsorig, e2', ?_, ?_, he2, hσ, hef⟩
      · exact primStep_of_baseStep bs
      · exact Relation.ReflTransGen.refl
    | append_singleton Ks Ki revIH =>
      -- Non-empty context: e1 erases to `Ki.fill (fill Ks e1')`.
      rw [fill_append, fill_cons, fill_nil,
          show fillItem Ki = Ki.fill from rfl] at heq_e
      have hnv_inner : toVal (fill Ks e1') = none :=
        fill_not_val (K := Ks) (EctxItemLanguage.val_stuck bstep)
      -- The rewritten context has `Ks ++ [Ki]` length = Ks.length + 1.
      rw [List.length_append, List.length_cons, List.length_nil] at hlen
      -- The IH, specialized to strictly-smaller K'.  We package it so that
      -- for a subterm `e0 : Exp` and shorter `K'` with `eraseExpr e0 =
      -- fill K' e1'` (with `K'.length ≤ Ks.length`), we can apply `IHlen`.
      have IHapp : ∀ {K' : List ECtxItem} {e0 : Exp}, K'.length ≤ Ks.length →
          eraseExpr e0 = fill K' e1' → PrimStep.NotStuck (e0, σ1) →
          PrimStepMatchedByErasedSteps e0 σ1 (fill K' e2') σ2 efs := by
        intro K' e0 hlk he0 hns0
        exact IHlen K'.length (Nat.lt_of_le_of_lt hlk (by omega))
                hns0 he0 (K := K') rfl
      -- Clear the bookkeeping hypotheses and the reverseRec IH, so subsequent
      -- `cases` invocations don't get confused.
      clear hlen IHlen revIH
      -- Case-split on Ki (the outermost erased frame).
      -- Local helper: given the shape reconstruction `e1 = Ki'.fill einner`
      -- where `eraseExpr einner = fill Ks e1'`, produce the target result.
      have finish :
          ∀ (Ki_orig : ECtxItem) (einner : Exp),
            e1 = Ki_orig.fill einner →
            eraseExpr einner = fill Ks e1' →
            eraseECtxItem Ki_orig = [Ki] →
            PrimStepMatchedByErasedSteps e1 σ1
              (fill (Ks ++ [Ki]) e2') σ2 efs := by
        intro Ki_orig einner heo hi hek
        have hns0 : PrimStep.NotStuck (einner, σ1) := notStuck_of_frame (heo ▸ hns)
        have hmatch : PrimStepMatchedByErasedSteps einner σ1 (fill Ks e2') σ2 efs :=
          IHapp (Nat.le_refl _) hi hns0
        have hlift := hmatch.fill_ctx [Ki_orig]
        show PrimStepMatchedByErasedSteps e1 σ1 (fill (Ks ++ [Ki]) e2') σ2 efs
        rw [heo, fill_append]
        simp only [fill_cons, fill_nil, fillItem, eraseECtx, List.flatMap_cons,
                   List.flatMap_nil, List.append_nil, hek] at hlift ⊢
        exact hlift
      -- Recover the original frame and subexpression behind the erased frame.
      rcases erase_eq_fill_item hnv_inner heq_e with
        ⟨Ki_orig, einner, heo, hek, hi⟩ | ⟨rfl, r0, r1, r2, rfl⟩
      · exact finish Ki_orig einner heo hi hek
      · -- `Ki = .fst` with `e1` a `Resolve`: the erasure `.fst (.fst ((_,_),_))`
        -- collides with a genuine `.fst` frame; delegate to the carve-out.
        simp only [eraseExpr, eraseResolve, ECtxItem.fill, Exp.fst.injEq] at heq_e
        exact resolve_fst_primStepMatched bstep hns heq_e IHapp

/-! ## A base step in the original produces a prim step in the erased program -/

/-- Every base step in the original program is matched by at least one
primitive step in the erased program (whose result may differ by a bounded
number of deterministic pure steps). -/
@[rocq_alias base_step_erased_prim_step]
theorem baseStep_erased_primStep {e1 : Exp} {σ1 : State}
    {κ : List Observation} {e2 : Exp} {σ2 : State} {efs : List Exp}
    (h : BaseStep e1 σ1 κ e2 σ2 efs) :
    ∃ e2' σ2' efs',
      PrimStep.primStep (eraseExpr e1, eraseState σ1) [] (e2', σ2', efs') := by
  induction h with
  | recS f x e σ =>
    refine ⟨_, _, _, primStep_of_baseStep (.recS f x _ _)⟩
  | pairS v1 v2 σ =>
    refine ⟨_, _, _, primStep_of_baseStep (.pairS (eraseVal v1) (eraseVal v2) _)⟩
  | injLS v σ =>
    refine ⟨_, _, _, primStep_of_baseStep (.injLS (eraseVal v) _)⟩
  | injRS v σ =>
    refine ⟨_, _, _, primStep_of_baseStep (.injRS (eraseVal v) _)⟩
  | betaS f x e1 v2 e' σ heq =>
    refine ⟨_, _, _, primStep_of_baseStep (.betaS f x (eraseExpr e1) (eraseVal v2) _ _ rfl)⟩
  | unOpS op v v' σ hv =>
    have hv' : op.eval (eraseVal v) = some (eraseVal v') :=
      UnOp.eval_erase.mpr ⟨v', hv, rfl⟩
    refine ⟨_, _, _, primStep_of_baseStep (.unOpS op (eraseVal v) (eraseVal v') _ hv')⟩
  | binOpS op v1 v2 v' σ hv =>
    have hv' : op.eval (eraseVal v1) (eraseVal v2) = some (eraseVal v') :=
      BinOp.eval_erase.mpr ⟨v', hv, rfl⟩
    refine ⟨_, _, _, primStep_of_baseStep
      (.binOpS op (eraseVal v1) (eraseVal v2) (eraseVal v') _ hv')⟩
  | ifTrueS e1 e2 σ =>
    refine ⟨_, _, _, primStep_of_baseStep (.ifTrueS (eraseExpr e1) (eraseExpr e2) _)⟩
  | ifFalseS e1 e2 σ =>
    refine ⟨_, _, _, primStep_of_baseStep (.ifFalseS (eraseExpr e1) (eraseExpr e2) _)⟩
  | fstS v1 v2 σ =>
    refine ⟨_, _, _, primStep_of_baseStep (.fstS (eraseVal v1) (eraseVal v2) _)⟩
  | sndS v1 v2 σ =>
    refine ⟨_, _, _, primStep_of_baseStep (.sndS (eraseVal v1) (eraseVal v2) _)⟩
  | caseLS v e1 e2 σ =>
    refine ⟨_, _, _, primStep_of_baseStep (.caseLS (eraseVal v) (eraseExpr e1) (eraseExpr e2) _)⟩
  | caseRS v e1 e2 σ =>
    refine ⟨_, _, _, primStep_of_baseStep (.caseRS (eraseVal v) (eraseExpr e1) (eraseExpr e2) _)⟩
  | allocNS n v σ l hpos hnone =>
    refine ⟨_, _, _, primStep_of_baseStep (.allocNS n (eraseVal v) (eraseState σ) l hpos ?_)⟩
    intro i hi0 hin
    have := hnone i hi0 hin
    rw [eraseState_get?, this]; rfl
  | freeS l v σ hget =>
    refine ⟨_, _, _, primStep_of_baseStep (.freeS l (eraseVal v) (eraseState σ) ?_)⟩
    rw [eraseState_get?, hget]; rfl
  | loadS l v σ hget =>
    refine ⟨_, _, _, primStep_of_baseStep (.loadS l (eraseVal v) (eraseState σ) ?_)⟩
    rw [eraseState_get?, hget]; rfl
  | storeS l v w σ hget =>
    refine ⟨_, _, _, primStep_of_baseStep (.storeS l (eraseVal v) (eraseVal w) (eraseState σ) ?_)⟩
    rw [eraseState_get?, hget]; rfl
  | xchgS l v1 v2 σ hget =>
    refine ⟨_, _, _, primStep_of_baseStep
      (.xchgS l (eraseVal v1) (eraseVal v2) (eraseState σ) ?_)⟩
    rw [eraseState_get?, hget]; rfl
  | cmpXchgS l v1 v2 vl σ b hget hcs hb =>
    refine ⟨_, _, _, primStep_of_baseStep
      (.cmpXchgS l (eraseVal v1) (eraseVal v2) (eraseVal vl) (eraseState σ) b ?_ ?_ ?_)⟩
    · rw [eraseState_get?, hget]; rfl
    · rw [eraseVal_compareSafe]; exact hcs
    · rw [show decide (eraseVal vl = eraseVal v1) = decide (vl = v1) from
            decide_eq_decide.mpr (eraseVal_inj_iff hcs)]
      exact hb
  | faaS l i1 i2 σ hget =>
    refine ⟨_, _, _, primStep_of_baseStep (.faaS l i1 i2 (eraseState σ) ?_)⟩
    rw [eraseState_get?, hget]; rfl
  | forkS e σ =>
    refine ⟨_, _, _, primStep_of_baseStep (.forkS (eraseExpr e) _)⟩
  | newProphS σ p hp =>
    -- Erased NewProph is `(λ _, poison) ()`, which beta-reduces.
    refine ⟨_, _, _, primStep_of_baseStep
      (BaseStep.betaS (e1 := (.val (.lit .poison) : Exp))
        (f := .anon) (x := .anon) (v2 := .lit .unit)
        (σ := eraseState σ) (e' := _) rfl)⟩
  | resolveS p v e σ w σ' κs ts hstep hused ih =>
    -- Erased Resolve is a fst-fst projection out of a pair-of-pair.
    obtain ⟨e2', σ2', efs', hstep'⟩ := ih
    exact ⟨_, σ2', efs',
      fill_primStep (Ectx := List ECtxItem)
        [(.pairL (Val.lit .poison) : ECtxItem), .pairL (eraseVal w), .fst, .fst] hstep'⟩

/-- If the original expression is reducible, so is the erased one. -/
@[rocq_alias reducible_erased_reducible]
theorem reducible_erased_reducible {e : Exp} {σ : State}
    (h : PrimStep.Reducible (e, σ)) :
    PrimStep.Reducible (eraseExpr e, eraseState σ) := by
  obtain ⟨obs, e', σ', efs, ⟨bstep⟩⟩ := h
  rename_i e1 e2 K
  rw [eraseECtx_fill]
  obtain ⟨e2', σ2', efs', hstep⟩ := baseStep_erased_primStep bstep
  refine ⟨_, _, _, _, fill_primStep (eraseECtx K) hstep⟩

/-! ## Safety after pure steps in the erased thread pool -/

/-- Split a list mapped by `f`: if `l.map f = xs ++ y :: ys` then `l` factors
correspondingly. -/
private theorem List.map_eq_append_cons {α β : Type _} {f : α → β} :
    ∀ {l : List α} {xs : List β} {y : β} {ys : List β},
      l.map f = xs ++ y :: ys →
      ∃ la a lb, l = la ++ a :: lb ∧ la.map f = xs ∧ f a = y ∧ lb.map f = ys
  | [], xs, y, ys, h => by simp at h
  | a :: l, [], y, ys, h => by
    simp only [_root_.List.map_cons, _root_.List.nil_append, _root_.List.cons.injEq] at h
    exact ⟨[], a, l, rfl, rfl, h.1, h.2⟩
  | a :: l, x :: xs, y, ys, h => by
    simp only [_root_.List.map_cons, _root_.List.cons_append, _root_.List.cons.injEq] at h
    obtain ⟨la, a', lb, hl, hla, hfa, hlb⟩ := List.map_eq_append_cons h.2
    refine ⟨a :: la, a', lb, ?_, ?_, hfa, hlb⟩
    · simp [hl]
    · simp [_root_.List.map_cons, hla, h.1]

@[rocq_alias pure_step_tp_safe]
theorem pureStep_tp_safe {t1 t2 : List Exp} {e1 : Exp} {σ : State}
    (Ht2 : ∀ e2 ∈ t2, PrimStep.NotStuck (e2, σ))
    (Hpr : t1.Forall₂ (Relation.ReflTransGen PurePrimStep) (eraseTp t2))
    (Hmem : e1 ∈ t1) : PrimStep.NotStuck (e1, eraseState σ) := by
  -- Split `t1` at the position of `e1`, then walk through `Hpr`.
  obtain ⟨ps, ss, rfl⟩ := _root_.List.append_of_mem Hmem
  obtain ⟨l2, l2', hl2, hpr1, hpr2, hlen⟩ := List.exists_of_forall₂_append Hpr
  obtain ⟨e2, l2'', rfl, hpstep, _⟩ := List.exists_of_forall₂_cons hpr2
  -- Recover the original element `e2'` of `t2` at the split.
  obtain ⟨t2a, e2', t2b, rfl, _, rfl, _⟩ := List.map_eq_append_cons (f := eraseExpr) hl2
  -- The original element is not stuck.
  have hns : PrimStep.NotStuck (e2', σ) := Ht2 e2' (by simp)
  -- Case-analyse on `hpstep : e1 -ᵖ->* eraseExpr e2'`.
  rcases Relation.ReflTransGen.cases_head hpstep with heq | ⟨e', hpstep_first, _⟩
  · -- `e1 = eraseExpr e2'`. Split on `NotStuck`.
    subst heq
    rcases hns with hval | hred
    · -- `e2'` is a value ⇒ `eraseExpr e2'` is a value.
      left
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hval
      cases e2' <;> simp [ToVal.toVal] at hv
      rename_i w; subst hv
      rfl
    · -- `e2'` is reducible ⇒ `eraseExpr e2'` is reducible.
      exact .inr (reducible_erased_reducible hred)
  · -- `e1 -ᵖ-> e'`, so `e1` is reducible.
    exact .inr (reducible_of_reducibleNoObs (hpstep_first.safe _))

/-! ## Top-level erasure theorem -/

/-- Reflexivity of `PureSteps` on any list. -/
private theorem pureSteps_refl (t : List Exp) : Language.PureSteps t t := by
  induction t with
  | nil => exact List.Forall₂.nil
  | cons _ _ ih => exact List.Forall₂.cons Relation.ReflTransGen.refl ih

/-- Pointwise update of `PureSteps` at a given index. -/
private theorem pureSteps_set {t t' : List Exp} (h : Language.PureSteps t t')
    {i : Nat} {e' eo' : Exp}
    (hpure : Relation.ReflTransGen PurePrimStep e' eo') :
    Language.PureSteps (t.set i e') (t'.set i eo') := by
  induction h generalizing i with
  | nil => cases i <;> exact List.Forall₂.nil
  | @cons a b l1 l2 hab hl ih =>
    cases i with
    | zero => exact List.Forall₂.cons hpure hl
    | succ k => exact List.Forall₂.cons hab (ih (i := k))

/-- The cut lemma for `erasure`. Any reachable erased configuration comes
from an original configuration whose erasure `pure_steps` up to it. -/
private theorem erasure_cut {e : Exp} {σ : State} {φ : Val → State → Prop}
    (Had : adequate .NotStuck e σ φ)
    {ρ2 : List Exp × State}
    (h : Relation.ReflTransGen Language.ErasedStep ([eraseExpr e], eraseState σ) ρ2) :
    ∃ (t2'' : List Exp) (σ2' : State),
      Relation.ReflTransGen Language.ErasedStep ([e], σ) (t2'', σ2') ∧
      ρ2.2 = eraseState σ2' ∧
      Language.PureSteps ρ2.1 (eraseTp t2'') := by
  induction h with
  | refl =>
    exact ⟨[e], σ, Relation.ReflTransGen.refl, rfl, pureSteps_refl _⟩
  | @tail ρ_mid ρ2' _ hstep IH =>
    obtain ⟨t2, σ2⟩ := ρ2'
    obtain ⟨t2'', σ2', hos, hσ, hpr⟩ := IH
    obtain ⟨t3, σ3⟩ := ρ_mid
    simp only at hσ hpr
    rw [hσ] at hstep
    rcases Language.erasedStep_pureSteps hstep hpr with
      ⟨heqσ, hpstep⟩ | ⟨i, ei, eₜ, e', obs', hi1, hi2, rfl, hpstep⟩
    · -- Pure step; σ2 = eraseState σ2'.
      exact ⟨t2'', σ2', hos, heqσ.symm, hpstep⟩
    · -- Extension case.
      have hei_map : (eraseTp t2'')[i]? = some ei := hi2
      simp only [eraseTp, List.getElem?_map] at hei_map
      rcases hlookup : t2''[i]? with _ | eio
      · rw [hlookup] at hei_map; simp at hei_map
      rw [hlookup] at hei_map
      simp at hei_map
      subst hei_map
      have heio_ns : PrimStep.NotStuck (eio, σ2') :=
        Had.adequate_not_stuck _ _ _ rfl hos (List.mem_of_getElem? hlookup)
      obtain ⟨e2', σ2next, κ_ignore, efs', e2'', hstep', hpure', herase, hst, htp⟩ :=
        erased_primStep_primStep hpstep heio_ns
      refine ⟨t2''.set i e2' ++ efs', σ2next, ?_, hst.symm, ?_⟩
      · exact hos.tail ⟨_, Language.step_update_of_getElem? _ _ hlookup hstep'⟩
      · unfold eraseTp
        simp only [List.map_append, List.map_set]
        rw [← htp]
        refine List.Forall₂.append ?_ (pureSteps_refl _)
        have hpure_at : Relation.ReflTransGen PurePrimStep e' (eraseExpr e2') := by
          rw [herase]; exact hpure'
        exact pureSteps_set hpr hpure_at

/-- Erasure preserves adequacy. -/
@[rocq_alias erasure]
theorem erasure {e : Exp} {σ : State} {φ : Val → State → Prop}
    (Had : adequate .NotStuck e σ φ) :
    adequate .NotStuck (eraseExpr e) (eraseState σ)
      (fun v σ => ∃ v' σ', eraseVal v' = v ∧ eraseState σ' = σ ∧ φ v' σ') := by
  refine ⟨?_, ?_⟩
  · -- adequate_result
    intro t2 σ2 v2 hreach
    obtain ⟨t2'', σ2', hos, hσ, hpr⟩ := erasure_cut (ρ2 := (_, _)) Had hreach
    obtain ⟨e_head, t2''_rest, htp_eq, hp_head, _⟩ :=
      List.exists_of_forall₂_cons hpr
    -- eraseTp t2'' = e_head :: t2''_rest.
    obtain ⟨la, eo, lb, rfl, hla, herase_eo, hmap_rest⟩ :=
      List.map_eq_append_cons (f := eraseExpr) (l := t2'') (xs := [])
        (y := e_head) (ys := t2''_rest)
        (by show List.map eraseExpr t2'' = _; simpa [eraseTp] using htp_eq)
    -- la = []; eraseExpr eo = e_head; lb = t2''_rest
    have hla_nil : la = [] := by
      have := hla
      cases la <;> simp at this
      rfl
    subst hla_nil; subst herase_eo
    -- hp_head : (val v2 : Exp) -ᵖ->* eraseExpr eo
    have hv := Language.ReflTransGen_purePrimStep_val
      (v := v2) (e := eraseExpr eo) hp_head
    obtain ⟨v', hv', hve⟩ := toVal_erase_some hv
    have heo : eo = .val v' := by
      cases eo <;> simp [ToVal.toVal] at hv'
      simp [hv']
    subst heo
    -- hos : ([e], σ) -·->* (val v' :: lb, σ2')
    have hofVal : (ToVal.ofVal v' : Exp) = .val v' := rfl
    rw [← hofVal] at hos
    exact ⟨v', σ2', hve, hσ.symm, Had.adequate_result _ _ _ hos⟩
  · -- adequate_not_stuck
    intro t2 σ2 e2 _ hreach hel
    obtain ⟨t2'', σ2', hos, rfl, hpr⟩ := erasure_cut Had hreach
    apply pureStep_tp_safe (t1 := t2) (t2 := t2'') (σ := σ2')
    · intro e2' he2'
      exact Had.adequate_not_stuck _ _ _ rfl hos he2'
    · exact hpr
    · exact hel

end Iris.HeapLang
