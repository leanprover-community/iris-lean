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

/-! ## Local tactic macros

`erase_simp` unfolds the erasure functions at a location; used pervasively when
inverting or normalising `eraseExpr`/`eraseVal` terms.

`erase_peel` iteratively destructs any hypothesis of the form
`eraseExpr e = ...` or `eraseVal v = ...`, mirroring the Rocq
`repeat match goal with ... end` pattern in `erased_base_step_base_step`. -/

set_option hygiene false in
local macro "erase_simp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp
      [eraseExpr, eraseVal, eraseBaseLit, erasedNewProph, eraseResolve,
       eraseECtx, eraseECtxItem, ECtxItem.fill] $[$loc]?)

-- `peel_ki`: standard boilerplate for per-`Ki` case in `erased_primStep_primStep`.
-- Unfolds `ECtxItem.fill` in `heq_e` and case-splits on the original expression
-- `e1`, discharging shapes whose erasure cannot equal the current frame.
set_option hygiene false in
local macro "peel_ki" : tactic =>
  `(tactic|
    (simp only [ECtxItem.fill] at heq_e
     cases e1 <;> erase_simp at heq_e))

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
  | app _ _ ih1 ih2 => simp [Exp.substStr, eraseExpr, ih1, ih2]
  | unop _ _ ih => simp [Exp.substStr, eraseExpr, ih]
  | binop _ _ _ ih1 ih2 => simp [Exp.substStr, eraseExpr, ih1, ih2]
  | «if» _ _ _ ih0 ih1 ih2 => simp [Exp.substStr, eraseExpr, ih0, ih1, ih2]
  | pair _ _ ih1 ih2 => simp [Exp.substStr, eraseExpr, ih1, ih2]
  | fst _ ih => simp [Exp.substStr, eraseExpr, ih]
  | snd _ ih => simp [Exp.substStr, eraseExpr, ih]
  | injL _ ih => simp [Exp.substStr, eraseExpr, ih]
  | injR _ ih => simp [Exp.substStr, eraseExpr, ih]
  | case _ _ _ ih0 ih1 ih2 => simp [Exp.substStr, eraseExpr, ih0, ih1, ih2]
  | allocN _ _ ih1 ih2 => simp [Exp.substStr, eraseExpr, ih1, ih2]
  | free _ ih => simp [Exp.substStr, eraseExpr, ih]
  | load _ ih => simp [Exp.substStr, eraseExpr, ih]
  | store _ _ ih1 ih2 => simp [Exp.substStr, eraseExpr, ih1, ih2]
  | cmpXchg _ _ _ ih0 ih1 ih2 => simp [Exp.substStr, eraseExpr, ih0, ih1, ih2]
  | xchg _ _ ih1 ih2 => simp [Exp.substStr, eraseExpr, ih1, ih2]
  | faa _ _ ih1 ih2 => simp [Exp.substStr, eraseExpr, ih1, ih2]
  | fork _ ih => simp [Exp.substStr, eraseExpr, ih]
  | newProph => rfl
  | resolve _ _ _ ih0 ih1 ih2 =>
    simp [Exp.substStr, eraseExpr, eraseResolve, ih0, ih1, ih2]
  | _ => trivial

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

/-- If erased literal is `.int n`, then original was `.int n`. -/
private theorem eraseBaseLit_eq_int {l : BaseLit} {n : Int}
    (h : eraseBaseLit l = .int n) : l = .int n := by
  cases l <;> simp [eraseBaseLit] at h <;> simp_all

private theorem eraseBaseLit_eq_bool {l : BaseLit} {b : Bool}
    (h : eraseBaseLit l = .bool b) : l = .bool b := by
  cases l <;> simp [eraseBaseLit] at h <;> simp_all

private theorem eraseBaseLit_eq_loc {l : BaseLit} {loc : Loc}
    (h : eraseBaseLit l = .loc loc) : l = .loc loc := by
  cases l <;> simp [eraseBaseLit] at h <;> simp_all

private theorem eraseVal_eq_lit_int {v : Val} {n : Int}
    (h : eraseVal v = .lit (.int n)) : v = .lit (.int n) := by
  cases v <;> simp [eraseVal] at h
  rename_i l; rw [eraseBaseLit_eq_int h]

private theorem eraseVal_eq_lit_bool {v : Val} {b : Bool}
    (h : eraseVal v = .lit (.bool b)) : v = .lit (.bool b) := by
  cases v <;> simp [eraseVal] at h
  rename_i l; rw [eraseBaseLit_eq_bool h]

private theorem eraseVal_eq_lit_loc {v : Val} {loc : Loc}
    (h : eraseVal v = .lit (.loc loc)) : v = .lit (.loc loc) := by
  cases v <;> simp [eraseVal] at h
  rename_i l; rw [eraseBaseLit_eq_loc h]

/-- `eraseVal` acts as the identity on `int`, `bool`, `loc`, `unit` literals. -/
private theorem eraseVal_lit_of_ne_proph {l : BaseLit}
    (h : ¬ ∃ p, l = .prophecy p) : eraseVal (.lit l) = .lit l := by
  cases l <;> simp [eraseVal, eraseBaseLit]
  case prophecy p => exact absurd ⟨p, rfl⟩ h

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

private theorem eraseVal_eq_lit {v : Val} {l : BaseLit}
    (h : eraseVal v = .lit l) : ∃ l', v = .lit l' ∧ eraseBaseLit l' = l := by
  cases v <;> simp [eraseVal] at h
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

-- (eraseBaseLit_eq_bool, eraseBaseLit_eq_int, eraseBaseLit_eq_loc are defined above.)

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

@[rocq_alias erased_base_step_base_step_rec]
private theorem erased_baseStep_baseStep_rec (f x : Binder) (e : Exp) (v : Val)
    (σ : State) :
    BaseStepsToErasureOf (.app (.val (.rec_ f x e)) (.val v)) σ
      (((eraseExpr e).subst f (Val.rec_ f x (eraseExpr e))).subst x (eraseVal v))
      (eraseState σ) [] :=
  ⟨_, _, _, _, .betaS f x e v _ σ rfl, by simp [eraseExpr_subst, eraseVal], rfl, rfl⟩

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
  -- Original heap value erases to `.lit (.int n)`.
  obtain ⟨l', hlit, hbe⟩ := eraseVal_eq_lit hev
  subst hlit
  have hn : l' = .int n := eraseBaseLit_eq_int hbe
  subst hn
  refine ⟨_, _, _, _, .faaS l n m σ horig, ?_, ?_, rfl⟩
  · simp [eraseVal, eraseBaseLit]
  · rw [eraseState_initHeap]; rfl

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
  | recS f x e σ =>
    cases e1 <;> erase_simp at heq1
    obtain ⟨rfl, rfl, rfl⟩ := heq1
    rename_i f' x' e'
    refine ⟨_, _, _, _, .recS f' x' e' σ1, ?_, rfl, rfl⟩
    simp [eraseVal]
  | pairS v1 v2 σ =>
    cases e1 <;> erase_simp at heq1
    obtain ⟨hv1, hv2⟩ := heq1
    obtain ⟨w1, rfl, rfl⟩ := eraseExpr_eq_val hv1
    obtain ⟨w2, rfl, rfl⟩ := eraseExpr_eq_val hv2
    exact ⟨_, _, _, _, .pairS w1 w2 σ1, rfl, rfl, rfl⟩
  | injLS v σ =>
    cases e1 <;> erase_simp at heq1
    obtain ⟨w, rfl, rfl⟩ := eraseExpr_eq_val heq1
    exact ⟨_, _, _, _, .injLS w σ1, rfl, rfl, rfl⟩
  | injRS v σ =>
    cases e1 <;> erase_simp at heq1
    obtain ⟨w, rfl, rfl⟩ := eraseExpr_eq_val heq1
    exact ⟨_, _, _, _, .injRS w σ1, rfl, rfl, rfl⟩
  | betaS f x e0 v2 e' σ heq =>
    cases e1 <;> erase_simp at heq1
    case app ef ea =>
      obtain ⟨hf, ha⟩ := heq1
      obtain ⟨wf, rfl, hef⟩ := eraseExpr_eq_val hf
      obtain ⟨body, rfl, hbody⟩ := eraseVal_eq_rec hef
      obtain ⟨w2, rfl, rfl⟩ := eraseExpr_eq_val ha
      exact ⟨_, _, _, _, .betaS _ _ _ w2 _ σ1 rfl, by
        simp [heq, ← hbody, eraseExpr_subst, eraseVal], rfl, rfl⟩
    case newProph =>
      obtain ⟨hf, ha⟩ := heq1
      obtain ⟨_, _, _, _, hs, he2, hσ, hef⟩ := erased_baseStep_baseStep_NewProph σ1
      cases hf; cases ha; subst heq
      exact ⟨_, _, _, _, hs, he2, hσ, hef⟩
  | unOpS op v v' σ hv =>
    cases e1 <;> erase_simp at heq1
    obtain ⟨rfl, hv1⟩ := heq1
    obtain ⟨w, rfl, rfl⟩ := eraseExpr_eq_val hv1
    obtain ⟨w', hw, hwe⟩ := UnOp.eval_erase.mp hv
    exact ⟨_, _, _, _, .unOpS _ w w' σ1 hw, by simp [hwe], rfl, rfl⟩
  | binOpS op v1 v2 v' σ hv =>
    cases e1 <;> erase_simp at heq1
    obtain ⟨rfl, hv1, hv2⟩ := heq1
    obtain ⟨w1, rfl, rfl⟩ := eraseExpr_eq_val hv1
    obtain ⟨w2, rfl, rfl⟩ := eraseExpr_eq_val hv2
    obtain ⟨w', hw, hwe⟩ := BinOp.eval_erase.mp hv
    exact ⟨_, _, _, _, .binOpS _ w1 w2 w' σ1 hw, by simp [hwe], rfl, rfl⟩
  | ifTrueS e1' e2' σ =>
    cases e1 <;> erase_simp at heq1
    obtain ⟨hc, rfl, rfl⟩ := heq1
    obtain ⟨w, rfl, hw⟩ := eraseExpr_eq_val hc
    obtain ⟨l, rfl, hl⟩ := eraseVal_eq_lit hw
    have : l = .bool true := eraseBaseLit_eq_bool hl
    subst this
    exact ⟨_, _, _, _, .ifTrueS _ _ σ1, rfl, rfl, rfl⟩
  | ifFalseS e1' e2' σ =>
    cases e1 <;> erase_simp at heq1
    obtain ⟨hc, rfl, rfl⟩ := heq1
    obtain ⟨w, rfl, hw⟩ := eraseExpr_eq_val hc
    obtain ⟨l, rfl, hl⟩ := eraseVal_eq_lit hw
    have : l = .bool false := eraseBaseLit_eq_bool hl
    subst this
    exact ⟨_, _, _, _, .ifFalseS _ _ σ1, rfl, rfl, rfl⟩
  | fstS v1 v2 σ =>
    cases e1 <;> erase_simp at heq1
    obtain ⟨w, rfl, hw⟩ := eraseExpr_eq_val heq1
    obtain ⟨u1, u2, rfl, rfl, rfl⟩ := eraseVal_eq_pair hw
    exact ⟨_, _, _, _, .fstS u1 u2 σ1, rfl, rfl, rfl⟩
  | sndS v1 v2 σ =>
    cases e1 <;> erase_simp at heq1
    obtain ⟨w, rfl, hw⟩ := eraseExpr_eq_val heq1
    obtain ⟨u1, u2, rfl, rfl, rfl⟩ := eraseVal_eq_pair hw
    exact ⟨_, _, _, _, .sndS u1 u2 σ1, rfl, rfl, rfl⟩
  | caseLS v e1' e2' σ =>
    cases e1 <;> erase_simp at heq1
    obtain ⟨hc, rfl, rfl⟩ := heq1
    obtain ⟨w, rfl, hw⟩ := eraseExpr_eq_val hc
    obtain ⟨inner, rfl, rfl⟩ := eraseVal_eq_injL hw
    exact ⟨_, _, _, _, .caseLS inner _ _ σ1, rfl, rfl, rfl⟩
  | caseRS v e1' e2' σ =>
    cases e1 <;> erase_simp at heq1
    obtain ⟨hc, rfl, rfl⟩ := heq1
    obtain ⟨w, rfl, hw⟩ := eraseExpr_eq_val hc
    obtain ⟨inner, rfl, rfl⟩ := eraseVal_eq_injR hw
    exact ⟨_, _, _, _, .caseRS inner _ _ σ1, rfl, rfl, rfl⟩
  | allocNS n v σ l hpos hnone =>
    cases e1 <;> erase_simp at heq1
    obtain ⟨hn, hv⟩ := heq1
    obtain ⟨wn, rfl, hwn⟩ := eraseExpr_eq_val hn
    obtain ⟨lit, rfl, hlit⟩ := eraseVal_eq_lit hwn
    have := eraseBaseLit_eq_int hlit; subst this
    obtain ⟨wv, rfl, rfl⟩ := eraseExpr_eq_val hv
    exact erased_baseStep_baseStep_AllocN n wv σ1 l hpos hnone
  | freeS l v σ hget =>
    cases e1 <;> erase_simp at heq1
    obtain ⟨wl, rfl, hwl⟩ := eraseExpr_eq_val heq1
    obtain ⟨lit, rfl, hlit⟩ := eraseVal_eq_lit hwl
    have := eraseBaseLit_eq_loc hlit; subst this
    exact erased_baseStep_baseStep_Free l v σ1 hget
  | loadS l v σ hget =>
    cases e1 <;> erase_simp at heq1
    obtain ⟨wl, rfl, hwl⟩ := eraseExpr_eq_val heq1
    obtain ⟨lit, rfl, hlit⟩ := eraseVal_eq_lit hwl
    have := eraseBaseLit_eq_loc hlit; subst this
    exact erased_baseStep_baseStep_Load l σ1 v hget
  | storeS l v w σ hget =>
    cases e1 <;> erase_simp at heq1
    obtain ⟨hel, hew⟩ := heq1
    obtain ⟨wl, rfl, hwl⟩ := eraseExpr_eq_val hel
    obtain ⟨lit, rfl, hlit⟩ := eraseVal_eq_lit hwl
    have := eraseBaseLit_eq_loc hlit; subst this
    obtain ⟨ww, rfl, rfl⟩ := eraseExpr_eq_val hew
    exact erased_baseStep_baseStep_Store l v ww σ1 hget
  | xchgS l v1 v2 σ hget =>
    cases e1 <;> erase_simp at heq1
    obtain ⟨hel, hew⟩ := heq1
    obtain ⟨wl, rfl, hwl⟩ := eraseExpr_eq_val hel
    obtain ⟨lit, rfl, hlit⟩ := eraseVal_eq_lit hwl
    have := eraseBaseLit_eq_loc hlit; subst this
    obtain ⟨ww, rfl, rfl⟩ := eraseExpr_eq_val hew
    exact erased_baseStep_baseStep_Xchg l v1 ww σ1 hget
  | cmpXchgS l v1 v2 vl σ b hget hcs hb =>
    cases e1 <;> erase_simp at heq1
    obtain ⟨hel, hev1, hev2⟩ := heq1
    obtain ⟨wl, rfl, hwl⟩ := eraseExpr_eq_val hel
    obtain ⟨lit, rfl, hlit⟩ := eraseVal_eq_lit hwl
    have := eraseBaseLit_eq_loc hlit; subst this
    obtain ⟨w1, rfl, rfl⟩ := eraseExpr_eq_val hev1
    obtain ⟨w2, rfl, rfl⟩ := eraseExpr_eq_val hev2
    exact erased_baseStep_baseStep_CmpXchg l w1 w2 σ1 vl b hget hcs hb
  | faaS l i1 i2 σ hget =>
    cases e1 <;> erase_simp at heq1
    obtain ⟨hel, hei⟩ := heq1
    obtain ⟨wl, rfl, hwl⟩ := eraseExpr_eq_val hel
    obtain ⟨litl, rfl, hlitl⟩ := eraseVal_eq_lit hwl
    have := eraseBaseLit_eq_loc hlitl; subst this
    obtain ⟨wi, rfl, hwi⟩ := eraseExpr_eq_val hei
    obtain ⟨liti, rfl, hliti⟩ := eraseVal_eq_lit hwi
    have := eraseBaseLit_eq_int hliti; subst this
    exact erased_baseStep_baseStep_FAA l i1 i2 σ1 hget
  | forkS e σ =>
    cases e1 <;> erase_simp at heq1
    subst heq1
    exact ⟨_, _, _, _, .forkS _ σ1, rfl, rfl, rfl⟩
  | newProphS σ p hp =>
    cases e1 <;> erase_simp at heq1
  | resolveS p v e σ w σ' κs ts hstep hused =>
    cases e1 <;> erase_simp at heq1

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

/-- If the erased `Resolve` (which is `Resolve e0 (val v1) (val v2)`) sits atop
a context whose "hole" `e'` is a non-value, then either the context is empty
or its innermost frame is a `ResolveLCtx`. -/
@[rocq_alias fill_to_resolve]
theorem fill_to_resolve {e0 : Exp} {v1 v2 : Val} {K : List ECtxItem} {e' : Exp}
    (hnv : toVal e' = none)
    (heq : Exp.resolve e0 (.val v1) (.val v2) = fill K e') :
    K = [] ∨ ∃ K' Ki, K = K' ++ [ECtxItem.resolveL Ki v1 v2] := by
  cases K using FromMathlib.List.reverseRec with
  | nil => exact .inl rfl
  | append_singleton Ks Ki _ =>
    right
    rw [fill_append, fill_cons, fill_nil,
        show fillItem Ki = Ki.fill from rfl] at heq
    have hne : ∀ (w : Val), fill Ks e' ≠ (.val w : Exp) :=
      fun w => fill_not_val_ne_val w hnv
    cases Ki with
    | resolveL ctx' u1 u2 =>
      simp only [ECtxItem.fill, Exp.resolve.injEq] at heq
      obtain ⟨_, ⟨_⟩, ⟨_⟩⟩ := heq
      exact ⟨Ks, ctx', rfl⟩
    | resolveM =>
      simp only [ECtxItem.fill, Exp.resolve.injEq] at heq
      exact absurd heq.2.1.symm (hne _)
    | resolveR =>
      simp only [ECtxItem.fill, Exp.resolve.injEq] at heq
      exact absurd heq.2.2.symm (hne _)
    | _ => simp only [ECtxItem.fill] at heq; cases heq

/-- `PurePrimStep` from a `PureExec` instance. -/
private theorem purePrimStep_of_pureExec {e1 e2 : Exp}
    (h : PureExec True 1 e1 e2) : PurePrimStep e1 e2 := by
  have := h.pureExec trivial
  cases this with
  | tail y hxy hyz => cases hxy; exact hyz

/-- `Fst (Fst ((v0, v1), v2))` reduces to `v0` by four pure steps. -/
@[rocq_alias projs_pure_steps]
theorem projs_pure_steps (v0 v1 v2 : Val) :
    Relation.ReflTransGen PurePrimStep
      (eraseResolve (.val v0) (.val v1) (.val v2)) (.val v0) := by
  unfold eraseResolve
  -- Step 1: `(v0, v1)` (as expr) reduces to `((v0, v1) : Val)`.
  have s1 : PurePrimStep
      (Exp.pair (.val v0) (.val v1))
      (Exp.val (.pair v0 v1)) :=
    purePrimStep_of_pureExec instPureExecPair
  -- Step 2: `((v0, v1)_val, v2)` (as expr) reduces to `((v0, v1)_val, v2)_val`.
  have s2 : PurePrimStep
      (Exp.pair (.val (.pair v0 v1)) (.val v2))
      (Exp.val (.pair (.pair v0 v1) v2)) :=
    purePrimStep_of_pureExec instPureExecPair
  -- Step 3: `Fst ((...)_val)` reduces to `(v0, v1)_val`.
  have s3 : PurePrimStep
      (Exp.fst (.val (.pair (.pair v0 v1) v2)))
      (Exp.val (.pair v0 v1)) :=
    purePrimStep_of_pureExec instPureExecFst
  -- Step 4: `Fst ((v0, v1)_val)` reduces to `v0`.
  have s4 : PurePrimStep (Exp.fst (.val (.pair v0 v1))) (Exp.val v0) :=
    purePrimStep_of_pureExec instPureExecFst
  have h1 := ReflTransGen_pureStep_fill
      (K := fill (Expr := Exp) [ECtxItem.pairL v2, .fst, .fst])
      (Relation.ReflTransGen.single s1)
  have h2 := ReflTransGen_pureStep_fill
      (K := fill (Expr := Exp) [ECtxItem.fst, .fst])
      (Relation.ReflTransGen.single s2)
  have h3 := ReflTransGen_pureStep_fill
      (K := fill (Expr := Exp) [ECtxItem.fst])
      (Relation.ReflTransGen.single s3)
  simp only [fill_cons, fill_nil, fillItem, ECtxItem.fill] at h1 h2 h3
  exact h1.trans (h2.trans (h3.trans (Relation.ReflTransGen.single s4)))

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
    cases K using FromMathlib.List.reverseRec with
    | nil =>
      simp only [fill_nil] at heq_e
      subst heq_e
      exact Resolve_3_vals_base_stuck _ _ _ _ _ _ _ _ bstep
    | append_singleton Ks Ki _ =>
      rw [fill_append, fill_cons, fill_nil,
          show fillItem Ki = Ki.fill from rfl] at heq_e
      have hne : ∀ (w : Val), fill Ks e1 ≠ (.val w : Exp) :=
        fun w => fill_not_val_ne_val w hnv
      cases Ki with
      | resolveL ctx u1 u2 =>
        simp only [ECtxItem.fill, Exp.resolve.injEq] at heq_e
        have hh := heq_e.1
        have hval_inner : (toVal (ctx.fill (fill Ks e1))).isSome := by
          rw [← hh]; simp [ToVal.toVal]
        have hval_inner2 : (toVal (fill Ks e1)).isSome :=
          EctxItemLanguage.fillItem_val (Ki := ctx) _ hval_inner
        have hnv_inner : toVal (fill Ks e1) = none := fill_not_val (K := Ks) hnv
        rw [hnv_inner] at hval_inner2; simp at hval_inner2
      | resolveM =>
        simp only [ECtxItem.fill, Exp.resolve.injEq] at heq_e
        exact hne _ heq_e.2.1.symm
      | resolveR =>
        simp only [ECtxItem.fill, Exp.resolve.injEq] at heq_e
        exact hne _ heq_e.2.2.symm
      | _ => simp only [ECtxItem.fill] at heq_e; cases heq_e

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
  -- Case on the innermost erased frame of `Ks`.
  cases Ks using FromMathlib.List.reverseRec with
  | nil =>
    -- Ks = []: e1' = .pair (.pair X0 X1) X2, no base step matches
    -- (`.pairS` needs both arguments to be values).
    simp only [fill_nil] at heq_e
    rw [← heq_e] at bstep
    cases bstep
  | append_singleton Ks' Ki' _ =>
    rw [fill_append, fill_cons, fill_nil,
        show fillItem Ki' = Ki'.fill from rfl] at heq_e
    -- Head of Ki'.fill must be `.fst`, hence Ki' = .fst.
    cases Ki' <;>
      first
        | (simp only [ECtxItem.fill] at heq_e; cases heq_e; done)
        | skip
    -- Only `.fst` remains.
    simp only [ECtxItem.fill, Exp.fst.injEq] at heq_e
    -- Peel Ks' — its innermost frame must give a `.pair` head.
    cases Ks' using FromMathlib.List.reverseRec with
      | nil =>
        simp only [fill_nil] at heq_e
        rw [← heq_e] at bstep
        cases bstep
      | append_singleton Ks'' Ki'' _ =>
        rw [fill_append, fill_cons, fill_nil,
            show fillItem Ki'' = Ki''.fill from rfl] at heq_e
        -- Only `.pairL v` or `.pairR e` produce a `.pair` head.
        cases Ki'' with
        | pairL v_r2 =>
          simp only [ECtxItem.fill, Exp.pair.injEq] at heq_e
          obtain ⟨hinner, hv2⟩ := heq_e
          have hv2r : toVal (eraseExpr r2) = some v_r2 := by
            rw [hv2]; rfl
          obtain ⟨w_r2, hw_r2_some, hew_r2⟩ := toVal_erase_some hv2r
          have hr2eq : r2 = .val w_r2 := by
            cases r2 <;> simp [ToVal.toVal] at hw_r2_some
            exact congrArg _ hw_r2_some
          subst hr2eq
          cases Ks'' using FromMathlib.List.reverseRec with
          | nil =>
            simp only [fill_nil] at hinner
            have hnv_e1' : toVal e1' = none :=
              EctxItemLanguage.val_stuck bstep
            have hstep_val :
                ∀ {X Y : Exp} {σ0 κ0 e2f σ2f efsf},
                  BaseStep (Exp.pair X Y) σ0 κ0 e2f σ2f efsf →
                  ∃ vx vy, X = .val vx ∧ Y = .val vy := by
              intro X Y _ _ _ _ _ hb; cases hb
              rename_i _σx vx vy
              exact ⟨vx, vy, rfl, rfl⟩
            have := hstep_val (hinner ▸ bstep)
            obtain ⟨v0, v1, h0, h1⟩ := this
            have hv0 : toVal (eraseExpr r0) = some v0 := by rw [h0]; rfl
            have hv1 : toVal (eraseExpr r1) = some v1 := by rw [h1]; rfl
            obtain ⟨w_r0, hw_r0_some, _⟩ := toVal_erase_some hv0
            obtain ⟨w_r1, hw_r1_some, _⟩ := toVal_erase_some hv1
            have hr0eq : r0 = .val w_r0 := by
              cases r0 <;> simp [ToVal.toVal] at hw_r0_some
              exact congrArg _ hw_r0_some
            have hr1eq : r1 = .val w_r1 := by
              cases r1 <;> simp [ToVal.toVal] at hw_r1_some
              exact congrArg _ hw_r1_some
            subst hr0eq; subst hr1eq
            exact absurd hns (Resolve_3_vals_unsafe _ _ _ _)
          | append_singleton Ks''' Ki''' _ =>
            rw [fill_append, fill_cons, fill_nil,
                show fillItem Ki''' = Ki'''.fill from rfl] at hinner
            cases Ki''' with
            | pairL v_r1 =>
              simp only [ECtxItem.fill, Exp.pair.injEq] at hinner
              obtain ⟨hi, hv1⟩ := hinner
              have hv1r : toVal (eraseExpr r1) = some v_r1 := by
                rw [hv1]; rfl
              obtain ⟨w_r1, hw_r1_some, hew_r1⟩ := toVal_erase_some hv1r
              have hr1eq : r1 = .val w_r1 := by
                cases r1 <;> simp [ToVal.toVal] at hw_r1_some
                exact congrArg _ hw_r1_some
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
                cases K_h using FromMathlib.List.reverseRec with
                | nil =>
                  simp only [fill_nil] at heq_gen
                  rw [← heq_gen] at bs_h
                  cases bs_h with
                  | resolveS _ _ _ _ _ _ _ _ bs_inner _ =>
                    right
                    exact ⟨_, _, _, _, BaseStep.ContextStep.ofBaseStep [] bs_inner⟩
                | append_singleton K_rest Ki_top _ =>
                  rw [fill_append, fill_cons, fill_nil,
                      show fillItem Ki_top = Ki_top.fill from rfl] at heq_gen
                  have hne_h : ∀ (w : Val), fill K_rest he1_h ≠ (.val w : Exp) :=
                    fun w => fill_not_val_ne_val w hnv_h
                  cases Ki_top with
                  | resolveL ctx u1 u2 =>
                    simp only [ECtxItem.fill, Exp.resolve.injEq] at heq_gen
                    obtain ⟨hr0_eq, _, _⟩ := heq_gen
                    right
                    refine ⟨_, _, _, _,
                      BaseStep.ContextStep.ofBaseStep' (K_rest ++ [ctx])
                        (by rw [fill_append, fill_cons, fill_nil,
                                show fillItem ctx = ctx.fill from rfl,
                                ← hr0_eq]) rfl bs_h⟩
                  | resolveM =>
                    simp only [ECtxItem.fill, Exp.resolve.injEq] at heq_gen
                    exact absurd heq_gen.2.1.symm (hne_h _)
                  | resolveR =>
                    simp only [ECtxItem.fill, Exp.resolve.injEq] at heq_gen
                    exact absurd heq_gen.2.2.symm (hne_h _)
                  | _ =>
                    simp only [ECtxItem.fill] at heq_gen; cases heq_gen
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
                  cases K_h using FromMathlib.List.reverseRec with
                  | nil =>
                    simp only [fill_nil] at heq_h
                    rw [← heq_h] at bs_h
                    match bs_h with
                    | BaseStep.resolveS p v _ _ _ _ κs_r ts_r bs_inner hused =>
                      exact ⟨p, v, _, κs_r, ts_r, rfl, hused, bs_inner⟩
                  | append_singleton K_rest Ki_top _ =>
                    rw [fill_append, fill_cons, fill_nil,
                        show fillItem Ki_top = Ki_top.fill from rfl] at heq_h
                    have hne_h :
                        ∀ (w : Val), fill K_rest he1_h ≠ (.val w : Exp) :=
                      fun w => fill_not_val_ne_val w hnv_h
                    cases Ki_top with
                    | resolveL ctx u1 u2 =>
                      simp only [ECtxItem.fill, Exp.resolve.injEq] at heq_h
                      obtain ⟨hr0_eq, _, _⟩ := heq_h
                      exfalso
                      have hbs_ctx :
                          BaseStep (ctx.fill (fill K_rest he1_h)) σ1
                            κ_r0 inner_e2 σ_r0 efs_r0 := hr0_eq ▸ hbstep_r0
                      have hval_isSome :
                          (toVal (fill K_rest he1_h)).isSome :=
                        EctxItemLanguage.base_ctx_step_val hbs_ctx
                      rcases Option.isSome_iff_exists.mp hval_isSome with ⟨w, hw⟩
                      have hnv_fill : toVal (fill K_rest he1_h) = none :=
                        fill_not_val (K := K_rest) hnv_h
                      rw [hnv_fill] at hw; cases hw
                    | resolveM =>
                      simp only [ECtxItem.fill, Exp.resolve.injEq] at heq_h
                      exact absurd heq_h.2.1.symm (hne_h _)
                    | resolveR =>
                      simp only [ECtxItem.fill, Exp.resolve.injEq] at heq_h
                      exact absurd heq_h.2.2.symm (hne_h _)
                    | _ =>
                      simp only [ECtxItem.fill] at heq_h; cases heq_h
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
            | pairR e_r0 =>
              simp only [ECtxItem.fill, Exp.pair.injEq] at hinner
              obtain ⟨he_r0, hi⟩ := hinner
              subst he_r0
              have hns_r1 : PrimStep.NotStuck (r1, σ1) := by
                have heq : (Exp.resolve r0 r1 (.val w_r2)) =
                           fill [ECtxItem.resolveM r0 w_r2] r1 := by
                  simp [fill_cons, fill_nil, fillItem, ECtxItem.fill]
                rw [heq] at hns
                exact Language.Context.notStuck_fill_inv
                  (K := fill [ECtxItem.resolveM r0 w_r2]) hns
              have hlk : Ks'''.length ≤
                  (Ks''' ++ [ECtxItem.pairR (eraseExpr r0)] ++
                   [ECtxItem.pairL v_r2] ++ [ECtxItem.fst]).length := by
                simp
              have hmatch := IHapp hlk hi hns_r1
              have hlift := hmatch.fill_ctx [ECtxItem.resolveM r0 w_r2]
              have hLHS :
                  fill [ECtxItem.resolveM r0 w_r2] r1 =
                  (Exp.resolve r0 r1 (.val w_r2)) := by
                simp [fill_cons, fill_nil, fillItem, ECtxItem.fill]
              have hRHS :
                  fill (eraseECtx [ECtxItem.resolveM r0 w_r2])
                       (fill Ks''' e2') =
                  fill (Ks''' ++
                    [ECtxItem.pairR (eraseExpr r0)] ++
                    [ECtxItem.pairL (eraseVal w_r2)] ++
                    [ECtxItem.fst] ++ [ECtxItem.fst]) e2' := by
                simp [eraseECtx, List.flatMap_cons, List.flatMap_nil,
                      eraseECtxItem, fill_append, fill_cons, fill_nil,
                      fillItem, ECtxItem.fill]
              rw [hLHS, hRHS] at hlift
              subst hew_r2
              exact hlift
            | _ => simp only [ECtxItem.fill] at hinner; cases hinner
        | pairR e_outer =>
          simp only [ECtxItem.fill, Exp.pair.injEq] at heq_e
          obtain ⟨he_outer, hi⟩ := heq_e
          subst he_outer
          have hns_r2 : PrimStep.NotStuck (r2, σ1) := by
            have heq : (Exp.resolve r0 r1 r2) =
                       fill [ECtxItem.resolveR r0 r1] r2 := by
              simp [fill_cons, fill_nil, fillItem, ECtxItem.fill]
            rw [heq] at hns
            exact Language.Context.notStuck_fill_inv
              (K := fill [ECtxItem.resolveR r0 r1]) hns
          have hlk : Ks''.length ≤ (Ks'' ++ [ECtxItem.pairR
                        (.pair (eraseExpr r0) (eraseExpr r1))] ++
                        [ECtxItem.fst]).length := by
            simp
          have hmatch := IHapp hlk hi hns_r2
          have hlift := hmatch.fill_ctx [ECtxItem.resolveR r0 r1]
          have hLHS :
              fill [ECtxItem.resolveR r0 r1] r2 =
              (Exp.resolve r0 r1 r2) := by
            simp [fill_cons, fill_nil, fillItem, ECtxItem.fill]
          have hRHS :
              fill (eraseECtx [ECtxItem.resolveR r0 r1]) (fill Ks'' e2') =
              fill (Ks'' ++
                [ECtxItem.pairR (.pair (eraseExpr r0) (eraseExpr r1))] ++
                [ECtxItem.fst] ++ [ECtxItem.fst]) e2' := by
            simp [eraseECtx, List.flatMap_cons, List.flatMap_nil,
                  eraseECtxItem, fill_append, fill_cons, fill_nil,
                  fillItem, ECtxItem.fill]
          rw [hLHS, hRHS] at hlift
          exact hlift
        | _ => simp only [ECtxItem.fill] at heq_e; cases heq_e

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
        have hns0 : PrimStep.NotStuck (einner, σ1) := by
          rw [heo] at hns
          exact Language.Context.notStuck_fill_inv
            (K := fill [Ki_orig]) (by simp [fill_cons, fill_nil, fillItem]; exact hns)
        have hmatch : PrimStepMatchedByErasedSteps einner σ1 (fill Ks e2') σ2 efs :=
          IHapp (Nat.le_refl _) hi hns0
        have hlift := hmatch.fill_ctx [Ki_orig]
        show PrimStepMatchedByErasedSteps e1 σ1 (fill (Ks ++ [Ki]) e2') σ2 efs
        rw [heo, fill_append]
        simp only [fill_cons, fill_nil, fillItem, eraseECtx, List.flatMap_cons,
                   List.flatMap_nil, List.append_nil, hek] at hlift ⊢
        exact hlift
      -- Discharge the .newProph collision that arises only for `Ki = .appL v2`
      -- or `Ki = .appR e1`, where the erased newProph shape is `.app v v`.
      -- We invoke this helper after the initial `cases e1 <;> simp ...`.
      have newProphAppL_bad : ∀ (v2 : Val), hl(v(λ _, #BaseLit.poison)) = fill Ks e1' ∧
          hl(#()) = hl(v(&v2)) → False := by
        intro _ ⟨h1, _⟩
        rw [← h1] at hnv_inner
        simp [ToVal.toVal] at hnv_inner
      have newProphAppR_bad : ∀ (e0 : Exp), e0 = hl(v(λ _, #BaseLit.poison)) ∧
          hl(#()) = fill Ks e1' → False := by
        intro _ ⟨_, h⟩
        rw [← h] at hnv_inner
        simp [ToVal.toVal] at hnv_inner
      cases Ki with
      | appL v2 =>
        peel_ki
        rotate_left
        · exact absurd heq_e (newProphAppL_bad _)
        rename_i einner ea
        obtain ⟨hi, ha⟩ := heq_e
        obtain ⟨v2', rfl, rfl⟩ := eraseExpr_eq_val ha
        exact finish (.appL v2') einner (by simp [ECtxItem.fill]) hi (by simp [eraseECtxItem])
      | appR e0 =>
        peel_ki
        rotate_left
        · exfalso
          have := heq_e.2
          rw [← this] at hnv_inner
          simp [ToVal.toVal] at hnv_inner
        rename_i eouter einner
        obtain ⟨rfl, hi⟩ := heq_e
        exact finish (.appR eouter) einner (by simp [ECtxItem.fill]) hi (by simp [eraseECtxItem])
      | unOp op1 =>
        peel_ki
        rename_i op' einner
        obtain ⟨rfl, hi⟩ := heq_e
        exact finish (.unOp op') einner (by simp [ECtxItem.fill]) hi (by simp [eraseECtxItem])
      | binOpL op1 v2 =>
        peel_ki
        rename_i op' einner ea
        obtain ⟨rfl, hi, ha⟩ := heq_e
        obtain ⟨v2', rfl, rfl⟩ := eraseExpr_eq_val ha
        exact finish (.binOpL op' v2') einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | binOpR op1 e0 =>
        peel_ki
        rename_i op' eouter einner
        obtain ⟨rfl, rfl, hi⟩ := heq_e
        exact finish (.binOpR op' eouter) einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | «if» e1' e2' =>
        peel_ki
        rename_i einner ei1 ei2
        obtain ⟨hi, rfl, rfl⟩ := heq_e
        exact finish (.if ei1 ei2) einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | pairL v2 =>
        peel_ki
        rename_i einner ea
        obtain ⟨hi, ha⟩ := heq_e
        obtain ⟨v2', rfl, rfl⟩ := eraseExpr_eq_val ha
        exact finish (.pairL v2') einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | pairR e0 =>
        peel_ki
        rename_i eouter einner
        obtain ⟨rfl, hi⟩ := heq_e
        exact finish (.pairR eouter) einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | fst =>
        -- e1 could be `.fst einner` (normal case) or `.resolve r0 r1 r2`
        -- (special case, since resolve erases to `.fst (.fst ...)`).
        peel_ki
        · -- .fst einner case: straightforward IH application.
          rename_i einner
          exact finish .fst einner (by simp [ECtxItem.fill]) heq_e
            (by simp [eraseECtxItem])
        · -- .resolve r0 r1 r2 case: delegate to the specialized helper.
          rename_i r0 r1 r2
          exact resolve_fst_primStepMatched bstep hns heq_e IHapp
      | snd =>
        peel_ki
        rename_i einner
        exact finish .snd einner (by simp [ECtxItem.fill]) heq_e (by simp [eraseECtxItem])
      | injL =>
        peel_ki
        rename_i einner
        exact finish .injL einner (by simp [ECtxItem.fill]) heq_e (by simp [eraseECtxItem])
      | injR =>
        peel_ki
        rename_i einner
        exact finish .injR einner (by simp [ECtxItem.fill]) heq_e (by simp [eraseECtxItem])
      | case ec1 ec2 =>
        peel_ki
        rename_i einner ei1 ei2
        obtain ⟨hi, rfl, rfl⟩ := heq_e
        exact finish (.case ei1 ei2) einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | allocNL v2 =>
        peel_ki
        rename_i einner ea
        obtain ⟨hi, ha⟩ := heq_e
        obtain ⟨v2', rfl, rfl⟩ := eraseExpr_eq_val ha
        exact finish (.allocNL v2') einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | allocNR e0 =>
        peel_ki
        rename_i eouter einner
        obtain ⟨rfl, hi⟩ := heq_e
        exact finish (.allocNR eouter) einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | free =>
        peel_ki
        rename_i einner
        exact finish .free einner (by simp [ECtxItem.fill]) heq_e (by simp [eraseECtxItem])
      | load =>
        peel_ki
        rename_i einner
        exact finish .load einner (by simp [ECtxItem.fill]) heq_e (by simp [eraseECtxItem])
      | storeL v2 =>
        peel_ki
        rename_i einner ea
        obtain ⟨hi, ha⟩ := heq_e
        obtain ⟨v2', rfl, rfl⟩ := eraseExpr_eq_val ha
        exact finish (.storeL v2') einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | storeR e0 =>
        peel_ki
        rename_i eouter einner
        obtain ⟨rfl, hi⟩ := heq_e
        exact finish (.storeR eouter) einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | xchgL v2 =>
        peel_ki
        rename_i einner ea
        obtain ⟨hi, ha⟩ := heq_e
        obtain ⟨v2', rfl, rfl⟩ := eraseExpr_eq_val ha
        exact finish (.xchgL v2') einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | xchgR e0 =>
        peel_ki
        rename_i eouter einner
        obtain ⟨rfl, hi⟩ := heq_e
        exact finish (.xchgR eouter) einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | cmpXchgL v1 v2 =>
        peel_ki
        rename_i einner ea1 ea2
        obtain ⟨hi, ha1, ha2⟩ := heq_e
        obtain ⟨v1', rfl, rfl⟩ := eraseExpr_eq_val ha1
        obtain ⟨v2', rfl, rfl⟩ := eraseExpr_eq_val ha2
        exact finish (.cmpXchgL v1' v2') einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | cmpXchgM e0 v2 =>
        peel_ki
        rename_i eouter einner ea
        obtain ⟨rfl, hi, ha⟩ := heq_e
        obtain ⟨v2', rfl, rfl⟩ := eraseExpr_eq_val ha
        exact finish (.cmpXchgM eouter v2') einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | cmpXchgR eA eB =>
        peel_ki
        rename_i eouter0 eouter1 einner
        obtain ⟨rfl, rfl, hi⟩ := heq_e
        exact finish (.cmpXchgR eouter0 eouter1) einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | faaL v2 =>
        peel_ki
        rename_i einner ea
        obtain ⟨hi, ha⟩ := heq_e
        obtain ⟨v2', rfl, rfl⟩ := eraseExpr_eq_val ha
        exact finish (.faaL v2') einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | faaR e0 =>
        peel_ki
        rename_i eouter einner
        obtain ⟨rfl, hi⟩ := heq_e
        exact finish (.faaR eouter) einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | resolveL Kres v1 v2 =>
        simp only [ECtxItem.fill] at heq_e
        exfalso; cases e1 <;> erase_simp at heq_e
      | resolveM e0 v2 =>
        simp only [ECtxItem.fill] at heq_e
        exfalso; cases e1 <;> erase_simp at heq_e
      | resolveR e0 e1outer =>
        simp only [ECtxItem.fill] at heq_e
        exfalso; cases e1 <;> erase_simp at heq_e

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
  suffices H : ∀ (ρ2 : List Exp × State),
      Relation.ReflTransGen Language.ErasedStep ([eraseExpr e], eraseState σ) ρ2 →
      ∃ (t2'' : List Exp) (σ2' : State),
        Relation.ReflTransGen Language.ErasedStep ([e], σ) (t2'', σ2') ∧
        ρ2.2 = eraseState σ2' ∧ Language.PureSteps ρ2.1 (eraseTp t2'') by
    exact H _ h
  intro ρ2 h
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
