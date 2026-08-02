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
    cases v1 <;> cases v2 <;> simp_all [Val.isUnboxed, eraseVal]
    exact eraseBaseLit_inj_of_unboxed h heq
  · -- injR / injR
    rename_i v1 v2
    cases v1 <;> cases v2 <;> simp_all [Val.isUnboxed, eraseVal]
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
    simp only [reduceCtorEq, false_iff]
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
      simp [eraseVal, eraseBaseLit, BinOp.eval] at h <;>
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
      simp [BinOp.eval] at hw <;>
      (subst hw; subst hwe; simp [eraseVal, eraseBaseLit, BinOp.eval])
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

/-- If the erased program makes a base step, so does the original program.

Full proof requires case analysis on every constructor of `BaseStep` on the
erased LHS and inverting the erasure to reconstruct an original step. This
is the largest sub-proof of the erasure theorem; see the Coq version. -/
@[rocq_alias erased_base_step_base_step]
theorem erased_baseStep_baseStep {e1 : Exp} {σ1 : State}
    {κ : List Observation} {e2 : Exp} {σ2 : State} {efs : List Exp}
    (h : BaseStep (eraseExpr e1) (eraseState σ1) κ e2 σ2 efs) :
    BaseStepsToErasureOf e1 σ1 e2 σ2 efs := by
  generalize heq1 : eraseExpr e1 = e1e at h
  generalize heqσ : eraseState σ1 = σ1e at h
  cases h with
  | recS f x e σ =>
    cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    obtain ⟨rfl, rfl, rfl⟩ := heq1
    rename_i f' x' e'
    refine ⟨_, _, _, _, .recS f' x' e' σ1, ?_, heqσ, rfl⟩
    simp [eraseExpr, eraseVal]
  | pairS v1 v2 σ =>
    cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    rename_i e1' e2'
    obtain ⟨hv1, hv2⟩ := heq1
    cases e1' <;> simp [eraseExpr, erasedNewProph, eraseResolve] at hv1
    cases e2' <;> simp [eraseExpr, erasedNewProph, eraseResolve] at hv2
    rename_i w1 w2
    cases hv1; cases hv2
    refine ⟨_, _, _, _, .pairS w1 w2 σ1, ?_, heqσ, rfl⟩
    simp [eraseExpr, eraseVal]
  | injLS v σ =>
    cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    rename_i e'
    cases e' <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    rename_i w
    cases heq1
    refine ⟨_, _, _, _, .injLS w σ1, ?_, heqσ, rfl⟩
    simp [eraseExpr, eraseVal]
  | injRS v σ =>
    cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    rename_i e'
    cases e' <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    rename_i w
    cases heq1
    refine ⟨_, _, _, _, .injRS w σ1, ?_, heqσ, rfl⟩
    simp [eraseExpr, eraseVal]
  | betaS f x e0 v2 e' σ heq =>
    cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    case app ef ea =>
      obtain ⟨hf, ha⟩ := heq1
      cases ef <;> simp [eraseExpr, erasedNewProph, eraseResolve] at hf
      case val w =>
        cases w <;> simp [eraseVal] at hf
        case rec_ f' x' body =>
          cases hf
          cases ea <;> simp [eraseExpr, erasedNewProph, eraseResolve] at ha
          case val w2 =>
            cases ha
            refine ⟨_, _, _, _, .betaS _ _ _ w2 _ σ1 rfl, ?_, heqσ, rfl⟩
            simp [heq, eraseExpr_subst, eraseVal, eraseExpr]
          all_goals cases ha
        all_goals cases hf
      all_goals cases hf
    case newProph =>
      -- e1 = .newProph: erased β-reduces to .val .poison; reconstruct via newProphS.
      obtain ⟨hf, ha⟩ := heq1
      obtain ⟨pf, Hpf⟩ := Std.List.fresh σ1.usedProphId.toList
      have Hpf_contains : ¬ σ1.usedProphId.contains pf := fun hc =>
        Hpf (Std.ExtTreeSet.mem_toList.mpr hc)
      refine ⟨_, _, _, _, .newProphS σ1 pf Hpf_contains, ?_, ?_, rfl⟩
      · -- Show erasure of the prophecy value equals betaS result
        cases hf; cases ha; subst heq
        rfl
      · -- Show state erasure unchanged
        rw [← heqσ]
        show _ = eraseState σ1
        simp [eraseState]
  | unOpS op v v' σ hv =>
    cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    rename_i op' e'
    obtain ⟨rfl, hv1⟩ := heq1
    cases e' <;> simp [eraseExpr, erasedNewProph, eraseResolve] at hv1
    rename_i w
    cases hv1
    obtain ⟨w', hw, hwe⟩ := UnOp.eval_erase.mp hv
    refine ⟨_, _, _, _, .unOpS op' w w' σ1 hw, ?_, heqσ, rfl⟩
    simp [eraseExpr, eraseVal, hwe]
  | binOpS op v1 v2 v' σ hv =>
    cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    rename_i op' e1' e2'
    obtain ⟨rfl, hv1, hv2⟩ := heq1
    cases e1' <;> simp [eraseExpr, erasedNewProph, eraseResolve] at hv1
    cases e2' <;> simp [eraseExpr, erasedNewProph, eraseResolve] at hv2
    rename_i w1 w2
    cases hv1; cases hv2
    obtain ⟨w', hw, hwe⟩ := BinOp.eval_erase.mp hv
    refine ⟨_, _, _, _, .binOpS op' w1 w2 w' σ1 hw, ?_, heqσ, rfl⟩
    simp [eraseExpr, eraseVal, hwe]
  | ifTrueS e1' e2' σ =>
    cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    rename_i ec et ef
    obtain ⟨hc, he1, he2⟩ := heq1
    cases ec <;> simp [eraseExpr, erasedNewProph, eraseResolve] at hc
    case val w =>
      cases w <;> simp [eraseVal] at hc
      case lit l =>
        cases l <;> simp [eraseBaseLit] at hc
        case bool b =>
          cases hc
          subst he1; subst he2
          refine ⟨_, _, _, _, .ifTrueS et ef σ1, rfl, heqσ, rfl⟩
        all_goals cases hc
      all_goals cases hc
  | ifFalseS e1' e2' σ =>
    cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    rename_i ec et ef
    obtain ⟨hc, he1, he2⟩ := heq1
    cases ec <;> simp [eraseExpr, erasedNewProph, eraseResolve] at hc
    case val w =>
      cases w <;> simp [eraseVal] at hc
      case lit l =>
        cases l <;> simp [eraseBaseLit] at hc
        case bool b =>
          cases hc
          subst he1; subst he2
          refine ⟨_, _, _, _, .ifFalseS et ef σ1, rfl, heqσ, rfl⟩
        all_goals cases hc
      all_goals cases hc
  | fstS v1 v2 σ =>
    cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    rename_i e'
    cases e' <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    case val w =>
      cases w <;> simp [eraseVal] at heq1
      case pair w1 w2 =>
        obtain ⟨rfl, rfl⟩ := heq1
        refine ⟨_, _, _, _, .fstS w1 w2 σ1, ?_, heqσ, rfl⟩
        rfl
      all_goals cases heq1
  | sndS v1 v2 σ =>
    cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    rename_i e'
    cases e' <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    case val w =>
      cases w <;> simp [eraseVal] at heq1
      case pair w1 w2 =>
        obtain ⟨rfl, rfl⟩ := heq1
        refine ⟨_, _, _, _, .sndS w1 w2 σ1, ?_, heqσ, rfl⟩
        rfl
      all_goals cases heq1
  | caseLS v e1' e2' σ =>
    cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    rename_i ec et ef
    obtain ⟨hc, he1, he2⟩ := heq1
    cases ec <;> simp [eraseExpr, erasedNewProph, eraseResolve] at hc
    case val w =>
      cases w <;> simp [eraseVal] at hc
      case injL inner =>
        cases hc; subst he1; subst he2
        refine ⟨_, _, _, _, .caseLS inner _ _ σ1, ?_, heqσ, rfl⟩
        rfl
      all_goals cases hc
  | caseRS v e1' e2' σ =>
    cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    rename_i ec et ef
    obtain ⟨hc, he1, he2⟩ := heq1
    cases ec <;> simp [eraseExpr, erasedNewProph, eraseResolve] at hc
    case val w =>
      cases w <;> simp [eraseVal] at hc
      case injR inner =>
        cases hc; subst he1; subst he2
        refine ⟨_, _, _, _, .caseRS inner _ _ σ1, ?_, heqσ, rfl⟩
        rfl
      all_goals cases hc
  | allocNS n v σ l hpos hnone =>
    cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    case allocN en ev =>
      obtain ⟨hn, hv⟩ := heq1
      cases en <;> simp [eraseExpr, erasedNewProph, eraseResolve] at hn
      case val w =>
        cases w <;> simp [eraseVal] at hn
        case lit litn =>
          cases litn <;> simp [eraseBaseLit] at hn
          case int n' =>
            cases ev <;> simp [eraseExpr, erasedNewProph, eraseResolve] at hv
            case val w2 =>
              cases hv; cases hn
              refine ⟨_, _, _, _,
                .allocNS _ w2 σ1 l hpos (fun i hi0 hin => ?_), ?_, ?_, rfl⟩
              · have hn := hnone i hi0 hin
                rw [← heqσ, eraseState_get?] at hn
                cases hget : σ1.get? (l + i) with
                | none => rfl
                | some ov => rw [hget] at hn; simp at hn
              · rfl
              · rw [← heqσ, eraseState_initHeap]; rfl
            all_goals cases hv
          all_goals cases hn
        all_goals cases hn
      all_goals cases hn
  | freeS l v σ hget =>
    cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    case free el =>
      cases el <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
      case val w =>
        cases w <;> simp [eraseVal] at heq1
        case lit lit =>
          cases lit <;> simp [eraseBaseLit] at heq1
          case loc =>
            cases heq1
            rw [← heqσ, eraseState_get?] at hget
            cases horig : σ1.get? l with
            | none => rw [horig] at hget; simp at hget
            | some ov =>
              rw [horig] at hget; simp at hget
              cases ov with
              | none => simp [eraseVal] at hget
              | some ov' =>
                refine ⟨_, _, _, _, .freeS l ov' σ1 horig, rfl, ?_, rfl⟩
                rw [← heqσ, eraseState_initHeap]; rfl
          all_goals cases heq1
        all_goals cases heq1
      all_goals cases heq1
  | loadS l v σ hget =>
    cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    case load el =>
      cases el <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
      case val w =>
        cases w <;> simp [eraseVal] at heq1
        case lit lit =>
          cases lit <;> simp [eraseBaseLit] at heq1
          case loc =>
            cases heq1
            rw [← heqσ, eraseState_get?] at hget
            cases horig : σ1.get? l with
            | none => rw [horig] at hget; simp at hget
            | some ov =>
              rw [horig] at hget; simp at hget
              cases ov with
              | none => simp [eraseVal] at hget
              | some ov' =>
                simp at hget
                refine ⟨_, _, _, _, .loadS l ov' σ1 horig, ?_, heqσ, rfl⟩
                simp [eraseExpr, eraseVal, hget]
          all_goals cases heq1
        all_goals cases heq1
      all_goals cases heq1
  | storeS l v w σ hget =>
    cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    case store el ew =>
      obtain ⟨hel, hew⟩ := heq1
      cases el <;> simp [eraseExpr, erasedNewProph, eraseResolve] at hel
      case val wl =>
        cases wl <;> simp [eraseVal] at hel
        case lit lit =>
          cases lit <;> simp [eraseBaseLit] at hel
          case loc =>
            cases hel
            cases ew <;> simp [eraseExpr, erasedNewProph, eraseResolve] at hew
            case val ww =>
              cases hew
              rw [← heqσ, eraseState_get?] at hget
              cases horig : σ1.get? l with
              | none => rw [horig] at hget; simp at hget
              | some ov =>
                rw [horig] at hget
                cases ov with
                | none => simp [eraseVal] at hget
                | some ov' =>
                  refine ⟨_, _, _, _, .storeS _ ov' ww σ1 horig, rfl, ?_, rfl⟩
                  rw [← heqσ, eraseState_initHeap]; rfl
            all_goals cases hew
          all_goals cases hel
        all_goals cases hel
      all_goals cases hel
  | xchgS l v1 v2 σ hget =>
    cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    case xchg el ew =>
      obtain ⟨hel, hew⟩ := heq1
      cases el <;> simp [eraseExpr, erasedNewProph, eraseResolve] at hel
      case val wl =>
        cases wl <;> simp [eraseVal] at hel
        case lit lit =>
          cases lit <;> simp [eraseBaseLit] at hel
          case loc =>
            cases hel
            cases ew <;> simp [eraseExpr, erasedNewProph, eraseResolve] at hew
            case val ww =>
              cases hew
              rw [← heqσ, eraseState_get?] at hget
              cases horig : σ1.get? l with
              | none => rw [horig] at hget; simp at hget
              | some ov =>
                rw [horig] at hget; simp at hget
                cases ov with
                | none => simp [eraseVal] at hget
                | some ov' =>
                  simp at hget
                  refine ⟨_, _, _, _, .xchgS l ov' ww σ1 horig, ?_, ?_, rfl⟩
                  · simp [eraseExpr, eraseVal, hget]
                  · rw [← heqσ, eraseState_initHeap]; rfl
            all_goals cases hew
          all_goals cases hel
        all_goals cases hel
      all_goals cases hel
  | cmpXchgS l v1 v2 vl σ b hget hcs hb =>
    cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    case cmpXchg el ev1 ev2 =>
      obtain ⟨hel, hev1, hev2⟩ := heq1
      cases el <;> simp [eraseExpr, erasedNewProph, eraseResolve] at hel
      case val wl =>
        cases wl <;> simp [eraseVal] at hel
        case lit lit =>
          cases lit <;> simp [eraseBaseLit] at hel
          case loc =>
            cases hel
            cases ev1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at hev1
            case val w1 =>
              cases ev2 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at hev2
              case val w2 =>
                cases hev1; cases hev2
                rw [← heqσ, eraseState_get?] at hget
                cases horig : σ1.get? l with
                | none => rw [horig] at hget; simp at hget
                | some ov =>
                  rw [horig] at hget; simp at hget
                  cases ov with
                  | none => simp [eraseVal] at hget
                  | some ov' =>
                    simp at hget
                    have hcs' : ov'.compareSafe w1 = true := by
                      rw [← eraseVal_compareSafe, hget]; exact hcs
                    refine ⟨_, _, _, _, .cmpXchgS l w1 w2 ov' σ1 b horig hcs' ?_, ?_, ?_, rfl⟩
                    · rw [← hget] at hb
                      rw [← decide_eq_decide.mpr (eraseVal_inj_iff hcs')]; exact hb
                    · simp [eraseExpr, eraseVal, eraseBaseLit, hget]
                    · rw [← heqσ]
                      split
                      · rw [eraseState_initHeap]; rfl
                      · rfl
              all_goals cases hev2
            all_goals cases hev1
          all_goals cases hel
        all_goals cases hel
      all_goals cases hel
  | faaS l i1 i2 σ hget =>
    cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    case faa el ei =>
      obtain ⟨hel, hei⟩ := heq1
      cases el <;> simp [eraseExpr, erasedNewProph, eraseResolve] at hel
      case val wl =>
        cases wl <;> simp [eraseVal] at hel
        case lit lit =>
          cases lit <;> simp [eraseBaseLit] at hel
          case loc =>
            cases hel
            cases ei <;> simp [eraseExpr, erasedNewProph, eraseResolve] at hei
            case val wi =>
              cases wi <;> simp [eraseVal] at hei
              case lit lit =>
                cases lit <;> simp [eraseBaseLit] at hei
                case int =>
                  cases hei
                  rw [← heqσ, eraseState_get?] at hget
                  cases horig : σ1.get? l with
                  | none => rw [horig] at hget; simp at hget
                  | some ov =>
                    rw [horig] at hget; simp at hget
                    cases ov with
                    | none => simp [eraseVal] at hget
                    | some ov' =>
                      simp at hget
                      cases ov' <;> simp [eraseVal] at hget
                      case lit lit' =>
                        cases lit' <;> simp [eraseBaseLit] at hget
                        case int =>
                          cases hget
                          refine ⟨_, _, _, _, .faaS l i1 i2 σ1 horig, ?_, ?_, rfl⟩
                          · simp [eraseExpr, eraseVal, eraseBaseLit]
                          · rw [← heqσ, eraseState_initHeap]; rfl
                        all_goals cases hget
                      all_goals cases hget
                all_goals cases hei
              all_goals cases hei
            all_goals cases hei
          all_goals cases hel
        all_goals cases hel
      all_goals cases hel
  | forkS e σ =>
    cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
    rename_i e'
    subst heq1
    refine ⟨_, _, _, _, .forkS e' σ1, rfl, heqσ, rfl⟩
  | newProphS σ p hp =>
    cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1
  | resolveS p v e σ w σ' κs ts hstep hused =>
    cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq1

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
        -- eraseExpr e1 = .app (fill Ks e1') (.ofVal v2)
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rotate_left
        · exact absurd heq_e (newProphAppL_bad _)
        rename_i einner ea
        obtain ⟨hi, ha⟩ := heq_e
        cases ea <;> simp [eraseExpr, erasedNewProph, eraseResolve] at ha
        rename_i v2'
        have ha' : eraseVal v2' = v2 := Exp.val.inj ha
        subst ha'
        exact finish (.appL v2') einner (by simp [ECtxItem.fill]) hi (by simp [eraseECtxItem])
      | appR e0 =>
        -- eraseExpr e1 = .app e0 (fill Ks e1')
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rotate_left
        · -- newProph: `fill Ks e1' = .val ()` — contradicts hnv_inner
          exfalso
          have := heq_e.2
          rw [← this] at hnv_inner
          simp [ToVal.toVal] at hnv_inner
        rename_i eouter einner
        obtain ⟨he0, hi⟩ := heq_e
        subst he0
        exact finish (.appR eouter) einner (by simp [ECtxItem.fill]) hi (by simp [eraseECtxItem])
      | unOp op1 =>
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rename_i op' einner
        obtain ⟨hop, hi⟩ := heq_e
        subst hop
        exact finish (.unOp op') einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | binOpL op1 v2 =>
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rename_i op' einner ea
        obtain ⟨hop, hi, ha⟩ := heq_e
        subst hop
        cases ea <;> simp [eraseExpr, erasedNewProph, eraseResolve] at ha
        rename_i v2'
        have ha' : eraseVal v2' = v2 := Exp.val.inj ha
        subst ha'
        exact finish (.binOpL op' v2') einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | binOpR op1 e0 =>
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rename_i op' eouter einner
        obtain ⟨hop, he0, hi⟩ := heq_e
        subst hop; subst he0
        exact finish (.binOpR op' eouter) einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | «if» e1' e2' =>
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rename_i einner ei1 ei2
        obtain ⟨hi, h1, h2⟩ := heq_e
        subst h1; subst h2
        exact finish (.if ei1 ei2) einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | pairL v2 =>
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rename_i einner ea
        obtain ⟨hi, ha⟩ := heq_e
        cases ea <;> simp [eraseExpr, erasedNewProph, eraseResolve] at ha
        rename_i v2'
        have ha' : eraseVal v2' = v2 := Exp.val.inj ha
        subst ha'
        exact finish (.pairL v2') einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | pairR e0 =>
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rename_i eouter einner
        obtain ⟨he0, hi⟩ := heq_e
        subst he0
        exact finish (.pairR eouter) einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | fst =>
        -- e1 could be `.fst einner` (normal case) or `.resolve r0 r1 r2`
        -- (special case, since resolve erases to `.fst (.fst ...)`).
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        · -- .fst einner case: straightforward IH application.
          rename_i einner
          exact finish .fst einner (by simp [ECtxItem.fill]) heq_e
            (by simp [eraseECtxItem])
        · -- .resolve r0 r1 r2 case.  We peel off the erased context frames
          -- one at a time from `Ks`.  The scaffolding `Ks` should look like
          -- `.fst :: .pairL _ :: .pairL _ :: K_inner` where `K_inner` is the
          -- context around one of `r0, r1, r2`.  If everything collapses to
          -- three values, we contradict `hns` via `Resolve_3_vals_unsafe`.
          rename_i r0 r1 r2
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
            -- heq_e : .fst (.pair (.pair X0 X1) X2) = Ki'.fill (fill Ks' e1')
            -- So the head of Ki'.fill must be `.fst`, hence Ki' = .fst.
            cases Ki' <;>
              first
                | (simp only [ECtxItem.fill] at heq_e; cases heq_e; done)
                | skip
            -- Only `.fst` remains.
            -- heq_e : .fst (.pair (.pair X0 X1) X2) = .fst (fill Ks' e1')
            -- Extract inner equation.
            simp only [ECtxItem.fill, Exp.fst.injEq] at heq_e
            -- heq_e : .pair (.pair X0 X1) X2 = fill Ks' e1'
            -- Now peel Ks' — its innermost frame must give a `.pair` head.
            cases Ks' using FromMathlib.List.reverseRec with
              | nil =>
                -- Ks' = []: e1' = .pair (.pair X0 X1) X2.  The only base step
                -- on `.pair` is `.pairS`, which needs `.val (.pair X0 X1)` on
                -- the left — impossible since our LHS is `.pair …`.
                simp only [fill_nil] at heq_e
                rw [← heq_e] at bstep
                cases bstep
              | append_singleton Ks'' Ki'' _ =>
                rw [fill_append, fill_cons, fill_nil,
                    show fillItem Ki'' = Ki''.fill from rfl] at heq_e
                -- heq_e : .pair (.pair X0 X1) X2 = Ki''.fill (fill Ks'' e1')
                -- Only `.pairL v` or `.pairR e` produce a `.pair` head.
                cases Ki'' with
                | appL _ => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | appR _ => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | unOp _ => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | binOpL _ _ => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | binOpR _ _ => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | «if» _ _ => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | fst => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | snd => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | injL => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | injR => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | case _ _ => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | allocNL _ => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | allocNR _ => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | free => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | load => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | storeL _ => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | storeR _ => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | xchgL _ => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | xchgR _ => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | cmpXchgL _ _ => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | cmpXchgM _ _ => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | cmpXchgR _ _ => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | faaL _ => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | faaR _ => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | resolveL _ _ _ => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | resolveM _ _ => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | resolveR _ _ => simp only [ECtxItem.fill] at heq_e; cases heq_e
                | pairL v_r2 =>
                  -- .pair (.pair X0 X1) X2 = .pair (fill Ks'' e1') (.ofVal v_r2)
                  simp only [ECtxItem.fill, Exp.pair.injEq] at heq_e
                  obtain ⟨hinner, hv2⟩ := heq_e
                  -- hv2 : X2 = .ofVal v_r2, i.e. eraseExpr r2 = .val v_r2.
                  -- Derive `r2 = .val w_r2` with `eraseVal w_r2 = v_r2`.
                  have hv2r : toVal (eraseExpr r2) = some v_r2 := by
                    rw [hv2]; rfl
                  obtain ⟨w_r2, hw_r2_some, hew_r2⟩ := toVal_erase_some hv2r
                  have hr2eq : r2 = .val w_r2 := by
                    cases r2 <;> simp [ToVal.toVal] at hw_r2_some
                    exact congrArg _ hw_r2_some
                  subst hr2eq
                  -- hinner : .pair X0 X1 = fill Ks'' e1'
                  cases Ks'' using FromMathlib.List.reverseRec with
                  | nil =>
                    -- Ks'' = []: e1' = .pair X0 X1; .pairS wants both .val.
                    simp only [fill_nil] at hinner
                    -- hinner : .pair (eraseExpr r0) (eraseExpr r1) = e1'.
                    -- The only BaseStep on a `.pair` is `.pairS`, which requires
                    -- both sides to be `.ofVal _`.  So eraseExpr r0 and
                    -- eraseExpr r1 are both values, hence r0, r1 are values.
                    have hnv_e1' : toVal e1' = none :=
                      EctxItemLanguage.val_stuck bstep
                    -- Prep: use `Exp.pair X Y` as the value form.  Show that any
                    -- successful BaseStep of `.pair X Y` implies both X, Y are
                    -- `.val _`.
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
                    -- hinner : .pair (eraseExpr r0) (eraseExpr r1) =
                    --          Ki'''.fill (fill Ks''' e1')
                    -- Only `.pairL v` or `.pairR e` give a `.pair` head.
                    rw [fill_append, fill_cons, fill_nil,
                        show fillItem Ki''' = Ki'''.fill from rfl] at hinner
                    cases Ki''' with
                    | appL _ => simp only [ECtxItem.fill] at hinner; cases hinner
                    | appR _ => simp only [ECtxItem.fill] at hinner; cases hinner
                    | unOp _ => simp only [ECtxItem.fill] at hinner; cases hinner
                    | binOpL _ _ => simp only [ECtxItem.fill] at hinner; cases hinner
                    | binOpR _ _ => simp only [ECtxItem.fill] at hinner; cases hinner
                    | «if» _ _ => simp only [ECtxItem.fill] at hinner; cases hinner
                    | fst => simp only [ECtxItem.fill] at hinner; cases hinner
                    | snd => simp only [ECtxItem.fill] at hinner; cases hinner
                    | injL => simp only [ECtxItem.fill] at hinner; cases hinner
                    | injR => simp only [ECtxItem.fill] at hinner; cases hinner
                    | case _ _ => simp only [ECtxItem.fill] at hinner; cases hinner
                    | allocNL _ => simp only [ECtxItem.fill] at hinner; cases hinner
                    | allocNR _ => simp only [ECtxItem.fill] at hinner; cases hinner
                    | free => simp only [ECtxItem.fill] at hinner; cases hinner
                    | load => simp only [ECtxItem.fill] at hinner; cases hinner
                    | storeL _ => simp only [ECtxItem.fill] at hinner; cases hinner
                    | storeR _ => simp only [ECtxItem.fill] at hinner; cases hinner
                    | xchgL _ => simp only [ECtxItem.fill] at hinner; cases hinner
                    | xchgR _ => simp only [ECtxItem.fill] at hinner; cases hinner
                    | cmpXchgL _ _ => simp only [ECtxItem.fill] at hinner; cases hinner
                    | cmpXchgM _ _ => simp only [ECtxItem.fill] at hinner; cases hinner
                    | cmpXchgR _ _ => simp only [ECtxItem.fill] at hinner; cases hinner
                    | faaL _ => simp only [ECtxItem.fill] at hinner; cases hinner
                    | faaR _ => simp only [ECtxItem.fill] at hinner; cases hinner
                    | resolveL _ _ _ => simp only [ECtxItem.fill] at hinner; cases hinner
                    | resolveM _ _ => simp only [ECtxItem.fill] at hinner; cases hinner
                    | resolveR _ _ => simp only [ECtxItem.fill] at hinner; cases hinner
                    | pairL v_r1 =>
                      -- hinner : .pair (eraseExpr r0) (eraseExpr r1) =
                      --          .pair (fill Ks''' e1') (.ofVal v_r1)
                      simp only [ECtxItem.fill, Exp.pair.injEq] at hinner
                      obtain ⟨hi, hv1⟩ := hinner
                      have hv1r : toVal (eraseExpr r1) = some v_r1 := by
                        rw [hv1]; rfl
                      obtain ⟨w_r1, hw_r1_some, hew_r1⟩ := toVal_erase_some hv1r
                      have hr1eq : r1 = .val w_r1 := by
                        cases r1 <;> simp [ToVal.toVal] at hw_r1_some
                        exact congrArg _ hw_r1_some
                      subst hr1eq
                      -- TODO: recurse on r0.  Unlike the r1 and r2 cases,
                      -- there is no single-frame ECtxItem that fills at the
                      -- r0 position of `.resolve r0 v1 v2`: the only wrapper
                      -- is `.resolveL K v1 v2` which itself embeds a nested
                      -- context `K`.  The construction therefore has to
                      -- unpack IHapp's inner primStep on r0 as
                      --   ⟨e_h1, e_h2, K_r0, hbstep⟩,
                      -- and split on `K_r0`:
                      -- * K_r0 = K_rest ++ [Ki_top]: outer primStep is
                      --   `ContextStep.ofBaseStep
                      --      (K_rest ++ [.resolveL Ki_top w_r1 w_r2]) hbstep`.
                      -- * K_r0 = []: r0 base-steps at head.  Must derive
                      --   `.resolve r0 v1 v2` reducibility from `hns`; only
                      --   possible via `resolveS`, needing w_r1 = prophecy p
                      --   ∈ σ1.usedProphId and r0 base-stepping to a value.
                      -- Also needs `NotStuck (r0, σ1)`, which itself requires
                      -- inspecting `hns`'s primStep decomposition to rule out
                      -- the `resolveS` path (or handle it directly).
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
                          -- .resolve r0 (.val w_r1) (.val w_r2) = he1_h and it base-steps
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
                      -- Length bookkeeping for IHapp.
                      have hlk : Ks'''.length ≤
                          (Ks''' ++ [ECtxItem.pairL v_r1] ++
                           [ECtxItem.pairL v_r2] ++ [ECtxItem.fst]).length := by
                        simp
                      have hmatch := IHapp hlk hi hns_r0
                      -- Unpack the matching result on r0.
                      obtain ⟨e_r0_next, σ_r0, κ_r0, efs_r0, e_matched,
                              hstep_r0, hpure_r0, hex_r0, hσ_r0, hef_r0⟩ := hmatch
                      -- Prep for target reconstruction (subst hew_r1/r2 to align).
                      subst hew_r1
                      subst hew_r2
                      -- Destructure the primStep on r0 as a ContextStep.
                      -- Note: e_r0_next is substituted to `fill K_r0 inner_e2`.
                      obtain @⟨inner_e1, inner_e2, K_r0, hbstep_r0⟩ := hstep_r0
                      -- Case-split on K_r0.
                      cases K_r0 using FromMathlib.List.reverseRec with
                      | nil =>
                        -- K_r0 = [] sub-case.  r0 = inner_e1 base-steps at head
                        -- via `hbstep_r0`, so e_r0_next = fill [] inner_e2 = inner_e2.
                        -- The outer `.resolve r0 (.val w_r1) (.val w_r2)` must
                        -- primStep.  We decompose `hns` to extract that the outer
                        -- step is via `resolveS`, which yields:
                        --   * w_r1 = .lit (.prophecy p) with p ∈ σ1.usedProphId,
                        --   * some base step of r0 produces a value.
                        -- Since bs_inner from hns gives us r0 has a value-producing
                        -- base step, and the shape of r0 (determined by hbstep_r0)
                        -- constrains its base steps, hbstep_r0 also produces a
                        -- value (either it is the same as bs_inner up to state, or
                        -- both are of the shape whose steps all produce values).
                        simp only [fill_nil] at hbstep_r0 hex_r0 hns
                        -- Extract prophecy info + witness that r0 has some
                        -- value-producing base step from `hns`.
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
                              -- inner_e1 = ctx.fill (fill K_rest he1_h) where
                              -- he1_h base-steps.  But inner_e1 also base-steps
                              -- via hbstep_r0.  Apply base_ctx_step_val to derive
                              -- that fill K_rest he1_h is a value — contradicting
                              -- hnv_h through fill_not_val.
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
                        -- Show that hbstep_r0 also produces a value.  We case-
                        -- split on hbstep_r0's constructor; for each non-value-
                        -- producing shape, bs_inner_hns yields a contradiction
                        -- because r0's shape admits only that non-value step.
                        have hval_target : ∃ v : Val, inner_e2 = .val v := by
                          -- Strategy: case on hbstep_r0.  In cases where inner_e2 is
                          -- immediately a value, produce it directly.  In other cases
                          -- (betaS, ifTrueS, ifFalseS, caseLS, caseRS), case-split
                          -- bs_inner_hns further; both base steps have the same
                          -- shape (same LHS), and bs_inner_hns forces the (shape-
                          -- determined) target to be a value.  For betaS both
                          -- substitutions coincide (deterministic), so we transit.
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
                        -- Now construct the outer primStep via resolveS.
                        refine ⟨.val v_target, σ_r0, κ_r0 ++ [(p, (v_target, w_r2))],
                                efs_r0, .val (eraseVal v_target), ?_, ?_, ?_,
                                hσ_r0, hef_r0⟩
                        · -- outer primStep: use resolveS with hbstep_r0.
                          exact BaseStep.ContextStep.ofBaseStep []
                            (BaseStep.resolveS p v_target inner_e1 σ1 w_r2 σ_r0
                              κ_r0 efs_r0 hbstep_r0 hused)
                        · -- pure steps: lift hpure_r0 through the erased
                          -- projection context, then apply projs_pure_steps.
                          have hlift :=
                            ReflTransGen_pureStep_fill
                              (K := fill (Expr := Exp)
                                     [ECtxItem.pairL (eraseVal (.lit (.prophecy p))),
                                      ECtxItem.pairL (eraseVal w_r2),
                                      ECtxItem.fst, ECtxItem.fst])
                              hpure_r0
                          -- Massage the LHS of hlift to the target shape.
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
                          -- e_matched = eraseExpr (.val v_target) =
                          --             .val (eraseVal v_target)
                          have he_matched :
                              e_matched = .val (eraseVal v_target) := by
                            rw [← hex_r0]; rfl
                          rw [hLHS_eq, he_matched] at hlift
                          -- After hlift, we've reached the shape
                          -- .fst (.fst (.pair (.pair (.val (eraseVal v_target))
                          --                          (.val (eraseVal (prophecy p))))
                          --                   (.val (eraseVal w_r2)))).
                          -- Apply projs_pure_steps.
                          have hproj :=
                            projs_pure_steps (eraseVal v_target)
                              (eraseVal (.lit (.prophecy p)))
                              (eraseVal w_r2)
                          -- Chain hlift and hproj; but first make LHS shape match.
                          simp only [fill_cons, fill_nil, fillItem, ECtxItem.fill]
                            at hlift
                          exact hlift.trans hproj
                        · -- erase eq: eraseExpr (.val v_target) = .val (eraseVal v_target)
                          rfl
                      | append_singleton K_r0_rest Ki_r0_top _ =>
                        -- Non-empty K_r0.  Wrap via `.resolveL Ki_r0_top w_r1 w_r2`.
                        -- Assemble the outer primStep.
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
                        -- Assemble PrimStepMatchedByErasedSteps.
                        refine ⟨Exp.resolve
                                  (fill (K_r0_rest ++ [Ki_r0_top]) inner_e2)
                                  (.val w_r1) (.val w_r2),
                                σ_r0, κ_r0, efs_r0,
                                eraseExpr (Exp.resolve
                                  (fill (K_r0_rest ++ [Ki_r0_top]) inner_e2)
                                  (.val w_r1) (.val w_r2)),
                                ?_, ?_, rfl, hσ_r0, hef_r0⟩
                        · -- outer primStep: wrap hbstep_r0 in
                          -- (K_r0_rest ++ [.resolveL Ki_r0_top w_r1 w_r2]).
                          have hs :=
                            BaseStep.ContextStep.ofBaseStep
                              (K := K_r0_rest ++ [ECtxItem.resolveL Ki_r0_top w_r1 w_r2])
                              hbstep_r0
                          rw [hfill_eq, hfill_eq2] at hs
                          exact hs
                        · -- pure matching: need
                          --   ReflTransGen PurePrimStep
                          --     (fill (Ks''' ++ [.pairL v_r1] ++ [.pairL v_r2]
                          --                 ++ [.fst] ++ [.fst]) e2')
                          --     (eraseExpr (.resolve e_r0_next (.val w_r1) (.val w_r2)))
                          -- We have hpure_r0 : ReflTransGen PurePrimStep
                          --   (fill Ks''' e2') e_matched, with eraseExpr e_r0_next
                          --   = e_matched (from hex_r0).
                          -- Lift hpure_r0 through the fill context.
                          have hlift :=
                            ReflTransGen_pureStep_fill
                              (K := fill (Expr := Exp)
                                     [ECtxItem.pairL (eraseVal w_r1),
                                      ECtxItem.pairL (eraseVal w_r2),
                                      ECtxItem.fst, ECtxItem.fst])
                              hpure_r0
                          -- Massage LHS.
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
                                  fillItem, ECtxItem.fill, eraseVal]
                          rw [hLHS_pure, hRHS_pure] at hlift
                          exact hlift
                    | pairR e_r0 =>
                      -- hinner : .pair (eraseExpr r0) (eraseExpr r1) =
                      --          .pair e_r0 (fill Ks''' e1')
                      simp only [ECtxItem.fill, Exp.pair.injEq] at hinner
                      obtain ⟨he_r0, hi⟩ := hinner
                      subst he_r0
                      -- hi : eraseExpr r1 = fill Ks''' e1'
                      -- Derive NotStuck (r1, σ1) via
                      -- `.resolve r0 r1 (.val w_r2) = fill [.resolveM r0 w_r2] r1`.
                      have hns_r1 : PrimStep.NotStuck (r1, σ1) := by
                        have heq : (Exp.resolve r0 r1 (.val w_r2)) =
                                   fill [ECtxItem.resolveM r0 w_r2] r1 := by
                          simp [fill_cons, fill_nil, fillItem, ECtxItem.fill]
                        rw [heq] at hns
                        exact Language.Context.notStuck_fill_inv
                          (K := fill [ECtxItem.resolveM r0 w_r2]) hns
                      -- Length bookkeeping.
                      have hlk : Ks'''.length ≤
                          (Ks''' ++ [ECtxItem.pairR (eraseExpr r0)] ++
                           [ECtxItem.pairL v_r2] ++ [ECtxItem.fst]).length := by
                        simp
                      have hmatch := IHapp hlk hi hns_r1
                      -- Lift through single-frame `.resolveM r0 w_r2`.
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
                      -- Reconcile with target's context list decomposition.
                      -- Target: fill (Ks''' ++ [.pairL v_r1, .pairL v_r2,
                      --                        .fst, .fst]) e2'.  But here we
                      -- wrapped via `.resolveM`, which erases to
                      -- `[.pairR e_r0, .pairL v_r2, .fst, .fst]` — differing
                      -- in the first frame (pairL v_r1 vs pairR (eraseExpr r0)).
                      -- The target frame comes from Ki'' = .pairL v_r2 at the
                      -- Ks' level, then Ki''' = .pairR (eraseExpr r0) at the
                      -- Ks'' level (which we're in).  So the target is
                      -- fill (Ks''' ++ [.pairR (eraseExpr r0), .pairL v_r2,
                      --                 .fst, .fst]) e2'.  We have exactly
                      -- that, modulo `eraseVal w_r2 = v_r2`.
                      subst hew_r2
                      exact hlift
                | pairR e_outer =>
                  -- heq_e : .pair (.pair X0 X1) X2 =
                  --         .pair e_outer (fill Ks'' e1')
                  simp only [ECtxItem.fill, Exp.pair.injEq] at heq_e
                  obtain ⟨he_outer, hi⟩ := heq_e
                  subst he_outer
                  -- hi : eraseExpr r2 = fill Ks'' e1'
                  -- Derive NotStuck (r2, σ1) via
                  -- `.resolve r0 r1 r2 = fill [.resolveR r0 r1] r2`.
                  have hns_r2 : PrimStep.NotStuck (r2, σ1) := by
                    have heq : (Exp.resolve r0 r1 r2) =
                               fill [ECtxItem.resolveR r0 r1] r2 := by
                      simp [fill_cons, fill_nil, fillItem, ECtxItem.fill]
                    rw [heq] at hns
                    exact Language.Context.notStuck_fill_inv
                      (K := fill [ECtxItem.resolveR r0 r1]) hns
                  -- Length bookkeeping: current top-level Ks is
                  -- `Ks'' ++ [.pairR (.pair (eraseExpr r0) (eraseExpr r1))] ++ [.fst]`,
                  -- so Ks''.length ≤ Ks.length.
                  have hlk : Ks''.length ≤ (Ks'' ++ [ECtxItem.pairR
                                (.pair (eraseExpr r0) (eraseExpr r1))] ++
                                [ECtxItem.fst]).length := by
                    simp
                  have hmatch := IHapp hlk hi hns_r2
                  -- Lift through the single-frame `.resolveR r0 r1`.
                  have hlift := hmatch.fill_ctx [ECtxItem.resolveR r0 r1]
                  -- Massage LHS/RHS to the required shape.
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
      | snd =>
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rename_i einner
        exact finish .snd einner (by simp [ECtxItem.fill]) heq_e
          (by simp [eraseECtxItem])
      | injL =>
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rename_i einner
        exact finish .injL einner (by simp [ECtxItem.fill]) heq_e
          (by simp [eraseECtxItem])
      | injR =>
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rename_i einner
        exact finish .injR einner (by simp [ECtxItem.fill]) heq_e
          (by simp [eraseECtxItem])
      | case ec1 ec2 =>
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rename_i einner ei1 ei2
        obtain ⟨hi, h1, h2⟩ := heq_e
        subst h1; subst h2
        exact finish (.case ei1 ei2) einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | allocNL v2 =>
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rename_i einner ea
        obtain ⟨hi, ha⟩ := heq_e
        cases ea <;> simp [eraseExpr, erasedNewProph, eraseResolve] at ha
        rename_i v2'
        have ha' : eraseVal v2' = v2 := Exp.val.inj ha
        subst ha'
        exact finish (.allocNL v2') einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | allocNR e0 =>
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rename_i eouter einner
        obtain ⟨he0, hi⟩ := heq_e
        subst he0
        exact finish (.allocNR eouter) einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | free =>
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rename_i einner
        exact finish .free einner (by simp [ECtxItem.fill]) heq_e
          (by simp [eraseECtxItem])
      | load =>
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rename_i einner
        exact finish .load einner (by simp [ECtxItem.fill]) heq_e
          (by simp [eraseECtxItem])
      | storeL v2 =>
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rename_i einner ea
        obtain ⟨hi, ha⟩ := heq_e
        cases ea <;> simp [eraseExpr, erasedNewProph, eraseResolve] at ha
        rename_i v2'
        have ha' : eraseVal v2' = v2 := Exp.val.inj ha
        subst ha'
        exact finish (.storeL v2') einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | storeR e0 =>
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rename_i eouter einner
        obtain ⟨he0, hi⟩ := heq_e
        subst he0
        exact finish (.storeR eouter) einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | xchgL v2 =>
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rename_i einner ea
        obtain ⟨hi, ha⟩ := heq_e
        cases ea <;> simp [eraseExpr, erasedNewProph, eraseResolve] at ha
        rename_i v2'
        have ha' : eraseVal v2' = v2 := Exp.val.inj ha
        subst ha'
        exact finish (.xchgL v2') einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | xchgR e0 =>
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rename_i eouter einner
        obtain ⟨he0, hi⟩ := heq_e
        subst he0
        exact finish (.xchgR eouter) einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | cmpXchgL v1 v2 =>
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rename_i einner ea1 ea2
        obtain ⟨hi, ha1, ha2⟩ := heq_e
        cases ea1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at ha1
        cases ea2 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at ha2
        rename_i v1' v2'
        have ha1' : eraseVal v1' = v1 := Exp.val.inj ha1
        have ha2' : eraseVal v2' = v2 := Exp.val.inj ha2
        subst ha1'; subst ha2'
        exact finish (.cmpXchgL v1' v2') einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | cmpXchgM e0 v2 =>
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rename_i eouter einner ea
        obtain ⟨he0, hi, ha⟩ := heq_e
        subst he0
        cases ea <;> simp [eraseExpr, erasedNewProph, eraseResolve] at ha
        rename_i v2'
        have ha' : eraseVal v2' = v2 := Exp.val.inj ha
        subst ha'
        exact finish (.cmpXchgM eouter v2') einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | cmpXchgR eA eB =>
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rename_i eouter0 eouter1 einner
        obtain ⟨he0, he1, hi⟩ := heq_e
        subst he0; subst he1
        exact finish (.cmpXchgR eouter0 eouter1) einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | faaL v2 =>
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rename_i einner ea
        obtain ⟨hi, ha⟩ := heq_e
        cases ea <;> simp [eraseExpr, erasedNewProph, eraseResolve] at ha
        rename_i v2'
        have ha' : eraseVal v2' = v2 := Exp.val.inj ha
        subst ha'
        exact finish (.faaL v2') einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | faaR e0 =>
        simp only [ECtxItem.fill] at heq_e
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
        rename_i eouter einner
        obtain ⟨he0, hi⟩ := heq_e
        subst he0
        exact finish (.faaR eouter) einner (by simp [ECtxItem.fill]) hi
          (by simp [eraseECtxItem])
      | resolveL Kres v1 v2 =>
        -- The erased expression never contains `.resolve`, so this Ki is
        -- impossible: `Ki.fill x = .resolve ...` cannot equal `eraseExpr e1`.
        simp only [ECtxItem.fill] at heq_e
        exfalso
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
      | resolveM e0 v2 =>
        simp only [ECtxItem.fill] at heq_e
        exfalso
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e
      | resolveR e0 e1outer =>
        simp only [ECtxItem.fill] at heq_e
        exfalso
        cases e1 <;> simp [eraseExpr, erasedNewProph, eraseResolve] at heq_e

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
  obtain ⟨l2, l2', hl2, hpr1, hpr2, hlen⟩ := Iris.Std.List.exists_of_forall₂_append Hpr
  obtain ⟨e2, l2'', rfl, hpstep, _⟩ := Iris.Std.List.exists_of_forall₂_cons hpr2
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
        refine Iris.Std.List.Forall₂.append ?_ (pureSteps_refl _)
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
      Iris.Std.List.exists_of_forall₂_cons hpr
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
