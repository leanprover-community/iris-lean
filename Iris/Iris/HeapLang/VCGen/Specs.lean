/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

public import Iris.ProgramLogic.VCGen.WP
public import Iris.HeapLang.VCGen.Subst
public import Iris.HeapLang.ProofMode
public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.Instances

@[expose] public section

/-!
# `vcgen` specifications for HeapLang

The HeapLang program type is `HLProg GF = IrisProg GF Exp`, interpreted by the HeapLang weakest
precondition. `vcgen` decomposes a program `⟪e @ s ; E⟫` by the specifications of this file, keyed on
the constructors of `Exp`:

* **Values.** `ofVal v` establishes `Q v`.
* **Evaluation contexts.** `Exp.load e` evaluates `e` to a value `w` first and continues with
  `Exp.load (ofVal w)`. A context specification has a lower priority than every specification
  for the value form, so the value form wins once the subexpression is a value. Application
  spines `f e₁ e₂` keep their shape until every position is a value, so a specification of the
  call `f v₁ v₂` matches the whole call.
* **Pure steps.** `rec`, β-reduction, `if` on a boolean literal and integer arithmetic step to
  their reduct. A step drops the later modality that iris attaches to it (`P ⊢ ▷ P`).
* **Substitution.** β-reduction of `rec f x e` applied to `v` continues with
  `msubst [(f, rec f x e), (x, v)] e`. The equations `msubst_*_eq` push the substitution into `e`
  one constructor at a time, so `vcgen` substitutes exactly as far as evaluation demands. A
  variable splits on string equality, and the split on two distinct literals keeps one branch.
* **Heap.** `load`, `store` and `ref` are specified in continuation form, as iris's Texan triples:
  `l ↦ v ∗ (l ↦ v -∗ Q v)` for `!#l`. The continuation receives the loaded value `v` itself, so
  later specifications match on it.

Every specification is stated over `PROP := IProp GF` with the lattice of `Iris.VCGen.Lattice`.
-/

open Iris Iris.BI Iris.ProgramLogic Iris.HeapLang Iris.VCGen Lean.Order Std.WP

namespace Iris.HeapLang.VCGen

/-- A HeapLang program with assertions in `IProp GF`. -/
abbrev HLProg (GF : BundledGFunctors) := IrisProg GF Exp

/-- A HeapLang value as an expression. -/
local notation "ov " v:max => (ToVal.ofVal (Expr := Exp) v)

variable {hlc : HasLC} {GF : BundledGFunctors} [HeapLangGS hlc GF] {s : Stuckness} {E : CoPset}
  {Q : Val → IProp GF} {ε : EStack⟨⟩}

/-- The `Std.WP` weakest precondition of a HeapLang expression at the section's `GF`, `s`, `E`. -/
scoped syntax "hwp " term:max ppSpace term:max : term

/-- The `Std.WP` weakest precondition of a HeapLang program at the section's `GF`, `s`, `E`. -/
local syntax "pwp " term:max ppSpace term:max : term

/-- A HeapLang triple at the section's `GF`, `s`, `E`. -/
scoped syntax "htriple " term:max ppSpace term:max ppSpace term:max : term

set_option hygiene false in
macro_rules
  | `(hwp $e $Q) => `(@Std.WP.WP.wp (HLProg GF) _ _ _ _ _ _ ⟪$e @ s ; E⟫ $Q ε)
  | `(pwp $p $Q) => `(@Std.WP.WP.wp (HLProg GF) _ _ _ _ _ _ $p $Q ε)
  | `(htriple $e $P $Q) => `(Triple (Prog := HLProg GF) ⟪$e @ s ; E⟫ $P $Q ε)

/-- The HeapLang triple `hl⦃ P ⦄ e @ s ; E ⦃ Q ⦄`, after iris's `{P} e @ s ; E {Q}`. The program
part takes every form of `⟪·⟫`: `hl⦃ P ⦄ e ⦃ Q ⦄` is at stuckness `NotStuck` and mask `⊤`. The
resource functors are the variable `GF` in scope. -/
syntax:60 "hl⦃ " term " ⦄ " wpExpr " ⦃ " term " ⦄" : term

set_option hygiene false in
macro_rules
  | `(hl⦃ $P ⦄ $w:wpExpr ⦃ $Q ⦄) =>
    `(Std.WP.Triple (Prog := Iris.HeapLang.VCGen.HLProg GF) ⟪$w⟫ $P $Q Lean.Order.bot)

theorem hwp_eq (e : Exp) (Q : Val → IProp GF) :
    hwp e Q = Wp.wp (PROP := IProp GF) s E e Q := rfl

theorem triple_of_entails {e : Exp} {P : IProp GF} (h : P ⊢ Wp.wp (PROP := IProp GF) s E e Q) :
    htriple e P Q :=
  ⟨h⟩

/-! ## Values and pure steps -/

@[spec] theorem val_spec (v : Val) : htriple (ov v) (Q v) Q :=
  triple_of_entails wp_value'

theorem pure_spec {φ : Prop} {n : Nat} {e₁ e₂ : Exp} [Language.PureExec φ n e₁ e₂] (h : φ) :
    htriple e₁ (hwp e₂ Q) Q := by
  refine triple_of_entails (BIBase.Entails.trans ?_ (wp_pure_step_later h))
  refine BIBase.Entails.trans ?_ (laterN_intro n)
  exact wand_intro sep_elim_left

theorem pure_val_spec {φ : Prop} {n : Nat} {e₁ : Exp} {v : Val} [hpe : Language.PureExec φ n e₁ (ov v)]
    (h : φ) : htriple e₁ (Q v) Q :=
  ⟨BIBase.Entails.trans (val_spec (Q := Q) (s := s) (E := E) (ε := ε) v).le_wp
    (pure_spec (e₁ := e₁) h).le_wp⟩

@[spec] theorem rec_spec (f x : Binder) (e : Exp) :
    htriple (Exp.rec_ f x e) (Q (.rec_ f x e)) Q :=
  pure_val_spec trivial

/-! ## β-reduction

A closure value `rec f y e` applied to `w` continues with `msubst σ e`, where `σ` holds the
entries for the binders `f` and `y`. A closure built under a substitution has the body
`msubst (dropB f y σ) e`; its β-reduction conses the binder entries onto `σ` itself. There is
one specification per shape of the two binders, so that `σ` is always a literal list. -/

theorem beta_triple (f y : Binder) (e : Exp) (v : Val) :
    htriple (Exp.app (ov (Val.rec_ f y e)) (ov v))
      (hwp (msubst (consB f (.rec_ f y e) (consB y v [])) e) Q) Q := by
  rw [← beta_eq]
  exact pure_spec (e₁ := Exp.app (ov (Val.rec_ f y e)) (ov v)) trivial

theorem beta_msubst_triple (f y : Binder) (σ : List (String × Val)) (e : Exp) (v : Val) :
    htriple (Exp.app (ov (Val.rec_ f y (msubst (dropB f y σ) e))) (ov v))
      (hwp (msubst (consB f (.rec_ f y (msubst (dropB f y σ) e)) (consB y v σ)) e) Q) Q := by
  rw [← beta_msubst_eq]
  exact pure_spec (e₁ := Exp.app (ov (Val.rec_ f y (msubst (dropB f y σ) e))) (ov v)) trivial

@[spec] theorem beta_aa_spec (e : Exp) (v : Val) :
    htriple (Exp.app (ov (Val.rec_ .anon .anon e)) (ov v)) (hwp e Q) Q := by
  have := beta_triple (Q := Q) (s := s) (E := E) (ε := ε) .anon .anon e v
  simpa [consB, msubst_nil] using this

@[spec] theorem beta_an_spec (y : String) (e : Exp) (v : Val) :
    htriple (Exp.app (ov (Val.rec_ .anon (.named y) e)) (ov v)) (hwp (msubst [(y, v)] e) Q) Q :=
  beta_triple .anon (.named y) e v

@[spec] theorem beta_na_spec (f : String) (e : Exp) (v : Val) :
    htriple (Exp.app (ov (Val.rec_ (.named f) .anon e)) (ov v))
      (hwp (msubst [(f, .rec_ (.named f) .anon e)] e) Q) Q :=
  beta_triple (.named f) .anon e v

@[spec] theorem beta_nn_spec (f y : String) (e : Exp) (v : Val) :
    htriple (Exp.app (ov (Val.rec_ (.named f) (.named y) e)) (ov v))
      (hwp (msubst [(f, .rec_ (.named f) (.named y) e), (y, v)] e) Q) Q :=
  beta_triple (.named f) (.named y) e v

@[spec high] theorem beta_msubst_aa_spec (σ : List (String × Val)) (e : Exp) (v : Val) :
    htriple (Exp.app (ov (Val.rec_ .anon .anon (msubst (dropB .anon .anon σ) e))) (ov v))
      (hwp (msubst σ e) Q) Q :=
  beta_msubst_triple .anon .anon σ e v

@[spec high] theorem beta_msubst_an_spec (y : String) (σ : List (String × Val)) (e : Exp)
    (v : Val) :
    htriple (Exp.app (ov (Val.rec_ .anon (.named y) (msubst (dropB .anon (.named y) σ) e))) (ov v))
      (hwp (msubst ((y, v) :: σ) e) Q) Q :=
  beta_msubst_triple .anon (.named y) σ e v

@[spec high] theorem beta_msubst_na_spec (f : String) (σ : List (String × Val)) (e : Exp)
    (v : Val) :
    htriple (Exp.app (ov (Val.rec_ (.named f) .anon (msubst (dropB (.named f) .anon σ) e))) (ov v))
      (hwp (msubst ((f, .rec_ (.named f) .anon (msubst (dropB (.named f) .anon σ) e)) :: σ) e)
        Q) Q :=
  beta_msubst_triple (.named f) .anon σ e v

@[spec high] theorem beta_msubst_nn_spec (f y : String) (σ : List (String × Val)) (e : Exp)
    (v : Val) :
    htriple
      (Exp.app (ov (Val.rec_ (.named f) (.named y) (msubst (dropB (.named f) (.named y) σ) e)))
        (ov v))
      (hwp (msubst ((f, .rec_ (.named f) (.named y) (msubst (dropB (.named f) (.named y) σ) e)) ::
        (y, v) :: σ) e) Q) Q :=
  beta_msubst_triple (.named f) (.named y) σ e v

@[spec] theorem if_spec (b : Bool) (e₁ e₂ : Exp) :
    htriple (Exp.if (ov (Val.lit (.bool b))) e₁ e₂)
      (pwp (bif b then ⟪e₁ @ s ; E⟫ else ⟪e₂ @ s ; E⟫) Q) Q := by
  cases b
  · exact pure_spec (e₁ := Exp.if (ov (Val.lit (.bool false))) e₁ e₂) trivial
  · exact pure_spec (e₁ := Exp.if (ov (Val.lit (.bool true))) e₁ e₂) trivial

theorem binop_spec (op : BinOp) (v₁ v₂ v : Val) (h : op.eval v₁ v₂ = some v) :
    htriple (Exp.binop op (ov v₁) (ov v₂)) (Q v) Q :=
  pure_val_spec (n := 1) (e₁ := Exp.binop op (ov v₁) (ov v₂)) (hpe := instPureExecBinOp) h

@[spec] theorem plus_spec (a b : Int) :
    htriple (Exp.binop .plus (ov (.lit (.int a))) (ov (.lit (.int b)))) (Q (.lit (.int (a + b)))) Q :=
  binop_spec _ _ _ _ rfl

@[spec] theorem minus_spec (a b : Int) :
    htriple (Exp.binop .minus (ov (.lit (.int a))) (ov (.lit (.int b)))) (Q (.lit (.int (a - b)))) Q :=
  binop_spec _ _ _ _ rfl

@[spec] theorem mult_spec (a b : Int) :
    htriple (Exp.binop .mult (ov (.lit (.int a))) (ov (.lit (.int b)))) (Q (.lit (.int (a * b)))) Q :=
  binop_spec _ _ _ _ rfl

@[spec] theorem lt_spec (a b : Int) :
    htriple (Exp.binop .lt (ov (.lit (.int a))) (ov (.lit (.int b))))
      (Q (.lit (.bool (decide (a < b))))) Q :=
  binop_spec _ _ _ _ rfl

@[spec] theorem le_spec (a b : Int) :
    htriple (Exp.binop .le (ov (.lit (.int a))) (ov (.lit (.int b))))
      (Q (.lit (.bool (decide (a ≤ b))))) Q :=
  binop_spec _ _ _ _ rfl

-- `vcgen` reduces an equation between two literal values to an equation between their contents.
attribute [vcgen_simp] Val.lit.injEq BaseLit.loc.injEq BaseLit.int.injEq

/-! ## Evaluation contexts

`Ki.fill e` evaluates `e` first. The specifications have low priority, so that a specification
for the value form `Ki.fill (ov v)` applies whenever there is one. HeapLang evaluates right to
left: a right context item such as `appR e₁` focuses a nonvalue `e₂` in `Exp.app e₁ e₂`. Once `e₂`
is a value, the left context item `appL v` focuses `e₁`, so the left items take priority over the
right items. -/

theorem fill_spec (Ki : ECtxItem) (e : Exp) :
    htriple (Ki.fill e) (hwp e fun w => hwp (Ki.fill (ov w)) Q) Q :=
  triple_of_entails (BIBase.Entails.trans .rfl (wp_bind (ProgramLogic.fill [Ki])))

@[spec low] theorem appR_spec (e₁ e₂ : Exp) :
    htriple (Exp.app e₁ e₂) (hwp e₂ fun w => hwp (Exp.app e₁ (ov w)) Q) Q :=
  fill_spec (.appR e₁) e₂

@[spec mid] theorem appL_spec (e₁ : Exp) (v : Val) :
    htriple (Exp.app e₁ (ov v)) (hwp e₁ fun w => hwp (Exp.app (ov w) (ov v)) Q) Q :=
  fill_spec (.appL v) e₁

/-! Calls keep their application spine. HeapLang evaluates `f e₁ e₂` as `e₂`, then `e₁`, then
`f`. The spine specifications evaluate these positions while keeping the spine intact, and enter
the call only once the whole spine `app (app (ov f) (ov v₁)) (ov v₂)` consists of values. A
specification for the call `f v₁ v₂` (priority 1000) then matches the whole spine.

A spine specification's pattern also matches spines whose focused position is a value, so each
position has a higher priority than the position evaluated before it:

| priority | spine `app (app f e₁) e₂`              | three arguments |
| -------- | -------------------------------------- | --------------- |
| 650/800  | focus `e₁`                             | `appR₂`/`appR₃` |
| 750/850  | focus `f`                              | `appF₂`/`appF₃` |
| 900/950  | all values: enter `f v₁`               | `appV₂`/`appV₃` | -/

@[spec 650] theorem appR₂_spec (f e₁ : Exp) (v₂ : Val) :
    htriple (Exp.app (Exp.app f e₁) (ov v₂))
      (hwp e₁ fun w => hwp (Exp.app (Exp.app f (ov w)) (ov v₂)) Q) Q :=
  triple_of_entails (BIBase.Entails.trans .rfl
    (wp_bind (ProgramLogic.fill [ECtxItem.appR f, ECtxItem.appL v₂])))

@[spec 750] theorem appF₂_spec (f : Exp) (v₁ v₂ : Val) :
    htriple (Exp.app (Exp.app f (ov v₁)) (ov v₂))
      (hwp f fun w => hwp (Exp.app (Exp.app (ov w) (ov v₁)) (ov v₂)) Q) Q :=
  triple_of_entails (BIBase.Entails.trans .rfl
    (wp_bind (ProgramLogic.fill [ECtxItem.appL v₁, ECtxItem.appL v₂])))

@[spec 900] theorem appV₂_spec (f v₁ v₂ : Val) :
    htriple (Exp.app (Exp.app (ov f) (ov v₁)) (ov v₂))
      (hwp (Exp.app (ov f) (ov v₁)) fun w => hwp (Exp.app (ov w) (ov v₂)) Q) Q :=
  fill_spec (.appL v₂) (Exp.app (ov f) (ov v₁))

@[spec 800] theorem appR₃_spec (f e₁ : Exp) (v₂ v₃ : Val) :
    htriple (Exp.app (Exp.app (Exp.app f e₁) (ov v₂)) (ov v₃))
      (hwp e₁ fun w => hwp (Exp.app (Exp.app (Exp.app f (ov w)) (ov v₂)) (ov v₃)) Q) Q :=
  triple_of_entails (BIBase.Entails.trans .rfl
    (wp_bind (ProgramLogic.fill [ECtxItem.appR f, ECtxItem.appL v₂, ECtxItem.appL v₃])))

@[spec 850] theorem appF₃_spec (f : Exp) (v₁ v₂ v₃ : Val) :
    htriple (Exp.app (Exp.app (Exp.app f (ov v₁)) (ov v₂)) (ov v₃))
      (hwp f fun w => hwp (Exp.app (Exp.app (Exp.app (ov w) (ov v₁)) (ov v₂)) (ov v₃)) Q) Q :=
  triple_of_entails (BIBase.Entails.trans .rfl
    (wp_bind (ProgramLogic.fill [ECtxItem.appL v₁, ECtxItem.appL v₂, ECtxItem.appL v₃])))

@[spec 950] theorem appV₃_spec (f v₁ v₂ v₃ : Val) :
    htriple (Exp.app (Exp.app (Exp.app (ov f) (ov v₁)) (ov v₂)) (ov v₃))
      (hwp (Exp.app (Exp.app (ov f) (ov v₁)) (ov v₂)) fun w => hwp (Exp.app (ov w) (ov v₃)) Q) Q :=
  fill_spec (.appL v₃) (Exp.app (Exp.app (ov f) (ov v₁)) (ov v₂))

@[spec low] theorem binOpR_spec (op : BinOp) (e₁ e₂ : Exp) :
    htriple (Exp.binop op e₁ e₂) (hwp e₂ fun w => hwp (Exp.binop op e₁ (ov w)) Q) Q :=
  fill_spec (.binOpR op e₁) e₂

@[spec mid] theorem binOpL_spec (op : BinOp) (e₁ : Exp) (v : Val) :
    htriple (Exp.binop op e₁ (ov v)) (hwp e₁ fun w => hwp (Exp.binop op (ov w) (ov v)) Q) Q :=
  fill_spec (.binOpL op v) e₁

@[spec low] theorem if_ctx_spec (e₀ e₁ e₂ : Exp) :
    htriple (Exp.if e₀ e₁ e₂) (hwp e₀ fun w => hwp (Exp.if (ov w) e₁ e₂) Q) Q :=
  fill_spec (.if e₁ e₂) e₀

@[spec low] theorem load_ctx_spec (e : Exp) :
    htriple (Exp.load e) (hwp e fun w => hwp (Exp.load (ov w)) Q) Q :=
  fill_spec .load e

@[spec low] theorem storeR_spec (e₁ e₂ : Exp) :
    htriple (Exp.store e₁ e₂) (hwp e₂ fun w => hwp (Exp.store e₁ (ov w)) Q) Q :=
  fill_spec (.storeR e₁) e₂

@[spec mid] theorem storeL_spec (e₁ : Exp) (v : Val) :
    htriple (Exp.store e₁ (ov v)) (hwp e₁ fun w => hwp (Exp.store (ov w) (ov v)) Q) Q :=
  fill_spec (.storeL v) e₁

@[spec low] theorem allocNR_spec (e₁ e₂ : Exp) :
    htriple (Exp.allocN e₁ e₂) (hwp e₂ fun w => hwp (Exp.allocN e₁ (ov w)) Q) Q :=
  fill_spec (.allocNR e₁) e₂

@[spec mid] theorem allocNL_spec (e₁ : Exp) (v : Val) :
    htriple (Exp.allocN e₁ (ov v)) (hwp e₁ fun w => hwp (Exp.allocN (ov w) (ov v)) Q) Q :=
  fill_spec (.allocNL v) e₁

@[spec low] theorem free_ctx_spec (e : Exp) :
    htriple (Exp.free e) (hwp e fun w => hwp (Exp.free (ov w)) Q) Q :=
  fill_spec .free e

@[spec low] theorem pairR_spec (e₁ e₂ : Exp) :
    htriple (Exp.pair e₁ e₂) (hwp e₂ fun w => hwp (Exp.pair e₁ (ov w)) Q) Q :=
  fill_spec (.pairR e₁) e₂

@[spec mid] theorem pairL_spec (e₁ : Exp) (v : Val) :
    htriple (Exp.pair e₁ (ov v)) (hwp e₁ fun w => hwp (Exp.pair (ov w) (ov v)) Q) Q :=
  fill_spec (.pairL v) e₁

@[spec low] theorem fst_ctx_spec (e : Exp) :
    htriple (Exp.fst e) (hwp e fun w => hwp (Exp.fst (ov w)) Q) Q :=
  fill_spec .fst e

@[spec low] theorem snd_ctx_spec (e : Exp) :
    htriple (Exp.snd e) (hwp e fun w => hwp (Exp.snd (ov w)) Q) Q :=
  fill_spec .snd e

/-! ## Heap

The heap specifications hand the continuation `Q` the result value itself. The magic wand is
written `PreservesSup.upperAdjoint (BIBase.sep A)`, which `vcgen` introduces by framing `A`
onto the precondition (`upperAdjoint_sep_eq`). -/

/-- The magic wand `A -∗ B` as the upper adjoint of `A ∗ ·`. -/
local notation:25 A:26 " -∗ᵃ " B:25 => PreservesSup.upperAdjoint (BIBase.sep A) B

@[spec] theorem load_spec (l : Loc) (dq : DFrac) (v : Val) :
    htriple (Exp.load (ov (Val.lit (.loc l))))
      (iprop(l ↦{dq} some v ∗ (l ↦{dq} some v -∗ᵃ Q v))) Q := by
  apply triple_of_entails
  rw [upperAdjoint_sep_eq]
  iintro ⟨Hpt, HΦ⟩
  wp_load
  imodintro
  iapply HΦ $$ Hpt

@[spec] theorem store_spec (l : Loc) (v w : Val) :
    htriple (Exp.store (ov (Val.lit (.loc l))) (ov w))
      (iprop(l ↦ some v ∗ (l ↦ some w -∗ᵃ Q (.lit .unit)))) Q := by
  apply triple_of_entails
  rw [upperAdjoint_sep_eq]
  iintro ⟨Hpt, HΦ⟩
  wp_store
  imodintro
  iapply HΦ $$ Hpt

@[spec] theorem free_spec (l : Loc) (v : Val) :
    htriple (Exp.free (ov (Val.lit (.loc l))))
      (iprop(l ↦ some v ∗ Q (.lit .unit))) Q := by
  apply triple_of_entails
  iintro ⟨Hpt, HΦ⟩
  wp_free
  imodintro
  iexact HΦ

@[spec] theorem ref_spec (v : Val) :
    htriple (Exp.allocN (ov (Val.lit (.int 1))) (ov v))
      (⨅ l : Loc, l ↦ some v -∗ᵃ Q (.lit (.loc l))) Q := by
  apply triple_of_entails
  rw [iInf_eq]
  simp only [upperAdjoint_sep_eq]
  iintro H
  wp_alloc l with Hl
  imodintro
  ispecialize H $$ %l
  iapply H $$ Hl


/-! ## Substitution

`vcgen` rewrites the program `msubst σ e` by the equation for the head constructor of `e`. A
variable splits on the first entry of `σ`; the split on two distinct string literals leaves a single
branch. -/

section
variable {GF : BundledGFunctors} {s : Stuckness} {E : CoPset} (σ : List (String × Val))

set_option hygiene false in
local notation "mk " e:max => (⟪e @ s ; E⟫ : HLProg GF)

attribute [local semireducible] msubst

@[spec] theorem msubst_nil_eq (e : Exp) : mk (msubst [] e) = mk e := by rw [msubst_nil]
@[spec] theorem msubst_val_eq (w : Val) : mk (msubst σ (ov w)) = mk (ov w) := rfl
@[spec] theorem msubst_var_eq (x z : String) (v : Val) :
    mk (msubst ((x, v) :: σ) (.var z)) =
      if z = x then mk (ov v) else mk (msubst σ (.var z)) := by
  by_cases h : z = x <;> simp [msubst, lookup_cons, h]
@[spec] theorem msubst_rec_eq (f y : Binder) (e : Exp) :
    mk (msubst σ (.rec_ f y e)) = mk (.rec_ f y (msubst (dropB f y σ) e)) := rfl
@[spec] theorem msubst_app_eq (e₁ e₂ : Exp) :
    mk (msubst σ (.app e₁ e₂)) = mk (.app (msubst σ e₁) (msubst σ e₂)) := rfl
@[spec 1100] theorem msubst_app₂_eq (f e₁ e₂ : Exp) :
    mk (msubst σ (.app (.app f e₁) e₂)) = mk (.app (.app (msubst σ f) (msubst σ e₁)) (msubst σ e₂)) :=
  rfl
@[spec 1200] theorem msubst_app₂_val_eq (f : Val) (e₁ e₂ : Exp) :
    mk (msubst σ (.app (.app (ov f) e₁) e₂)) = mk (.app (.app (ov f) (msubst σ e₁)) (msubst σ e₂)) :=
  rfl
@[spec 1100] theorem msubst_app₃_eq (f e₁ e₂ e₃ : Exp) :
    mk (msubst σ (.app (.app (.app f e₁) e₂) e₃)) =
      mk (.app (.app (.app (msubst σ f) (msubst σ e₁)) (msubst σ e₂)) (msubst σ e₃)) := rfl
@[spec 1200] theorem msubst_app₃_val_eq (f : Val) (e₁ e₂ e₃ : Exp) :
    mk (msubst σ (.app (.app (.app (ov f) e₁) e₂) e₃)) =
      mk (.app (.app (.app (ov f) (msubst σ e₁)) (msubst σ e₂)) (msubst σ e₃)) := rfl
@[spec] theorem msubst_unop_eq (op : UnOp) (e : Exp) :
    mk (msubst σ (.unop op e)) = mk (.unop op (msubst σ e)) := rfl
@[spec] theorem msubst_binop_eq (op : BinOp) (e₁ e₂ : Exp) :
    mk (msubst σ (.binop op e₁ e₂)) = mk (.binop op (msubst σ e₁) (msubst σ e₂)) := rfl
@[spec] theorem msubst_if_eq (e₀ e₁ e₂ : Exp) :
    mk (msubst σ (.if e₀ e₁ e₂)) = mk (.if (msubst σ e₀) (msubst σ e₁) (msubst σ e₂)) := rfl
@[spec] theorem msubst_pair_eq (e₁ e₂ : Exp) :
    mk (msubst σ (.pair e₁ e₂)) = mk (.pair (msubst σ e₁) (msubst σ e₂)) := rfl
@[spec] theorem msubst_fst_eq (e : Exp) : mk (msubst σ (.fst e)) = mk (.fst (msubst σ e)) := rfl
@[spec] theorem msubst_snd_eq (e : Exp) : mk (msubst σ (.snd e)) = mk (.snd (msubst σ e)) := rfl
@[spec] theorem msubst_injL_eq (e : Exp) : mk (msubst σ (.injL e)) = mk (.injL (msubst σ e)) := rfl
@[spec] theorem msubst_injR_eq (e : Exp) : mk (msubst σ (.injR e)) = mk (.injR (msubst σ e)) := rfl
@[spec] theorem msubst_case_eq (e₀ e₁ e₂ : Exp) :
    mk (msubst σ (.case e₀ e₁ e₂)) = mk (.case (msubst σ e₀) (msubst σ e₁) (msubst σ e₂)) := rfl
@[spec] theorem msubst_allocN_eq (e₁ e₂ : Exp) :
    mk (msubst σ (.allocN e₁ e₂)) = mk (.allocN (msubst σ e₁) (msubst σ e₂)) := rfl
@[spec] theorem msubst_free_eq (e : Exp) : mk (msubst σ (.free e)) = mk (.free (msubst σ e)) := rfl
@[spec] theorem msubst_load_eq (e : Exp) : mk (msubst σ (.load e)) = mk (.load (msubst σ e)) := rfl
@[spec] theorem msubst_store_eq (e₁ e₂ : Exp) :
    mk (msubst σ (.store e₁ e₂)) = mk (.store (msubst σ e₁) (msubst σ e₂)) := rfl
@[spec] theorem msubst_cmpXchg_eq (e₀ e₁ e₂ : Exp) :
    mk (msubst σ (.cmpXchg e₀ e₁ e₂)) =
      mk (.cmpXchg (msubst σ e₀) (msubst σ e₁) (msubst σ e₂)) := rfl
@[spec] theorem msubst_xchg_eq (e₁ e₂ : Exp) :
    mk (msubst σ (.xchg e₁ e₂)) = mk (.xchg (msubst σ e₁) (msubst σ e₂)) := rfl
@[spec] theorem msubst_faa_eq (e₁ e₂ : Exp) :
    mk (msubst σ (.faa e₁ e₂)) = mk (.faa (msubst σ e₁) (msubst σ e₂)) := rfl
@[spec] theorem msubst_fork_eq (e : Exp) : mk (msubst σ (.fork e)) = mk (.fork (msubst σ e)) := rfl

end

end Iris.HeapLang.VCGen
