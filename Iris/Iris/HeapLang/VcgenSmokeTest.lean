module

import Iris.HeapLang.Omni
import Iris.HeapLang.Notation
import Std.Tactic.Do

/-!
# `@[spec]` lemmas driving `vcgen` over the HeapLang omni-WP

This wires the omni-WP `wp` step rules from `Omni.lean` into the (internal)
`Std.Internal.Do` verification-condition generator, following the
"approach 1" recipe: for every syntactic form,

* a **redex** spec, keyed on the fully-evaluated head (operands `.ofVal _`), and
* one **focus** spec per sub-expression position, expressing HeapLang's
  right-to-left evaluation order via `wp_bind_fill [ectxItem]`.

All specs are in the engine's `pre ⊑ wp prog post epost` shape.

**Priorities.** Redexes/values fire first (`high`); among the focus specs for a
constructor the one requiring the *most* already-evaluated positions gets the
higher priority (`L > M > R`), so `vcgen` never re-focuses a value and the tree
is walked deterministically. Termination: each focus spec strictly shrinks the
focused subterm; the value spec is the base case.
-/

open Iris.HeapLang Lean.Order Std.Internal.Do

namespace Iris.HeapLang.VcgenSmoke

/-! ## Values -/

@[spec high] theorem val_spec (v : Val) (post : Val → State → Prop) (epost : EPost.Nil) :
    post v ⊑ Std.Internal.Do.wp ((.ofVal v : Exp)) post epost := by
  intro σ h; exact wp_val.mpr h

/-- Recursive closures are values. -/
@[spec high] theorem rec_spec (f x : Binder) (e : Exp) (post : Val → State → Prop) (epost : EPost.Nil) :
    post (.rec_ f x e) ⊑ Std.Internal.Do.wp (Exp.rec_ f x e) post epost := by
  intro σ h; exact wp_rec h

/-! ## Unary operator -/

@[spec high] theorem unop_redex_spec {op : UnOp} {v v' : Val} (hop : op.eval v = some v')
    (post : Val → State → Prop) (epost : EPost.Nil) :
    post v' ⊑ Std.Internal.Do.wp (Exp.unop op (.ofVal v)) post epost := by
  intro σ h; exact wp_unop hop h

@[spec 1000] theorem unop_focus_spec {op : UnOp} {e : Exp}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e (fun v => Std.Internal.Do.wp (Exp.unop op (.ofVal v)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.unop op e) post epost := by
  intro σ h; exact wp_bind_fill [.unOp op] h

/-! ## Binary operator -/

@[spec high] theorem binop_redex_spec {op : BinOp} {v1 v2 v' : Val} (hop : op.eval v1 v2 = some v')
    (post : Val → State → Prop) (epost : EPost.Nil) :
    post v' ⊑ Std.Internal.Do.wp (Exp.binop op (.ofVal v1) (.ofVal v2)) post epost := by
  intro σ h; exact wp_binop hop h

@[spec 1200] theorem binop_focusL_spec {op : BinOp} {e1 : Exp} {v2 : Val}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e1 (fun v1 => Std.Internal.Do.wp (Exp.binop op (.ofVal v1) (.ofVal v2)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.binop op e1 (.ofVal v2)) post epost := by
  intro σ h; exact wp_bind_fill [.binOpL op v2] h

@[spec 1000] theorem binop_focusR_spec {op : BinOp} {e1 e2 : Exp}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e2 (fun v2 => Std.Internal.Do.wp (Exp.binop op e1 (.ofVal v2)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.binop op e1 e2) post epost := by
  intro σ h; exact wp_bind_fill [.binOpR op e1] h

/-! ## Application (β-reduction) -/

@[spec high] theorem beta_redex_spec {f x : Binder} {e1 : Exp} {v2 : Val}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp ((e1.subst f (.rec_ f x e1)).subst x v2) post epost
      ⊑ Std.Internal.Do.wp (Exp.app (.ofVal (.rec_ f x e1)) (.ofVal v2)) post epost := by
  intro σ h; exact wp_beta h

@[spec 1200] theorem app_focusL_spec {e1 : Exp} {v2 : Val}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e1 (fun v1 => Std.Internal.Do.wp (Exp.app (.ofVal v1) (.ofVal v2)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.app e1 (.ofVal v2)) post epost := by
  intro σ h; exact wp_bind_fill [.appL v2] h

@[spec 1000] theorem app_focusR_spec {e1 e2 : Exp}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e2 (fun v2 => Std.Internal.Do.wp (Exp.app e1 (.ofVal v2)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.app e1 e2) post epost := by
  intro σ h; exact wp_bind_fill [.appR e1] h

/-! ## Pairs -/

@[spec high] theorem pair_redex_spec {v1 v2 : Val}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    post (.pair v1 v2) ⊑ Std.Internal.Do.wp (Exp.pair (.ofVal v1) (.ofVal v2)) post epost := by
  intro σ h; exact wp_pair h

@[spec 1200] theorem pair_focusL_spec {e1 : Exp} {v2 : Val}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e1 (fun v1 => Std.Internal.Do.wp (Exp.pair (.ofVal v1) (.ofVal v2)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.pair e1 (.ofVal v2)) post epost := by
  intro σ h; exact wp_bind_fill [.pairL v2] h

@[spec 1000] theorem pair_focusR_spec {e1 e2 : Exp}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e2 (fun v2 => Std.Internal.Do.wp (Exp.pair e1 (.ofVal v2)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.pair e1 e2) post epost := by
  intro σ h; exact wp_bind_fill [.pairR e1] h

@[spec high] theorem fst_redex_spec {v1 v2 : Val}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    post v1 ⊑ Std.Internal.Do.wp (Exp.fst (.ofVal (.pair v1 v2))) post epost := by
  intro σ h; exact wp_fst h

@[spec 1000] theorem fst_focus_spec {e : Exp}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e (fun v => Std.Internal.Do.wp (Exp.fst (.ofVal v)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.fst e) post epost := by
  intro σ h; exact wp_bind_fill [.fst] h

@[spec high] theorem snd_redex_spec {v1 v2 : Val}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    post v2 ⊑ Std.Internal.Do.wp (Exp.snd (.ofVal (.pair v1 v2))) post epost := by
  intro σ h; exact wp_snd h

@[spec 1000] theorem snd_focus_spec {e : Exp}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e (fun v => Std.Internal.Do.wp (Exp.snd (.ofVal v)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.snd e) post epost := by
  intro σ h; exact wp_bind_fill [.snd] h

/-! ## Sum injections -/

@[spec high] theorem injL_redex_spec {v : Val}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    post (.injL v) ⊑ Std.Internal.Do.wp (Exp.injL (.ofVal v)) post epost := by
  intro σ h; exact wp_injL h

@[spec 1000] theorem injL_focus_spec {e : Exp}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e (fun v => Std.Internal.Do.wp (Exp.injL (.ofVal v)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.injL e) post epost := by
  intro σ h; exact wp_bind_fill [.injL] h

@[spec high] theorem injR_redex_spec {v : Val}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    post (.injR v) ⊑ Std.Internal.Do.wp (Exp.injR (.ofVal v)) post epost := by
  intro σ h; exact wp_injR h

@[spec 1000] theorem injR_focus_spec {e : Exp}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e (fun v => Std.Internal.Do.wp (Exp.injR (.ofVal v)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.injR e) post epost := by
  intro σ h; exact wp_bind_fill [.injR] h

/-! ## Conditional (only the scrutinee is evaluated) -/

@[spec high] theorem if_true_spec {e1 e2 : Exp}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e1 post epost
      ⊑ Std.Internal.Do.wp (Exp.if (.ofVal (.lit (.bool true))) e1 e2) post epost := by
  intro σ h; exact wp_if_true h

@[spec high] theorem if_false_spec {e1 e2 : Exp}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e2 post epost
      ⊑ Std.Internal.Do.wp (Exp.if (.ofVal (.lit (.bool false))) e1 e2) post epost := by
  intro σ h; exact wp_if_false h

@[spec 1000] theorem if_focus_spec {e e1 e2 : Exp}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e (fun v => Std.Internal.Do.wp (Exp.if (.ofVal v) e1 e2) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.if e e1 e2) post epost := by
  intro σ h; exact wp_bind_fill [.if e1 e2] h

/-! ## Case (only the scrutinee is evaluated) -/

@[spec high] theorem case_injL_spec {v : Val} {e1 e2 : Exp}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp (Exp.app e1 (.ofVal v)) post epost
      ⊑ Std.Internal.Do.wp (Exp.case (.ofVal (.injL v)) e1 e2) post epost := by
  intro σ h; exact wp_case_injL h

@[spec high] theorem case_injR_spec {v : Val} {e1 e2 : Exp}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp (Exp.app e2 (.ofVal v)) post epost
      ⊑ Std.Internal.Do.wp (Exp.case (.ofVal (.injR v)) e1 e2) post epost := by
  intro σ h; exact wp_case_injR h

@[spec 1000] theorem case_focus_spec {e e1 e2 : Exp}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e (fun v => Std.Internal.Do.wp (Exp.case (.ofVal v) e1 e2) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.case e e1 e2) post epost := by
  intro σ h; exact wp_bind_fill [.case e1 e2] h

/-! ## Heap: allocation

`ref v` (`allocN 1`) is premise-free; general `allocN n` carries `0 < n` and a
freshness witness as VCs. -/

@[spec high] theorem alloc_spec {v : Val} (post : Val → State → Prop) (epost : EPost.Nil) :
    (fun σ => ∀ l : Loc, σ.get? l = none → post (.lit (.loc l)) (σ.initHeap l 1 v))
      ⊑ Std.Internal.Do.wp (Exp.allocN (.ofVal (.lit (.int 1))) (.ofVal v)) post epost := by
  intro σ h; exact wp_alloc h

@[spec 1300] theorem allocN_spec {n : Int} {v : Val} (post : Val → State → Prop) (epost : EPost.Nil) :
    (fun σ => 0 < n ∧ (∃ l : Loc, ∀ i : Int, 0 ≤ i → i < n → σ.get? (l + i) = none) ∧
        ∀ l : Loc, (∀ i : Int, 0 ≤ i → i < n → σ.get? (l + i) = none) →
          post (.lit (.loc l)) (σ.initHeap l n v))
      ⊑ Std.Internal.Do.wp (Exp.allocN (.ofVal (.lit (.int n))) (.ofVal v)) post epost := by
  intro σ h; obtain ⟨hn, hfresh, hQ⟩ := h; exact wp_allocN hn hfresh hQ

@[spec 1200] theorem allocN_focusL_spec {e1 : Exp} {v2 : Val}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e1 (fun v1 => Std.Internal.Do.wp (Exp.allocN (.ofVal v1) (.ofVal v2)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.allocN e1 (.ofVal v2)) post epost := by
  intro σ h; exact wp_bind_fill [.allocNL v2] h

@[spec 1000] theorem allocN_focusR_spec {e1 e2 : Exp}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e2 (fun v2 => Std.Internal.Do.wp (Exp.allocN e1 (.ofVal v2)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.allocN e1 e2) post epost := by
  intro σ h; exact wp_bind_fill [.allocNR e1] h

/-! ## Heap: load / free (unary) -/

@[spec high] theorem load_spec {l : Loc} (post : Val → State → Prop) (epost : EPost.Nil) :
    (fun σ => ∃ v : Val, σ.get? l = some (some v) ∧ post v σ)
      ⊑ Std.Internal.Do.wp (Exp.load (.ofVal (.lit (.loc l)))) post epost := by
  intro σ h; obtain ⟨v, hl, hq⟩ := h; exact wp_load hl hq

@[spec 1000] theorem load_focus_spec {e : Exp} (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e (fun v => Std.Internal.Do.wp (Exp.load (.ofVal v)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.load e) post epost := by
  intro σ h; exact wp_bind_fill [.load] h

@[spec high] theorem free_spec {l : Loc} (post : Val → State → Prop) (epost : EPost.Nil) :
    (fun σ => ∃ v : Val, σ.get? l = some (some v) ∧ post (.lit .unit) (σ.initHeap l 1 none))
      ⊑ Std.Internal.Do.wp (Exp.free (.ofVal (.lit (.loc l)))) post epost := by
  intro σ h; obtain ⟨v, hl, hq⟩ := h; exact wp_free hl hq

@[spec 1000] theorem free_focus_spec {e : Exp} (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e (fun v => Std.Internal.Do.wp (Exp.free (.ofVal v)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.free e) post epost := by
  intro σ h; exact wp_bind_fill [.free] h

/-! ## Heap: store / xchg / faa (binary) -/

@[spec high] theorem store_spec {l : Loc} {w : Val} (post : Val → State → Prop) (epost : EPost.Nil) :
    (fun σ => ∃ v : Val, σ.get? l = some (some v) ∧ post (.lit .unit) (σ.initHeap l 1 (some w)))
      ⊑ Std.Internal.Do.wp (Exp.store (.ofVal (.lit (.loc l))) (.ofVal w)) post epost := by
  intro σ h; obtain ⟨v, hl, hq⟩ := h; exact wp_store hl hq

@[spec 1200] theorem store_focusL_spec {e1 : Exp} {v2 : Val}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e1 (fun v1 => Std.Internal.Do.wp (Exp.store (.ofVal v1) (.ofVal v2)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.store e1 (.ofVal v2)) post epost := by
  intro σ h; exact wp_bind_fill [.storeL v2] h

@[spec 1000] theorem store_focusR_spec {e1 e2 : Exp}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e2 (fun v2 => Std.Internal.Do.wp (Exp.store e1 (.ofVal v2)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.store e1 e2) post epost := by
  intro σ h; exact wp_bind_fill [.storeR e1] h

@[spec high] theorem xchg_spec {l : Loc} {v2 : Val} (post : Val → State → Prop) (epost : EPost.Nil) :
    (fun σ => ∃ v1 : Val, σ.get? l = some (some v1) ∧ post v1 (σ.initHeap l 1 (some v2)))
      ⊑ Std.Internal.Do.wp (Exp.xchg (.ofVal (.lit (.loc l))) (.ofVal v2)) post epost := by
  intro σ h; obtain ⟨v1, hl, hq⟩ := h; exact wp_xchg hl hq

@[spec 1200] theorem xchg_focusL_spec {e1 : Exp} {v2 : Val}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e1 (fun v1 => Std.Internal.Do.wp (Exp.xchg (.ofVal v1) (.ofVal v2)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.xchg e1 (.ofVal v2)) post epost := by
  intro σ h; exact wp_bind_fill [.xchgL v2] h

@[spec 1000] theorem xchg_focusR_spec {e1 e2 : Exp}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e2 (fun v2 => Std.Internal.Do.wp (Exp.xchg e1 (.ofVal v2)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.xchg e1 e2) post epost := by
  intro σ h; exact wp_bind_fill [.xchgR e1] h

@[spec high] theorem faa_spec {l : Loc} {i2 : Int} (post : Val → State → Prop) (epost : EPost.Nil) :
    (fun σ => ∃ i1 : Int, σ.get? l = some (some (.lit (.int i1))) ∧
        post (.lit (.int i1)) (σ.initHeap l 1 (some (.lit (.int (i1 + i2))))))
      ⊑ Std.Internal.Do.wp (Exp.faa (.ofVal (.lit (.loc l))) (.ofVal (.lit (.int i2)))) post epost := by
  intro σ h; obtain ⟨i1, hl, hq⟩ := h; exact wp_faa hl hq

@[spec 1200] theorem faa_focusL_spec {e1 : Exp} {v2 : Val}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e1 (fun v1 => Std.Internal.Do.wp (Exp.faa (.ofVal v1) (.ofVal v2)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.faa e1 (.ofVal v2)) post epost := by
  intro σ h; exact wp_bind_fill [.faaL v2] h

@[spec 1000] theorem faa_focusR_spec {e1 e2 : Exp}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e2 (fun v2 => Std.Internal.Do.wp (Exp.faa e1 (.ofVal v2)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.faa e1 e2) post epost := by
  intro σ h; exact wp_bind_fill [.faaR e1] h

/-! ## Heap: compare-and-exchange (ternary) -/

@[spec high] theorem cmpXchg_spec {l : Loc} {v1 v2 : Val} (post : Val → State → Prop) (epost : EPost.Nil) :
    (fun σ => ∃ vl : Val, σ.get? l = some (some vl) ∧ vl.compareSafe v1 ∧
        ∀ b : Bool, decide (vl = v1) = b →
          post (.pair vl (.lit (.bool b))) (if b then σ.initHeap l 1 (some v2) else σ))
      ⊑ Std.Internal.Do.wp (Exp.cmpXchg (.ofVal (.lit (.loc l))) (.ofVal v1) (.ofVal v2)) post epost := by
  intro σ h; obtain ⟨vl, hl, hcmp, hQ⟩ := h; exact wp_cmpXchg hl hcmp hQ

@[spec 1200] theorem cmpXchg_focusL_spec {e0 : Exp} {v1 v2 : Val}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e0 (fun v0 => Std.Internal.Do.wp (Exp.cmpXchg (.ofVal v0) (.ofVal v1) (.ofVal v2)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.cmpXchg e0 (.ofVal v1) (.ofVal v2)) post epost := by
  intro σ h; exact wp_bind_fill [.cmpXchgL v1 v2] h

@[spec 1100] theorem cmpXchg_focusM_spec {e0 e1 : Exp} {v2 : Val}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e1 (fun v1 => Std.Internal.Do.wp (Exp.cmpXchg e0 (.ofVal v1) (.ofVal v2)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.cmpXchg e0 e1 (.ofVal v2)) post epost := by
  intro σ h; exact wp_bind_fill [.cmpXchgM e0 v2] h

@[spec 1000] theorem cmpXchg_focusR_spec {e0 e1 e2 : Exp}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e2 (fun v2 => Std.Internal.Do.wp (Exp.cmpXchg e0 e1 (.ofVal v2)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.cmpXchg e0 e1 e2) post epost := by
  intro σ h; exact wp_bind_fill [.cmpXchgR e0 e1] h

/-! ## Demos -/

private def lit (n : Int) : Exp := .ofVal (.lit (.int n))
private def add (a b : Exp) : Exp := Exp.binop .plus a b

/-- Pure arithmetic, nested redexes: `(1 + 2) + (3 + 4) = 10`. -/
example : (fun _ => True) ⊑
    Std.Internal.Do.wp (add (add (lit 1) (lit 2)) (add (lit 3) (lit 4)))
      (fun r _ => r = .lit (.int 10)) EPost.Nil.mk := by
  unfold add lit
  vcgen
  -- Leftover VCs are the per-node `BinOp.eval` obligations. Each `rfl` also pins
  -- the intermediate-value metavariable, so a couple of passes (inner nodes
  -- before the outer one) discharge the whole chain regardless of goal order.
  all_goals (try rfl)
  all_goals (try rfl)

/-- Mixing constructs: `fst ((1 + 2), (3 + 4)) = 3`, with a conditional wrapper. -/
example : (fun _ => True) ⊑
    Std.Internal.Do.wp
      (Exp.if (.ofVal (.lit (.bool true)))
        (Exp.fst (Exp.pair (add (lit 1) (lit 2)) (add (lit 3) (lit 4))))
        (lit 0))
      (fun r _ => r = .lit (.int 3)) EPost.Nil.mk := by
  unfold add lit
  vcgen
  all_goals (try rfl)
  all_goals (try rfl)

/-! ### Larger programs in HeapLang surface syntax

Written with the `hl(…)` notation; `vcgen` symbolically executes the whole
expression, leaving only the primitive `BinOp.eval` obligations as VCs. -/

/-- Deeper arithmetic, mixed operators: `(10 - 3) * (2 + 2)` ⟶ `28`. -/
private def arith : Exp := hl((#10 - #3) * (#2 + #2))
example : (fun _ => True) ⊑
    Std.Internal.Do.wp arith (fun r _ => r = .lit (.int 28)) EPost.Nil.mk := by
  unfold arith
  vcgen
  all_goals (try rfl)
  all_goals (try rfl)

/-- Build a nested tuple, then project into it (pairs/`fst`/`snd` bind nothing, so
`vcgen` handles them fully): `fst (snd (1, (2 * 3, 4 + 5)))` ⟶ `6`. -/
private def project : Exp := hl(fst(snd((#1, (#2 * #3, #4 + #5)))))
example : (fun _ => True) ⊑
    Std.Internal.Do.wp project (fun r _ => r = .lit (.int 6)) EPost.Nil.mk := by
  unfold project
  vcgen
  all_goals (try rfl)
  all_goals (try rfl)

/-! ### The frontier

`vcgen` here drives *substitution-free* evaluation: arithmetic, pairs/projections,
injections, and control flow whose scrutinee is a **literal** (as in the `if true …`
demo above — the dead branch is discarded untouched). Three things are out of reach
with just these specs, all for the same underlying reason — a spec has to match the
program **syntactically**:

* **Binding — `let`, `λ`-application, recursion.** β-reduction (`beta_redex_spec`)
  produces a metalevel `Exp.subst …` term; `vcgen` has no spec for a raw `subst`
  call, and feeding `Exp.subst` to its simp set makes the substitution's binder
  handling panic. Needs a normalizing substitution operation `vcgen` can compute.
* **Control flow on a *computed* condition** (`if x < y then …`). The guard reduces
  to `.lit (.bool (x < y))`, whose boolean does not syntactically match `if_true`'s
  `true` / `if_false`'s `false`; `if_focus` then re-fires on the value scrutinee and
  loops. Needs the comparison to normalize to a literal `true`/`false`.
* **Mutable state end-to-end.** `ref`/`load`/`store` each step, but the heap
  side-conditions (`σ.get? l = some …`) are left as VCs — there is no separation-logic
  frame in this plain `State → Prop` lattice to discharge them automatically. -/

end Iris.HeapLang.VcgenSmoke
