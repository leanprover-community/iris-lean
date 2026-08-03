module

public import IrisDoNightly.Legacy.Delta
public import IrisDoNightly.Legacy.Loop
public import IrisDoNightly.Legacy.SLFrame
public import IrisDoNightly.Notation
import Std.Tactic.Do
import Std.Internal.Do

set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open Lean.Order Std.Internal.Do Iris.HeapLang Iris.HeapLang.SL Iris.HeapLang.SL.HeapLangAxioms

namespace Iris.HeapLang.Codec

section
variable {wp} [HeapLangAxioms wp]

/-- Assume a pure fact carried on the left of a `hand`. -/
theorem hand_hpure_mono {φ : Prop} {P Q : HProp} (h : φ → P ⊑ Q) :
    hand (hpure φ) P ⊑ Q := fun _ ⟨hφ, hP⟩ => h hφ _ hP

/-- Eliminate an existential on the left of `⊑`. -/
theorem hexists_le {α : Sort _} {P : α → HProp} {Q : HProp} (h : ∀ a, P a ⊑ Q) :
    hexists P ⊑ Q := fun _ ⟨a, hP⟩ => h a _ hP

/-- Application of a `let`/`λ` (anonymous recursion binder): the continuation is a *single*
`body.subst x v₂`, with no residual `.subst anon` for `vcgen`'s head-reducer to choke on.  This is
the `@[spec]` that lets `vcgen` step through named `let`-bindings (loads) in one pass. -/
@[spec] theorem spec_app_lam_anon {x : Binder} {body e₂ : Exp} {Φ : Val → HProp} :
    wp⟦e₂⟧ (fun v₂ => wp⟦body.subst x v₂⟧ Φ) ⊑ wp⟦Exp.app (Exp.rec_ Binder.anon x body) e₂⟧ Φ := by
  refine PartialOrder.rel_trans ?_ spec_app_lam
  refine wp_mono (fun v₂ => ?_)
  exact PartialOrder.rel_of_eq (by simp only [Exp.subst])


/-- Eliminate a framed existential on the left of `⊑`. -/
theorem sepConj_hexists_le {α : Sort _} (F : HProp) (P : α → HProp) (Q : HProp)
    (h : ∀ a, (F ∗ P a) ⊑ Q) : (F ∗ hexists P) ⊑ Q :=
  fun _ ⟨σ1, σ2, hd, hσ, hF, a, hPa⟩ => h a _ ⟨σ1, σ2, hd, hσ, hF, hPa⟩

/-- Assume a framed pure fact on the left of `⊑`. -/
theorem sepConj_hand_pure_le {φ : Prop} (F P : HProp) (Q : HProp)
    (h : φ → (F ∗ P) ⊑ Q) : (F ∗ hand (hpure φ) P) ⊑ Q :=
  fun _ ⟨σ1, σ2, hd, hσ, hF, hφ, hP⟩ => h hφ _ ⟨σ1, σ2, hd, hσ, hF, hP⟩

/-! ## Sequenced, auto-framed heap-op rules

The primitive `spec_*` rules fire on a bare heap op with the *whole* state being the op's footprint.
Real straight-line code threads a frame `F` (the rest of the heap) through a sequence of ops.  These
combinators bake the frame in and consume one `let`/`;` step, so a loop body is discharged as a
linear chain of `refine`s with no manual `wp_frame`/`wp_bind` juggling. -/

/-- `let c := !l; body` where the footprint carries `l ↦ w` (framing `F`). -/
theorem wp_let_load (F : HProp) (l : Loc) (w : Val) (c : Binder) (body : Exp) (Φ : Val → HProp)
    (hcont : (F ∗ (l ↦ w)) ⊑ wp⟦body.subst c w⟧ Φ) :
    (F ∗ (l ↦ w)) ⊑
      wp⟦Exp.app (Exp.rec_ Binder.anon c body) (Exp.load (Exp.ofVal (Val.lit (.loc l))))⟧ Φ := by
  refine PartialOrder.rel_trans ?_ spec_app_lam
  refine PartialOrder.rel_trans (sepConj_mono_r (spec_load (wp:=wp) l w)) ?_
  refine PartialOrder.rel_trans (wp_frame F) ?_
  refine wp_mono ?_
  intro v
  simp only [Exp.subst, Exp.substStr]
  rintro σ ⟨σ₁, σ₂, hd, rfl, hF, rfl, hc⟩
  exact hcont _ ⟨σ₁, σ₂, hd, rfl, hF, hc⟩

/-- `let c := !(l +ₗ i); body` where the footprint carries `(l+i) ↦ w`. -/
theorem wp_let_load_offset (F : HProp) (l : Loc) (i : Int) (w : Val) (c : Binder) (body : Exp)
    (Φ : Val → HProp) (hcont : (F ∗ ((l + i) ↦ w)) ⊑ wp⟦body.subst c w⟧ Φ) :
    (F ∗ ((l + i) ↦ w)) ⊑
      wp⟦Exp.app (Exp.rec_ Binder.anon c body)
        (Exp.load (Exp.binop BinOp.offset (Exp.ofVal (Val.lit (.loc l)))
          (Exp.ofVal (Val.lit (.int i)))))⟧ Φ := by
  refine PartialOrder.rel_trans ?_ spec_app_lam
  refine PartialOrder.rel_trans (sepConj_mono_r (spec_load_offset (wp:=wp) l i w)) ?_
  refine PartialOrder.rel_trans (wp_frame F) ?_
  refine wp_mono ?_
  intro v
  simp only [Exp.subst, Exp.substStr]
  rintro σ ⟨σ₁, σ₂, hd, rfl, hF, rfl, hc⟩
  exact hcont _ ⟨σ₁, σ₂, hd, rfl, hF, hc⟩

/-- `l ← w; body` where the footprint carries `l ↦ v₀` (updated to `l ↦ w` for `body`). -/
theorem wp_seq_store (F : HProp) (l : Loc) (v₀ w : Val) (body : Exp) (Φ : Val → HProp)
    (hcont : (F ∗ (l ↦ w)) ⊑ wp⟦body⟧ Φ) :
    (F ∗ (l ↦ v₀)) ⊑
      wp⟦Exp.app (Exp.rec_ Binder.anon Binder.anon body)
        (Exp.store (Exp.ofVal (Val.lit (.loc l))) (Exp.ofVal w))⟧ Φ := by
  refine PartialOrder.rel_trans ?_ spec_app_lam
  refine PartialOrder.rel_trans (sepConj_mono_r (spec_store (wp:=wp) l v₀ w)) ?_
  refine PartialOrder.rel_trans (wp_frame F) ?_
  refine wp_mono ?_
  intro v
  simp only [Exp.subst, Exp.substStr]
  exact hcont

/-- `(l +ₗ i) ← w; body` where the footprint carries `(l+i) ↦ v₀`. -/
theorem wp_seq_store_offset (F : HProp) (l : Loc) (i : Int) (v₀ w : Val) (body : Exp)
    (Φ : Val → HProp) (hcont : (F ∗ ((l + i) ↦ w)) ⊑ wp⟦body⟧ Φ) :
    (F ∗ ((l + i) ↦ v₀)) ⊑
      wp⟦Exp.app (Exp.rec_ Binder.anon Binder.anon body)
        (Exp.store (Exp.binop BinOp.offset (Exp.ofVal (Val.lit (.loc l)))
          (Exp.ofVal (Val.lit (.int i)))) (Exp.ofVal w))⟧ Φ := by
  refine PartialOrder.rel_trans ?_ spec_app_lam
  refine PartialOrder.rel_trans (sepConj_mono_r (spec_store_offset (wp:=wp) l i v₀ w)) ?_
  refine PartialOrder.rel_trans (wp_frame F) ?_
  refine wp_mono ?_
  intro v
  simp only [Exp.subst, Exp.substStr]
  exact hcont

/-- `∗` is associative and commutative, so `ac_rfl` can discharge any frame rearrangement. -/
instance : Std.Associative (α := HProp) sepConj := ⟨sepConj_assoc⟩
instance : Std.Commutative (α := HProp) sepConj := ⟨sepConj_comm⟩

/-! ### Prelude-wiring rules (pure projections + allocation), for `bytes → bytes` functions -/

/-- `let x := snd (a, b); body`. -/
theorem wp_let_snd (P : HProp) (a b : Val) (x : Binder) (body : Exp) (Φ : Val → HProp)
    (hcont : P ⊑ wp⟦body.subst x b⟧ Φ) :
    P ⊑ wp⟦Exp.app (Exp.rec_ Binder.anon x body)
      (Exp.snd (Exp.ofVal (Val.pair a b)))⟧ Φ := by
  refine PartialOrder.rel_trans ?_ spec_app_lam
  refine PartialOrder.rel_trans ?_ spec_snd
  refine PartialOrder.rel_trans ?_ spec_val
  exact le_hexists _ a (le_hexists _ b (le_hand_pure rfl hcont))

/-- `let x := fst (a, b); body`. -/
theorem wp_let_fst (P : HProp) (a b : Val) (x : Binder) (body : Exp) (Φ : Val → HProp)
    (hcont : P ⊑ wp⟦body.subst x a⟧ Φ) :
    P ⊑ wp⟦Exp.app (Exp.rec_ Binder.anon x body)
      (Exp.fst (Exp.ofVal (Val.pair a b)))⟧ Φ := by
  refine PartialOrder.rel_trans ?_ spec_app_lam
  refine PartialOrder.rel_trans ?_ spec_fst
  refine PartialOrder.rel_trans ?_ spec_val
  exact le_hexists _ a (le_hexists _ b (le_hand_pure rfl hcont))

/-- `let x := allocn(n, w); body` — binds a fresh array of `n` copies of `w`, framing `P`. -/
theorem wp_let_allocN (P : HProp) (n : Nat) (w : Val) (hn : 0 < n) (x : Binder) (body : Exp)
    (Φ : Val → HProp)
    (hcont : ∀ l : Loc, (P ∗ (l ↦∗ (List.replicate n w))) ⊑
      wp⟦body.subst x (Val.lit (.loc l))⟧ Φ) :
    P ⊑ wp⟦Exp.app (Exp.rec_ Binder.anon x body)
      (Exp.allocN (Exp.ofVal (Val.lit (.int n))) (Exp.ofVal w))⟧ Φ := by
  refine PartialOrder.rel_trans ?_ spec_app_lam
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (sepConj_emp P).symm) ?_
  refine PartialOrder.rel_trans (sepConj_mono_r (spec_allocN (wp := wp) n w hn)) ?_
  refine PartialOrder.rel_trans (wp_frame P) ?_
  refine wp_mono ?_
  intro v
  rintro σ ⟨σ1, σ2, hd, rfl, hP, l, rfl, hl⟩
  exact hcont l _ ⟨σ1, σ2, hd, rfl, hP, hl⟩

/-- `let x := ref(w); body` — binds a fresh cell holding `w`, framing `P`. -/
theorem wp_let_ref (P : HProp) (w : Val) (x : Binder) (body : Exp) (Φ : Val → HProp)
    (hcont : ∀ l : Loc, (P ∗ (l ↦ w)) ⊑ wp⟦body.subst x (Val.lit (.loc l))⟧ Φ) :
    P ⊑ wp⟦Exp.app (Exp.rec_ Binder.anon x body)
      (Exp.allocN (Exp.ofVal (Val.lit (.int 1))) (Exp.ofVal w))⟧ Φ := by
  refine PartialOrder.rel_trans ?_ spec_app_lam
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (sepConj_emp P).symm) ?_
  refine PartialOrder.rel_trans (sepConj_mono_r (spec_alloc (wp := wp) w)) ?_
  refine PartialOrder.rel_trans (wp_frame P) ?_
  refine wp_mono ?_
  intro v
  rintro σ ⟨σ1, σ2, hd, rfl, hP, l, rfl, hl⟩
  exact hcont l _ ⟨σ1, σ2, hd, rfl, hP, hl⟩

/-- 4-atom `∗` rearrangement used to isolate cell `i` of an array while framing the rest. -/
private theorem sepConj_ac4 (x y z w : HProp) : ((x ∗ (y ∗ z)) ∗ w) = ((x ∗ (z ∗ w)) ∗ y) := by
  rw [sepConj_assoc x (y ∗ z) w, sepConj_assoc y z w, sepConj_assoc x (z ∗ w) y,
    sepConj_comm (z ∗ w) y]

/-- Array-level load: `let c := !(a +ₗ i); body` reading cell `i` of a *whole* array `a ↦∗ NS`.
The array stays intact in the continuation, so callers never split/recombine. -/
theorem wp_let_load_arr (F : HProp) (a : Loc) (NS : List Val) (i : Nat) (hi : i < NS.length)
    (c : Binder) (body : Exp) (Φ : Val → HProp)
    (hcont : ((a ↦∗ NS) ∗ F) ⊑ wp⟦body.subst c (NS[i]'hi)⟧ Φ) :
    ((a ↦∗ NS) ∗ F) ⊑
      wp⟦Exp.app (Exp.rec_ Binder.anon c body)
        (Exp.load (Exp.binop BinOp.offset (Exp.ofVal (Val.lit (.loc a)))
          (Exp.ofVal (Val.lit (.int (i : Int))))))⟧ Φ := by
  have hsplit : (a ↦∗ NS) = ((a ↦∗ (NS.take i)) ∗
      (((a + (i : Int)) ↦ (NS[i]'hi)) ∗ ((a + (i : Int) + (1 : Int)) ↦∗ (NS.drop (i + 1))))) := by
    rw [arrayPointsTo_split a NS i (Nat.le_of_lt hi), List.drop_eq_getElem_cons hi, arrayPointsTo_cons]
  have heq : ((a ↦∗ NS) ∗ F) =
      (((a ↦∗ (NS.take i)) ∗ (((a + (i : Int) + (1 : Int)) ↦∗ (NS.drop (i + 1))) ∗ F)) ∗
        ((a + (i : Int)) ↦ (NS[i]'hi))) := by
    rw [hsplit]; exact sepConj_ac4 _ _ _ _
  rw [heq] at hcont ⊢
  exact wp_let_load_offset _ a (i : Int) (NS[i]'hi) c body Φ hcont

/-- Array-level store **spec** (a Hoare triple, not a continuation): storing `w` at index `i` of a
whole array `a ↦∗ OS` yields `a ↦∗ OS.set i w`.  Registered `@[spec]` so `vcgen` uses the *whole
array* as the store's footprint — for a single-array loop nothing needs framing, so no wand arises. -/
@[spec] theorem spec_store_arr (a : Loc) (OS : List Val) (i : Nat) (hi : i < OS.length) (v : Val) :
    (a ↦∗ OS) ⊑
      wp⟦Exp.store (Exp.binop BinOp.offset (Exp.ofVal (Val.lit (.loc a)))
        (Exp.ofVal (Val.lit (.int (i : Int))))) (Exp.ofVal v)⟧
        (fun _ => a ↦∗ (OS.set i v)) := by
  have hsplit : (a ↦∗ OS) = ((a ↦∗ (OS.take i)) ∗
      (((a + (i : Int)) ↦ (OS[i]'hi)) ∗ ((a + (i : Int) + (1 : Int)) ↦∗ (OS.drop (i + 1))))) := by
    rw [arrayPointsTo_split a OS i (Nat.le_of_lt hi), List.drop_eq_getElem_cons hi, arrayPointsTo_cons]
  have hsplit2 : (a ↦∗ (OS.set i v)) = ((a ↦∗ (OS.take i)) ∗
      (((a + (i : Int)) ↦ v) ∗ ((a + (i : Int) + (1 : Int)) ↦∗ (OS.drop (i + 1))))) := by
    rw [show OS.set i v = OS.take i ++ v :: OS.drop (i + 1) by
      simp [List.set_eq_take_append_cons_drop, hi]]
    rw [arrayPointsTo_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi), arrayPointsTo_cons]
  rw [hsplit]
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (by ac_rfl :
    _ = (((a ↦∗ (OS.take i)) ∗ ((a + (i : Int) + (1 : Int)) ↦∗ (OS.drop (i + 1)))) ∗
      ((a + (i : Int)) ↦ (OS[i]'hi))))) ?_
  refine PartialOrder.rel_trans
    (sepConj_mono_r (spec_store_offset (wp := wp) a (i : Int) (OS[i]'hi) v)) ?_
  refine PartialOrder.rel_trans (wp_frame _) ?_
  refine wp_mono ?_
  intro _
  rw [hsplit2]
  exact PartialOrder.rel_of_eq (by ac_rfl)

/-- Monotonicity of `hand (hpure φ) ·`, and pure-fact commutation out of `∗`. -/
theorem hand_mono_r {φ : Prop} {P Q : HProp} (h : P ⊑ Q) :
    hand (hpure φ) P ⊑ hand (hpure φ) Q := fun _ ⟨hφ, hP⟩ => ⟨hφ, h _ hP⟩

theorem sepConj_hand_hpure_le (F : HProp) (φ : Prop) (X : HProp) :
    (F ∗ hand (hpure φ) X) ⊑ hand (hpure φ) (F ∗ X) :=
  fun _ ⟨σ1, σ2, hd, hσ, hF, hφ, hX⟩ => ⟨hφ, σ1, σ2, hd, hσ, hF, hX⟩

/-- Array-level load **spec**: reading index `i` of a whole array `a ↦∗ OS` returns `OS[i]` and keeps
the array.  `@[spec]` so `vcgen` uses the whole array as the load's footprint. -/
@[spec] theorem spec_load_arr (a : Loc) (OS : List Val) (i : Nat) (hi : i < OS.length) :
    (a ↦∗ OS) ⊑
      wp⟦Exp.load (Exp.binop BinOp.offset (Exp.ofVal (Val.lit (.loc a)))
        (Exp.ofVal (Val.lit (.int (i : Int)))))⟧
        (fun v => hand (hpure (v = OS[i]'hi)) (a ↦∗ OS)) := by
  have hsplit : (a ↦∗ OS) = ((a ↦∗ (OS.take i)) ∗
      (((a + (i : Int)) ↦ (OS[i]'hi)) ∗ ((a + (i : Int) + (1 : Int)) ↦∗ (OS.drop (i + 1))))) := by
    rw [arrayPointsTo_split a OS i (Nat.le_of_lt hi), List.drop_eq_getElem_cons hi, arrayPointsTo_cons]
  rw [hsplit]
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (by ac_rfl :
    _ = (((a ↦∗ (OS.take i)) ∗ ((a + (i : Int) + (1 : Int)) ↦∗ (OS.drop (i + 1)))) ∗
      ((a + (i : Int)) ↦ (OS[i]'hi))))) ?_
  refine PartialOrder.rel_trans (sepConj_mono_r (spec_load_offset (wp := wp) a (i : Int) (OS[i]'hi))) ?_
  refine PartialOrder.rel_trans (wp_frame _) ?_
  refine wp_mono ?_
  intro v
  refine PartialOrder.rel_trans (sepConj_hand_hpure_le _ _ _) (hand_mono_r ?_)
  exact PartialOrder.rel_of_eq (by ac_rfl)

/-- Array-level store: `(a +ₗ i) ← w; body` updating cell `i` of a *whole* array `a ↦∗ OS`; the
continuation owns `a ↦∗ OS.set i w`. -/
theorem wp_seq_store_arr (F : HProp) (a : Loc) (OS : List Val) (i : Nat) (hi : i < OS.length)
    (w : Val) (body : Exp) (Φ : Val → HProp)
    (hcont : ((a ↦∗ (OS.set i w)) ∗ F) ⊑ wp⟦body⟧ Φ) :
    ((a ↦∗ OS) ∗ F) ⊑
      wp⟦Exp.app (Exp.rec_ Binder.anon Binder.anon body)
        (Exp.store (Exp.binop BinOp.offset (Exp.ofVal (Val.lit (.loc a)))
          (Exp.ofVal (Val.lit (.int (i : Int))))) (Exp.ofVal w))⟧ Φ := by
  have hsplit : (a ↦∗ OS) = ((a ↦∗ (OS.take i)) ∗
      (((a + (i : Int)) ↦ (OS[i]'hi)) ∗ ((a + (i : Int) + (1 : Int)) ↦∗ (OS.drop (i + 1))))) := by
    rw [arrayPointsTo_split a OS i (Nat.le_of_lt hi), List.drop_eq_getElem_cons hi, arrayPointsTo_cons]
  have hsplit2 : (a ↦∗ (OS.set i w)) = ((a ↦∗ (OS.take i)) ∗
      (((a + (i : Int)) ↦ w) ∗ ((a + (i : Int) + (1 : Int)) ↦∗ (OS.drop (i + 1))))) := by
    rw [show OS.set i w = OS.take i ++ w :: OS.drop (i + 1) by
      simp [List.set_eq_take_append_cons_drop, hi]]
    rw [arrayPointsTo_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi), arrayPointsTo_cons]
  have heq1 : ((a ↦∗ OS) ∗ F) =
      (((a ↦∗ (OS.take i)) ∗ (((a + (i : Int) + (1 : Int)) ↦∗ (OS.drop (i + 1))) ∗ F)) ∗
        ((a + (i : Int)) ↦ (OS[i]'hi))) := by
    rw [hsplit]; exact sepConj_ac4 _ _ _ _
  have heq2 : ((a ↦∗ (OS.set i w)) ∗ F) =
      (((a ↦∗ (OS.take i)) ∗ (((a + (i : Int) + (1 : Int)) ↦∗ (OS.drop (i + 1))) ∗ F)) ∗
        ((a + (i : Int)) ↦ w)) := by
    rw [hsplit2]; exact sepConj_ac4 _ _ _ _
  rw [heq1]
  rw [heq2] at hcont
  exact wp_seq_store_offset _ a (i : Int) (OS[i]'hi) w body Φ hcont

/-- The `delta` store value `((a - b) + 256) % 256` (mod via `tmod`) evaluates purely to a byte. -/
theorem wp_delta_arith (a b : Int) (Φ : Val → HProp) :
    Φ (byteVal (Int.tmod ((a - b) + 256) 256)) ⊑
      wp⟦Exp.binop BinOp.tmod
          (Exp.binop BinOp.plus
            (Exp.binop BinOp.minus (Exp.ofVal (byteVal a)) (Exp.ofVal (byteVal b)))
            (Exp.ofVal (byteVal 256)))
          (Exp.ofVal (byteVal 256))⟧ Φ := by
  refine PartialOrder.rel_trans ?_ spec_binop
  refine PartialOrder.rel_trans ?_ spec_val
  refine PartialOrder.rel_trans ?_ spec_binop
  refine PartialOrder.rel_trans ?_ spec_val
  refine PartialOrder.rel_trans ?_ spec_binop
  refine PartialOrder.rel_trans ?_ spec_val
  refine PartialOrder.rel_trans ?_ spec_val
  refine le_hexists _ (byteVal (a - b)) (le_hand_pure (by simp [BinOp.eval, byteVal]) ?_)
  refine le_hexists _ (byteVal ((a - b) + 256)) (le_hand_pure (by simp [BinOp.eval, byteVal]) ?_)
  refine le_hexists _ (byteVal (Int.tmod ((a - b) + 256) 256))
    (le_hand_pure (by simp [BinOp.eval, byteVal]) ?_)
  exact PartialOrder.rel_refl

/-- Minimal heap-loop: zero every cell of an array.  Validates the wp_rec + array-focus +
sliding-window pattern that every codec loop needs. -/
def zeroArray (l : Loc) (len : Int) : Val := hl_val%
  rec go i := if i < #len then ((#l +ₗ i) ← #0; let i' := i + #1; go i') else #()

theorem zeroArray_spec (l : Loc) (vs : List Val) :
    arrayPointsTo l vs ⊑
      wp⟦Exp.app (Exp.ofVal (zeroArray l vs.length)) (Exp.ofVal (.lit (.int 0)))⟧
        (fun _ => arrayPointsTo l (List.replicate vs.length (.lit (.int 0)))) := by
  -- Whole-array invariant: `out` stays one contiguous block (zeroed prefix ++ untouched suffix),
  -- so the store's footprint is the *entire* array and `vcgen` never needs to frame.
  have key := wp_rec (wp := wp) (A := Nat) (fun i => vs.length - i) _ _ _ (zeroArray l vs.length) rfl
    (fun i => (.lit (.int i) : Val))
    (fun _ _ => arrayPointsTo l (List.replicate vs.length (.lit (.int 0))))
    (fun i => hand (hpure (i ≤ vs.length))
                (l ↦∗ (List.replicate i (.lit (.int 0)) ++ vs.drop i)))
    ?_
  · exact fun σ hσ => key 0 σ ⟨Nat.zero_le _, hσ⟩
  · intro i ih
    refine hand_hpure_mono (fun hle => ?_)
    simp only [zeroArray]; simp [Exp.subst, Exp.substStr]
    vcgen [spec_store_arr, spec_app_lam, ih]
    refine le_hexists _ (Val.lit (.bool (decide ((i : Int) < (vs.length : Int)))))
      (le_hand_pure (by simp [BinOp.eval]) ?_)
    refine le_hexists _ (decide ((i : Int) < (vs.length : Int))) (le_hand_pure rfl ?_)
    split
    · rename_i h
      simp only [decide_eq_true_eq] at h
      have hi : i < vs.length := by omega
      vcgen [spec_store_arr, spec_app_lam, ih, Exp.subst, Exp.substStr]
      case vc2 => simp only [List.length_append, List.length_replicate, List.length_drop]; omega
      case vc1 =>
        refine le_hexists _ (Val.lit (.int ((i : Int) + 1))) (le_hand_pure (by simp [BinOp.eval]) ?_)
        simp only [Exp.subst, Exp.substStr, substStr_ofVal]
        rw [show ((i : Int) + 1) = ((i + 1 : Nat) : Int) by omega]
        refine PartialOrder.rel_trans ?_ (ih (i + 1) (by omega))
        refine le_hand_pure (by omega) ?_
        refine PartialOrder.rel_of_eq ?_
        congr 1
        rw [List.set_append, List.length_replicate, if_neg (Nat.lt_irrefl i), Nat.sub_self,
          List.drop_eq_getElem_cons hi, List.set_cons_zero, List.replicate_succ', List.append_assoc,
          List.singleton_append]
    · rename_i h
      simp only [decide_eq_true_eq] at h
      have hi : i = vs.length := by omega
      subst hi
      simp only [List.drop_length, List.append_nil]
      vcgen

/-! ## `delta` compression loop

A verification-oriented transcription of `Codec.Delta.compress`'s inner loop: each byte is stored as
its difference from the running previous byte, reduced mod 256.  Loads of `src[i]` and `prev` are
hoisted into `let`s so every primitive step operates on value operands (behaviourally identical to
the fused `Delta.compress`). -/
def deltaCompressLoop (src out prev : Loc) (n : Int) : Val := hl_val%
  rec go i :=
    if i < #n then
      let c := !(#src +ₗ i);
      let p := !(#prev);
      let d := ((c - p) + #256) % #256;
      (#out +ₗ i) ← d;
      #prev ← c;
      let i' := i + #1;
      go i'
    else #()

/-- Correctness of the compression loop: starting at index `i` with `out[0,i)` already holding the
delta-encoding of the first `i` bytes and `prev` holding the running previous byte, running the loop
fills the rest of `out` with the full delta-encoding of `ns`.  `src` is read-only. -/
theorem deltaCompressLoop_spec (src out prev : Loc) (ns : List Int)
    (hbytes : ∀ x ∈ ns, 0 ≤ x ∧ x < 256) :
    ∀ i : Nat, i ≤ ns.length →
      ((src ↦∗ (ns.map byteVal)) ∗ (prev ↦ (byteVal ((ns.take i).getLastD 0))) ∗
        (out ↦∗ ((deltaEnc 0 (ns.take i)).map byteVal ++
          List.replicate (ns.length - i) (byteVal 0))))
      ⊑ wp⟦Exp.app (Exp.ofVal (deltaCompressLoop src out prev ns.length)) (Exp.ofVal (.lit (.int i)))⟧
          (fun _ => (src ↦∗ (ns.map byteVal)) ∗ (hexists fun p => prev ↦ (byteVal p)) ∗
            (out ↦∗ ((deltaEnc 0 ns).map byteVal))) := by
  intro i0 hi0
  have key := wp_rec (wp := wp) (A := Nat) (fun i => ns.length - i) _ _ _
    (deltaCompressLoop src out prev ns.length) rfl
    (fun i => (.lit (.int i) : Val))
    (fun _ _ => (src ↦∗ (ns.map byteVal)) ∗ (hexists fun p => prev ↦ (byteVal p)) ∗
      (out ↦∗ ((deltaEnc 0 ns).map byteVal)))
    (fun i => hand (hpure (i ≤ ns.length))
      ((src ↦∗ (ns.map byteVal)) ∗ (prev ↦ (byteVal ((ns.take i).getLastD 0))) ∗
        (out ↦∗ ((deltaEnc 0 (ns.take i)).map byteVal ++
          List.replicate (ns.length - i) (byteVal 0)))))
    ?_
  · exact PartialOrder.rel_trans (le_hand_pure hi0 PartialOrder.rel_refl) (key i0)
  · intro i ih
    refine hand_hpure_mono (fun hle => ?_)
    simp only [deltaCompressLoop]
    simp [Exp.subst, Exp.substStr]
    vcgen [spec_app_lam]
    refine le_hexists _ (Val.lit (.bool (decide ((i : Int) < (ns.length : Int)))))
      (le_hand_pure (by simp [BinOp.eval]) ?_)
    refine le_hexists _ (decide ((i : Int) < (ns.length : Int))) (le_hand_pure rfl ?_)
    split
    · rename_i h
      simp only [decide_eq_true_eq] at h
      have hi : i < ns.length := by omega
      have hiNS : i < (ns.map byteVal).length := by rw [List.length_map]; exact hi
      -- load `c := src[i] = byteVal ns[i]`
      refine wp_let_load_arr _ src (ns.map byteVal) i hiNS _ _ _ ?_
      simp [Exp.subst, Exp.substStr, List.getElem_map]
      -- load `p := prev`  (rearrange prev to the frame's rightmost slot)
      refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (by ac_rfl :
        _ = (((src ↦∗ (ns.map byteVal)) ∗ (out ↦∗ (List.map byteVal (deltaEnc 0 (List.take i ns)) ++
          List.replicate (ns.length - i) (byteVal 0)))) ∗
          (prev ↦ (byteVal ((List.take i ns).getLast?.getD 0)))))) ?_
      refine wp_let_load _ prev (byteVal ((List.take i ns).getLast?.getD 0)) _ _ _ ?_
      simp [Exp.subst, Exp.substStr]
      -- compute `d := ((c - p) + 256) % 256`
      refine PartialOrder.rel_trans ?_ spec_app_lam
      refine PartialOrder.rel_trans ?_ (wp_delta_arith (ns[i]'hi) ((List.take i ns).getLast?.getD 0) _)
      simp [Exp.subst, Exp.substStr]
      -- store `out[i] := d`  (bring `out` to the front)
      have hiOS : i < (List.map byteVal (deltaEnc 0 (List.take i ns)) ++
          List.replicate (ns.length - i) (byteVal 0)).length := by
        rw [List.length_append, List.length_map, deltaEnc_length, List.length_take,
          List.length_replicate]; omega
      refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (by ac_rfl :
        _ = ((out ↦∗ (List.map byteVal (deltaEnc 0 (List.take i ns)) ++
          List.replicate (ns.length - i) (byteVal 0))) ∗
          ((src ↦∗ (ns.map byteVal)) ∗ (prev ↦ (byteVal ((List.take i ns).getLast?.getD 0))))))) ?_
      refine wp_seq_store_arr _ out _ i hiOS
        (byteVal ((ns[i]'hi - (List.take i ns).getLast?.getD 0 + 256).tmod 256)) _ _ ?_
      -- store `prev := c`  (bring `prev` to the front)
      refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (by ac_rfl :
        _ = (((out ↦∗ ((List.map byteVal (deltaEnc 0 (List.take i ns)) ++
          List.replicate (ns.length - i) (byteVal 0)).set i
            (byteVal ((ns[i]'hi - (List.take i ns).getLast?.getD 0 + 256).tmod 256)))) ∗
          (src ↦∗ (ns.map byteVal))) ∗
          (prev ↦ (byteVal ((List.take i ns).getLast?.getD 0)))))) ?_
      refine wp_seq_store _ prev (byteVal ((List.take i ns).getLast?.getD 0))
        (byteVal (ns[i]'hi)) _ _ ?_
      -- recurse: reduce `let i' := i+1; go i'`, then apply the IH at `i+1`
      vcgen
      refine le_hexists _ (Val.lit (.int ((i : Int) + 1))) (le_hand_pure (by simp [BinOp.eval]) ?_)
      refine PartialOrder.rel_trans ?_ spec_rec
      refine le_hexists _ _ (le_hexists _ _ (le_hexists _ _ (le_hand_pure rfl ?_)))
      simp only [Exp.subst, Exp.substStr, substStr_ofVal]
      rw [show ((i : Int) + 1) = ((i + 1 : Nat) : Int) by omega]
      refine PartialOrder.rel_trans ?_ (ih (i + 1) (by omega))
      refine le_hand_pure (by omega) ?_
      -- pure data facts for the invariant at `i+1`
      have hnn : (0 : Int) ≤ ns[i]'hi := (hbytes (ns[i]'hi) (List.getElem_mem hi)).1
      have hp0 : (List.take i ns).getLast?.getD 0 < 256 := by
        rcases hlast : (List.take i ns).getLast? with _ | x
        · simp [hlast]
        · simp only [hlast, Option.getD]
          exact (hbytes x (List.mem_of_mem_take (List.mem_of_getLast? hlast))).2
      have htake : List.take (i + 1) ns = List.take i ns ++ [ns[i]'hi] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
      have hlen : (List.map byteVal (deltaEnc 0 (List.take i ns))).length = i := by
        rw [List.length_map, deltaEnc_length, List.length_take]; omega
      have hprevv : (List.take (i + 1) ns).getLastD 0 = ns[i]'hi := by
        rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.length_take,
          Nat.min_eq_left (by omega : i + 1 ≤ ns.length)]; simp [hi]
      have hval : (ns[i]'hi - (List.take i ns).getLast?.getD 0 + 256).tmod 256
          = (ns[i]'hi - (List.take i ns).getLastD 0 + 256) % 256 := by
        rw [List.getLastD_eq_getLast?, Int.tmod_eq_emod]
        simp [show (0 : Int) ≤ ns[i]'hi - (List.take i ns).getLast?.getD 0 + 256 by omega]
      have hout : (List.map byteVal (deltaEnc 0 (List.take i ns)) ++
            List.replicate (ns.length - i) (byteVal 0)).set i
            (byteVal ((ns[i]'hi - (List.take i ns).getLast?.getD 0 + 256).tmod 256))
          = List.map byteVal (deltaEnc 0 (List.take (i + 1) ns)) ++
            List.replicate (ns.length - (i + 1)) (byteVal 0) := by
        rw [hval, htake, deltaEnc_snoc, List.map_append, List.map_cons, List.map_nil,
          show ns.length - i = (ns.length - (i + 1)) + 1 by omega, List.replicate_succ,
          List.append_assoc]
        simp [hlen, List.set_append]
      -- assemble: rewrite `out` and `prev` in the invariant, then close by AC
      refine PartialOrder.rel_of_eq ?_
      rw [hprevv, hout]
      ac_rfl
    · rename_i h
      simp only [decide_eq_true_eq] at h
      have hi : i = ns.length := by omega
      subst hi
      -- exit: `#()`; the invariant at `i = len` is exactly the postcondition (prev existentially)
      simp only [List.take_length, Nat.sub_self, List.replicate, List.append_nil]
      refine PartialOrder.rel_trans ?_ spec_val
      rintro σ ⟨σ1, σ2, hd, rfl, hSRC, σ3, σ4, hd', heq2, hPREV, hOUT⟩
      exact ⟨σ1, σ2, hd, rfl, hSRC, σ3, σ4, hd', heq2, ⟨_, hPREV⟩, hOUT⟩

/-! ## `delta` decompression loop -/

/-- The `delta` decode value `(p + d) % 256` evaluates purely to a byte. -/
theorem wp_delta_dec_arith (p d : Int) (Φ : Val → HProp) :
    Φ (byteVal (Int.tmod (p + d) 256)) ⊑
      wp⟦Exp.binop BinOp.tmod (Exp.binop BinOp.plus (Exp.ofVal (byteVal p)) (Exp.ofVal (byteVal d)))
          (Exp.ofVal (byteVal 256))⟧ Φ := by
  refine PartialOrder.rel_trans ?_ spec_binop
  refine PartialOrder.rel_trans ?_ spec_val
  refine PartialOrder.rel_trans ?_ spec_binop
  refine PartialOrder.rel_trans ?_ spec_val
  refine PartialOrder.rel_trans ?_ spec_val
  refine le_hexists _ (byteVal (p + d)) (le_hand_pure (by simp [BinOp.eval, byteVal]) ?_)
  refine le_hexists _ (byteVal (Int.tmod (p + d) 256))
    (le_hand_pure (by simp [BinOp.eval, byteVal]) ?_)
  exact PartialOrder.rel_refl

/-- Verification-oriented transcription of `Codec.Delta.decompress`'s inner loop: the inverse
prefix-sum.  Loads of `src[i]` and `prev` are hoisted into `let`s. -/
def deltaDecompressLoop (src out prev : Loc) (n : Int) : Val := hl_val%
  rec go i :=
    if i < #n then
      let d := !(#src +ₗ i);
      let p := !(#prev);
      let c := (p + d) % #256;
      (#out +ₗ i) ← c;
      #prev ← c;
      let i' := i + #1;
      go i'
    else #()

/-- Correctness of the decompression loop against the pure `deltaDec` model.  `src` (the encoded
deltas) is read-only; `out` is filled with the decoded bytes. -/
theorem deltaDecompressLoop_spec (src out prev : Loc) (ds : List Int)
    (hbytes : ∀ x ∈ ds, 0 ≤ x ∧ x < 256) :
    ∀ i : Nat, i ≤ ds.length →
      ((src ↦∗ (ds.map byteVal)) ∗ (prev ↦ (byteVal ((deltaDec 0 (ds.take i)).getLastD 0))) ∗
        (out ↦∗ ((deltaDec 0 (ds.take i)).map byteVal ++
          List.replicate (ds.length - i) (byteVal 0))))
      ⊑ wp⟦Exp.app (Exp.ofVal (deltaDecompressLoop src out prev ds.length))
          (Exp.ofVal (.lit (.int i)))⟧
          (fun _ => (src ↦∗ (ds.map byteVal)) ∗ (hexists fun p => prev ↦ (byteVal p)) ∗
            (out ↦∗ ((deltaDec 0 ds).map byteVal))) := by
  intro i0 hi0
  have key := wp_rec (wp := wp) (A := Nat) (fun i => ds.length - i) _ _ _
    (deltaDecompressLoop src out prev ds.length) rfl
    (fun i => (.lit (.int i) : Val))
    (fun _ _ => (src ↦∗ (ds.map byteVal)) ∗ (hexists fun p => prev ↦ (byteVal p)) ∗
      (out ↦∗ ((deltaDec 0 ds).map byteVal)))
    (fun i => hand (hpure (i ≤ ds.length))
      ((src ↦∗ (ds.map byteVal)) ∗ (prev ↦ (byteVal ((deltaDec 0 (ds.take i)).getLastD 0))) ∗
        (out ↦∗ ((deltaDec 0 (ds.take i)).map byteVal ++
          List.replicate (ds.length - i) (byteVal 0)))))
    ?_
  · exact PartialOrder.rel_trans (le_hand_pure hi0 PartialOrder.rel_refl) (key i0)
  · intro i ih
    refine hand_hpure_mono (fun hle => ?_)
    simp only [deltaDecompressLoop]
    simp [Exp.subst, Exp.substStr]
    vcgen [spec_app_lam]
    refine le_hexists _ (Val.lit (.bool (decide ((i : Int) < (ds.length : Int)))))
      (le_hand_pure (by simp [BinOp.eval]) ?_)
    refine le_hexists _ (decide ((i : Int) < (ds.length : Int))) (le_hand_pure rfl ?_)
    split
    · rename_i h
      simp only [decide_eq_true_eq] at h
      have hi : i < ds.length := by omega
      have hiNS : i < (ds.map byteVal).length := by rw [List.length_map]; exact hi
      -- load `d := src[i] = byteVal ds[i]`
      refine wp_let_load_arr _ src (ds.map byteVal) i hiNS _ _ _ ?_
      simp [Exp.subst, Exp.substStr, List.getElem_map]
      -- load `p := prev`
      refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (by ac_rfl :
        _ = (((src ↦∗ (ds.map byteVal)) ∗ (out ↦∗ (List.map byteVal (deltaDec 0 (List.take i ds)) ++
          List.replicate (ds.length - i) (byteVal 0)))) ∗
          (prev ↦ (byteVal ((deltaDec 0 (List.take i ds)).getLast?.getD 0)))))) ?_
      refine wp_let_load _ prev (byteVal ((deltaDec 0 (List.take i ds)).getLast?.getD 0)) _ _ _ ?_
      simp [Exp.subst, Exp.substStr]
      -- compute `c := (p + d) % 256`
      refine PartialOrder.rel_trans ?_ spec_app_lam
      refine PartialOrder.rel_trans ?_
        (wp_delta_dec_arith ((deltaDec 0 (List.take i ds)).getLast?.getD 0) (ds[i]'hi) _)
      simp [Exp.subst, Exp.substStr]
      -- store `out[i] := c`
      have hiOS : i < (List.map byteVal (deltaDec 0 (List.take i ds)) ++
          List.replicate (ds.length - i) (byteVal 0)).length := by
        rw [List.length_append, List.length_map, deltaDec_length, List.length_take,
          List.length_replicate]; omega
      refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (by ac_rfl :
        _ = ((out ↦∗ (List.map byteVal (deltaDec 0 (List.take i ds)) ++
          List.replicate (ds.length - i) (byteVal 0))) ∗
          ((src ↦∗ (ds.map byteVal)) ∗
            (prev ↦ (byteVal ((deltaDec 0 (List.take i ds)).getLast?.getD 0))))))) ?_
      refine wp_seq_store_arr _ out _ i hiOS
        (byteVal (((deltaDec 0 (List.take i ds)).getLast?.getD 0 + ds[i]'hi).tmod 256)) _ _ ?_
      -- store `prev := c`
      refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (by ac_rfl :
        _ = (((out ↦∗ ((List.map byteVal (deltaDec 0 (List.take i ds)) ++
          List.replicate (ds.length - i) (byteVal 0)).set i
            (byteVal (((deltaDec 0 (List.take i ds)).getLast?.getD 0 + ds[i]'hi).tmod 256)))) ∗
          (src ↦∗ (ds.map byteVal))) ∗
          (prev ↦ (byteVal ((deltaDec 0 (List.take i ds)).getLast?.getD 0)))))) ?_
      refine wp_seq_store _ prev (byteVal ((deltaDec 0 (List.take i ds)).getLast?.getD 0))
        (byteVal (((deltaDec 0 (List.take i ds)).getLast?.getD 0 + ds[i]'hi).tmod 256)) _ _ ?_
      -- recurse
      vcgen
      refine le_hexists _ (Val.lit (.int ((i : Int) + 1))) (le_hand_pure (by simp [BinOp.eval]) ?_)
      refine PartialOrder.rel_trans ?_ spec_rec
      refine le_hexists _ _ (le_hexists _ _ (le_hexists _ _ (le_hand_pure rfl ?_)))
      simp only [Exp.subst, Exp.substStr, substStr_ofVal]
      rw [show ((i : Int) + 1) = ((i + 1 : Nat) : Int) by omega]
      refine PartialOrder.rel_trans ?_ (ih (i + 1) (by omega))
      refine le_hand_pure (by omega) ?_
      -- pure data facts for the invariant at `i+1`
      have hdnn : (0 : Int) ≤ ds[i]'hi := (hbytes (ds[i]'hi) (List.getElem_mem hi)).1
      have hp0 : 0 ≤ (deltaDec 0 (List.take i ds)).getLast?.getD 0 := by
        rcases hlast : (deltaDec 0 (List.take i ds)).getLast? with _ | x
        · simp [hlast]
        · simp only [hlast, Option.getD]
          exact (deltaDec_mem_range 0 (List.take i ds) x (List.mem_of_getLast? hlast)).1
      have htake : List.take (i + 1) ds = List.take i ds ++ [ds[i]'hi] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
      have hlen : (List.map byteVal (deltaDec 0 (List.take i ds))).length = i := by
        rw [List.length_map, deltaDec_length, List.length_take]; omega
      have hval : ((deltaDec 0 (List.take i ds)).getLast?.getD 0 + ds[i]'hi).tmod 256
          = ((deltaDec 0 (List.take i ds)).getLastD 0 + ds[i]'hi) % 256 := by
        rw [List.getLastD_eq_getLast?, Int.tmod_eq_emod]
        simp [show (0 : Int) ≤ (deltaDec 0 (List.take i ds)).getLast?.getD 0 + ds[i]'hi by omega]
      have hprevv : (deltaDec 0 (List.take (i + 1) ds)).getLastD 0
          = ((deltaDec 0 (List.take i ds)).getLastD 0 + ds[i]'hi) % 256 := by
        rw [htake, deltaDec_snoc, List.getLastD_concat]
      have hout : (List.map byteVal (deltaDec 0 (List.take i ds)) ++
            List.replicate (ds.length - i) (byteVal 0)).set i
            (byteVal (((deltaDec 0 (List.take i ds)).getLast?.getD 0 + ds[i]'hi).tmod 256))
          = List.map byteVal (deltaDec 0 (List.take (i + 1) ds)) ++
            List.replicate (ds.length - (i + 1)) (byteVal 0) := by
        rw [hval, htake, deltaDec_snoc, List.map_append, List.map_cons, List.map_nil,
          show ds.length - i = (ds.length - (i + 1)) + 1 by omega, List.replicate_succ,
          List.append_assoc]
        simp [hlen, List.set_append]
      -- assemble: rewrite `out` and `prev`, close by AC
      refine PartialOrder.rel_of_eq ?_
      rw [show (deltaDec 0 (List.take (i + 1) ds)).getLastD 0
            = ((deltaDec 0 (List.take i ds)).getLastD 0 + ds[i]'hi) % 256 from hprevv,
        ← hval, hout]
      ac_rfl
    · rename_i h
      simp only [decide_eq_true_eq] at h
      have hi : i = ds.length := by omega
      subst hi
      simp only [List.take_length, Nat.sub_self, List.replicate, List.append_nil]
      refine PartialOrder.rel_trans ?_ spec_val
      rintro σ ⟨σ1, σ2, hd, rfl, hSRC, σ3, σ4, hd', heq2, hPREV, hOUT⟩
      exact ⟨σ1, σ2, hd, rfl, hSRC, σ3, σ4, hd', heq2, ⟨_, hPREV⟩, hOUT⟩

/-! ## Top-level `delta` functions and the end-to-end round-trip

Each top-level function does the `bytes`-prelude (read length/base, allocate output, init `prev`) and then
runs the loop.  Crucially, once the `let src`/`out`/`prev` bindings are symbolically executed, the
inlined loop *is* `deltaCompressLoop`/`deltaDecompressLoop` at the freshly-allocated locations, so the
loop specs apply directly. -/

/-- Full `delta` compression: `bytes → bytes`.  Mirrors `Codec.Delta.compress` (loads hoisted). -/
def deltaCompressFn : Val := hl_val%
  λ b,
    let n := snd(b);
    let src := fst(b);
    let out := allocn(n, #0);
    let prev := ref(#0);
    let loop := (rec go i :=
      if i < n then
        let c := !(src +ₗ i);
        let p := !(prev);
        let d := ((c - p) + #256) % #256;
        (out +ₗ i) ← d;
        prev ← c;
        let i' := i + #1;
        go i'
      else #());
    loop #0;
    (out, n)

/-- Full `delta` decompression: `bytes → bytes`.  Mirrors `Codec.Delta.decompress` (loads hoisted). -/
def deltaDecompressFn : Val := hl_val%
  λ b,
    let n := snd(b);
    let src := fst(b);
    let out := allocn(n, #0);
    let prev := ref(#0);
    let loop := (rec go i :=
      if i < n then
        let d := !(src +ₗ i);
        let p := !(prev);
        let c := (p + d) % #256;
        (out +ₗ i) ← c;
        prev ← c;
        let i' := i + #1;
        go i'
      else #());
    loop #0;
    (out, n)

/-- Top-level compression correctness: compressing `bytes(srcl, |ns|)` yields a fresh `bytes(outl, |ns|)`
holding the delta-encoding of `ns`; the input is preserved. -/
theorem deltaCompressFn_spec (srcl : Loc) (ns : List Int)
    (hbytes : ∀ x ∈ ns, 0 ≤ x ∧ x < 256) (hne : 0 < ns.length) :
    (srcl ↦∗ (ns.map byteVal))
      ⊑ wp⟦Exp.app (Exp.ofVal deltaCompressFn) (Exp.ofVal (bytesVal srcl ns.length))⟧
          (fun r => hexists fun outl => hexists fun prevl => hexists fun p =>
            hand (hpure (r = bytesVal outl ns.length))
              ((srcl ↦∗ (ns.map byteVal)) ∗ (prevl ↦ (byteVal p)) ∗
                (outl ↦∗ ((deltaEnc 0 ns).map byteVal)))) := by
  simp only [deltaCompressFn]
  refine PartialOrder.rel_trans ?_ (wp_beta _ _ _ _ _)
  simp only [Exp.subst, Exp.substStr, bytesVal]
  -- prelude: read length & base, allocate `out`, init `prev`
  refine wp_let_snd _ (Val.lit (.loc srcl)) (Val.lit (.int ns.length)) _ _ _ ?_
  simp only [Exp.subst, Exp.substStr]
  refine wp_let_fst _ (Val.lit (.loc srcl)) (Val.lit (.int ns.length)) _ _ _ ?_
  simp only [Exp.subst, Exp.substStr]
  refine wp_let_allocN _ ns.length (byteVal 0) hne _ _ _ ?_
  intro outl
  simp only [Exp.subst, Exp.substStr]
  refine wp_let_ref _ (byteVal 0) _ _ _ ?_
  intro prevl
  simp only [Exp.subst, Exp.substStr]
  -- bind the loop value, then run `loop #0; (out, n)`
  refine PartialOrder.rel_trans ?_ spec_app_lam
  refine PartialOrder.rel_trans ?_ spec_rec
  simp only [Exp.subst, Exp.substStr]
  refine PartialOrder.rel_trans ?_ spec_app_lam
  -- enter the loop at i = 0 (state = invariant at 0), then finish with the returned pair
  refine PartialOrder.rel_trans ?_
    (PartialOrder.rel_trans (deltaCompressLoop_spec srcl outl prevl ns hbytes 0 (by omega))
      (wp_mono ?_))
  · -- state ⊑ invariant(0)
    refine PartialOrder.rel_of_eq ?_
    simp only [List.take_zero, deltaEnc, List.map_nil, List.nil_append, Nat.sub_zero,
      List.getLastD_nil, byteVal]
    ac_rfl
  · -- after the loop, return `(out, n)`
    intro _
    refine PartialOrder.rel_trans ?_ spec_pair
    refine PartialOrder.rel_trans ?_ spec_val
    refine PartialOrder.rel_trans ?_ spec_val
    refine le_hexists _ outl (le_hexists _ prevl ?_)
    rintro σ ⟨σ1, σ2, hd, rfl, hSRC, σ3, σ4, hd', heq, ⟨p, hPREV⟩, hOUT⟩
    exact ⟨p, rfl, σ1, σ2, hd, rfl, hSRC, σ3, σ4, hd', heq, hPREV, hOUT⟩

/-- Top-level decompression correctness (dual of `deltaCompressFn_spec`). -/
theorem deltaDecompressFn_spec (srcl : Loc) (ds : List Int)
    (hbytes : ∀ x ∈ ds, 0 ≤ x ∧ x < 256) (hne : 0 < ds.length) :
    (srcl ↦∗ (ds.map byteVal))
      ⊑ wp⟦Exp.app (Exp.ofVal deltaDecompressFn) (Exp.ofVal (bytesVal srcl ds.length))⟧
          (fun r => hexists fun outl => hexists fun prevl => hexists fun p =>
            hand (hpure (r = bytesVal outl ds.length))
              ((srcl ↦∗ (ds.map byteVal)) ∗ (prevl ↦ (byteVal p)) ∗
                (outl ↦∗ ((deltaDec 0 ds).map byteVal)))) := by
  simp only [deltaDecompressFn]
  refine PartialOrder.rel_trans ?_ (wp_beta _ _ _ _ _)
  simp only [Exp.subst, Exp.substStr, bytesVal]
  refine wp_let_snd _ (Val.lit (.loc srcl)) (Val.lit (.int ds.length)) _ _ _ ?_
  simp only [Exp.subst, Exp.substStr]
  refine wp_let_fst _ (Val.lit (.loc srcl)) (Val.lit (.int ds.length)) _ _ _ ?_
  simp only [Exp.subst, Exp.substStr]
  refine wp_let_allocN _ ds.length (byteVal 0) hne _ _ _ ?_
  intro outl
  simp only [Exp.subst, Exp.substStr]
  refine wp_let_ref _ (byteVal 0) _ _ _ ?_
  intro prevl
  simp only [Exp.subst, Exp.substStr]
  refine PartialOrder.rel_trans ?_ spec_app_lam
  refine PartialOrder.rel_trans ?_ spec_rec
  simp only [Exp.subst, Exp.substStr]
  refine PartialOrder.rel_trans ?_ spec_app_lam
  refine PartialOrder.rel_trans ?_
    (PartialOrder.rel_trans (deltaDecompressLoop_spec srcl outl prevl ds hbytes 0 (by omega))
      (wp_mono ?_))
  · refine PartialOrder.rel_of_eq ?_
    simp only [List.take_zero, deltaDec, List.map_nil, List.nil_append, Nat.sub_zero,
      List.getLastD_nil, byteVal]
    ac_rfl
  · intro _
    refine PartialOrder.rel_trans ?_ spec_pair
    refine PartialOrder.rel_trans ?_ spec_val
    refine PartialOrder.rel_trans ?_ spec_val
    refine le_hexists _ outl (le_hexists _ prevl ?_)
    rintro σ ⟨σ1, σ2, hd, rfl, hSRC, σ3, σ4, hd', heq, ⟨p, hPREV⟩, hOUT⟩
    exact ⟨p, rfl, σ1, σ2, hd, rfl, hSRC, σ3, σ4, hd', heq, hPREV, hOUT⟩

/-- **End-to-end round-trip:** decompressing the compression of `bytes(srcl, |ns|)` recovers `ns`.
Composes the two top-level specs through the pure round-trip `deltaDec_deltaEnc`.  The input and all
intermediate/scratch cells are retained (linear separation logic), so they appear existentially. -/
theorem delta_roundtrip (srcl : Loc) (ns : List Int)
    (hbytes : ∀ x ∈ ns, 0 ≤ x ∧ x < 256) (hne : 0 < ns.length) :
    (srcl ↦∗ (ns.map byteVal))
      ⊑ wp⟦Exp.app (Exp.ofVal deltaDecompressFn)
          (Exp.app (Exp.ofVal deltaCompressFn) (Exp.ofVal (bytesVal srcl ns.length)))⟧
          (fun r => hexists fun out2 => hexists fun outl => hexists fun prevl =>
            hexists fun prev2 => hexists fun p => hexists fun p2 =>
              hand (hpure (r = bytesVal out2 ns.length))
                ((srcl ↦∗ (ns.map byteVal)) ∗ (out2 ↦∗ (ns.map byteVal)) ∗ (prevl ↦ (byteVal p)) ∗
                  (prev2 ↦ (byteVal p2)) ∗ (outl ↦∗ ((deltaEnc 0 ns).map byteVal)))) := by
  -- evaluate the inner `compress` call first
  refine PartialOrder.rel_trans ?_ (wp_bind (wp := wp) (ECtxItem.appR (Exp.ofVal deltaDecompressFn)))
  refine PartialOrder.rel_trans (deltaCompressFn_spec (wp := wp) srcl ns hbytes hne) (wp_mono ?_)
  intro v
  refine hexists_le (fun outl => hexists_le (fun prevl => hexists_le (fun p => ?_)))
  refine hand_hpure_mono (fun hv => ?_)
  subst hv
  -- run `decompress` on the compressed output, framing the retained cells
  have hspec := deltaDecompressFn_spec (wp := wp) outl (deltaEnc 0 ns) (deltaEnc_mem_range 0 ns)
    (by rw [deltaEnc_length]; exact hne)
  rw [deltaEnc_length 0 ns, deltaDec_deltaEnc ns hbytes 0] at hspec
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (by ac_rfl :
    _ = (((srcl ↦∗ (ns.map byteVal)) ∗ (prevl ↦ (byteVal p))) ∗
      (outl ↦∗ ((deltaEnc 0 ns).map byteVal))))) ?_
  refine PartialOrder.rel_trans (sepConj_mono_r hspec) ?_
  refine PartialOrder.rel_trans (wp_frame _) ?_
  refine wp_mono ?_
  intro r2
  refine sepConj_hexists_le _ _ _ (fun out2 => sepConj_hexists_le _ _ _ (fun prev2 =>
    sepConj_hexists_le _ _ _ (fun p2 => sepConj_hand_pure_le _ _ _ (fun hr2 => ?_))))
  subst hr2
  refine le_hexists _ out2 (le_hexists _ outl (le_hexists _ prevl (le_hexists _ prev2
    (le_hexists _ p (le_hexists _ p2 (le_hand_pure rfl ?_))))))
  refine PartialOrder.rel_of_eq ?_
  ac_rfl

end
end Iris.HeapLang.Codec
