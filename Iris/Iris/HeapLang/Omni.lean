/-
An omnisemantics (omni-WP) for a fragment of HeapLang, built as the greatest
fixpoint of the safety functional over the language's `primStep`, and a bridge
showing it produces an `adequate` (partial-correctness) predicate.
-/
module

public import Iris.HeapLang.Instances
public import Iris.ProgramLogic.Adequacy
public import Std.Internal.Do.WP.Basic

@[expose] public section
namespace Iris.HeapLang

open ProgramLogic PrimStep Language Language.Notation Lean.Order

/-! ## Greatest fixpoint (dual of `Lean.Order.lfp`) -/

section gfp
open Lean.Order.PartialOrder Lean.Order.CompleteLattice
variable {α : Sort u} [Lean.Order.CompleteLattice α]

/-- Greatest fixpoint: the largest post-fixed point `x ⊑ f x`. -/
noncomputable def gfp (f : α → α) : α := sup (fun x => x ⊑ f x)

/-- Coinduction: any post-fixed point is below `gfp f`. -/
theorem le_gfp {f : α → α} {x : α} (h : x ⊑ f x) : x ⊑ gfp f := le_sup _ h

theorem gfp_postfixed {f : α → α} (hm : monotone f) : gfp f ⊑ f (gfp f) := by
  apply sup_le; intro y hy
  exact rel_trans hy (hm _ _ (le_sup _ hy))

theorem gfp_prefixed {f : α → α} (hm : monotone f) : f (gfp f) ⊑ gfp f :=
  le_gfp (hm _ _ (gfp_postfixed hm))

theorem gfp_fix {f : α → α} (hm : monotone f) : gfp f = f (gfp f) :=
  rel_antisymm (gfp_postfixed hm) (gfp_prefixed hm)

end gfp

/-! ## The omni-WP for HeapLang

`WPArg := State → (Val → State → Prop) → Prop`, ordered pointwise (so it is a
`CompleteLattice` via the `Prop` instance and pi-lifting), and `wp` is the gfp
of the safety functional `wpF`. -/

abbrev WPArg := Exp → State → (Val → State → Prop) → Prop

/-- One unfolding of the (sequential) safety predicate: either a value
satisfying the post, or reducible and every successor is again safe. Forks are
forbidden — this is the fork-free fragment, so every step has `efs = []`. -/
def wpF (r : WPArg) : WPArg := fun e σ Q =>
  (∃ v, ToVal.toVal e = some v ∧ Q v σ) ∨
  (Reducible (e, σ) ∧
    ∀ κ e' σ' efs, (e, σ) -<κ>-> (e', σ', efs) → efs = [] ∧ r e' σ' Q)

noncomputable def wp : WPArg := gfp wpF

theorem wpF_monotone : monotone wpF := by
  intro r1 r2 h e σ Q hr
  rcases hr with hv | ⟨hred, hstep⟩
  · exact .inl hv
  · refine .inr ⟨hred, fun κ e' σ' efs hs => ?_⟩
    obtain ⟨hnil, h1⟩ := hstep κ e' σ' efs hs
    exact ⟨hnil, h e' σ' Q h1⟩

/-- The defining fixpoint equation for `wp`. -/
theorem wp_unfold : wp = wpF wp := gfp_fix wpF_monotone

theorem wp_unfold_apply {e σ Q} : wp e σ Q ↔ wpF wp e σ Q := by rw [← wp_unfold]

/-- Coinduction principle: an invariant closed under `wpF` is below `wp`. -/
theorem wp_coind (I : WPArg) (h : ∀ e σ Q, I e σ Q → wpF I e σ Q) :
    ∀ e σ Q, I e σ Q → wp e σ Q :=
  le_gfp (f := wpF) (x := I) h

/-! ## Adequacy bridge (fork-free fragment)

Since `wpF` forbids forks, a `wp`-safe singleton pool steps only to `wp`-safe
singleton pools. Lifting this invariant along `-·->ₜₚ*` discharges the three
`AdequateNoFork` obligations. -/

/-- A `wp`-safe thread that steps stays `wp`-safe (and the step produces no
forks). The new state `σ'` is the successor's state, so there is no
interference to reason about. -/
theorem wp_primStep {e σ Q κ e' σ' efs}
    (hwp : wp e σ Q) (hstep : (e, σ) -<κ>-> (e', σ', efs)) :
    efs = [] ∧ wp e' σ' Q := by
  rw [wp_unfold_apply] at hwp
  rcases hwp with ⟨v, hv, _⟩ | ⟨_, hk⟩
  · exact absurd (Language.val_stuck hstep) (by rw [hv]; exact Option.some_ne_none v)
  · exact hk κ e' σ' efs hstep

/-- A `wp`-safe thread is not stuck. -/
theorem wp_notStuck {e σ Q} (hwp : wp e σ Q) : NotStuck (e, σ) := by
  rw [wp_unfold_apply] at hwp
  rcases hwp with ⟨v, hv, _⟩ | ⟨hred, _⟩
  · exact .inl (by rw [hv]; exact rfl)
  · exact .inr hred

/-- One pool step out of a `wp`-safe singleton lands on a `wp`-safe singleton. -/
theorem wp_erasedStep {e σ Q t' σ'} (hwp : wp e σ Q)
    (hstep : ([e], σ) -·->ₜₚ (t', σ')) : ∃ e', t' = [e'] ∧ wp e' σ' Q := by
  obtain ⟨κ, hstep⟩ := hstep
  generalize hsrc : ([e], σ) = src at hstep
  cases hstep with
  | @atomic e₀ _ _ e' _ efs hbase t₁ t₂ =>
    obtain ⟨hpool, rfl⟩ := Prod.mk.injEq .. ▸ hsrc
    -- [e] = t₁ ++ e₀ :: t₂ forces t₁ = t₂ = [] and e₀ = e
    rcases List.append_eq_cons_iff.mp hpool.symm with ⟨rfl, heq⟩ | ⟨a, _, hcontra⟩
    · obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp heq
      obtain ⟨rfl, hwp'⟩ := wp_primStep hwp hbase
      exact ⟨e', by simp, hwp'⟩
    · exact absurd hcontra (by simp)

/-- Reaching any pool from a `wp`-safe singleton keeps it a `wp`-safe singleton. -/
theorem wp_reach {e σ Q} (hwp : wp e σ Q) :
    ∀ {p : List Exp × State}, ([e], σ) -·->ₜₚ* p → ∃ e', p.1 = [e'] ∧ wp e' p.2 Q := by
  intro p hreach
  induction hreach with
  | refl => exact ⟨e, rfl, hwp⟩
  | @tail q r _ hstep ih =>
    obtain ⟨e₁, hq, hwp₁⟩ := ih
    obtain ⟨tq, σq⟩ := q; subst hq
    obtain ⟨tr, σr⟩ := r
    obtain ⟨e₂, rfl, hwp₂⟩ := wp_erasedStep hwp₁ hstep
    exact ⟨e₂, rfl, hwp₂⟩

/-- **Adequacy for the fork-free fragment**: the omni-`wp` yields an
`AdequateNoFork` partial-correctness predicate. -/
theorem wp_adequateNoFork (e : Exp) (σ : State) (Q : Val → State → Prop)
    (hwp : wp e σ Q) : AdequateNoFork .NotStuck e σ Q where
  no_fork hreach := by
    obtain ⟨e', hq, _⟩ := wp_reach hwp hreach; simp only at hq; rw [hq]; rfl
  result hreach := by
    obtain ⟨e', hq, hwp'⟩ := wp_reach hwp hreach; simp only at hq hwp'
    -- hq : ofVal v :: t₂ = [e'], so the pool is exactly [ofVal v] and e' = ofVal v
    obtain ⟨rfl, -⟩ := List.cons_eq_cons.mp hq
    rw [wp_unfold_apply] at hwp'
    rcases hwp' with ⟨v', hv', hQ⟩ | ⟨hred, _⟩
    · rw [ToVal.toVal_coe] at hv'; cases hv'; exact hQ
    · exact absurd (toVal_none_of_reducible hred) (by rw [ToVal.toVal_coe]; simp)
  not_stuck _ hreach hmem := by
    obtain ⟨e', hq, hwp'⟩ := wp_reach hwp hreach; simp only at hq hwp'
    rw [hq, List.mem_singleton] at hmem; subst hmem
    exact wp_notStuck hwp'

/-! ## `WPPre` instance (wiring into the `Do.lean` framework)

The omni-`wp` is the predicate transformer of the `WPPre` framework, with
result type `Val`, precondition lattice `State → Prop`, and the trivial
exceptional postcondition `EPost.nil` (the fragment is exception-free). -/

/-- `wp` is monotone in its postcondition. -/
theorem wp_mono {e σ} {Q Q' : Val → State → Prop}
    (hQ : ∀ v σ, Q v σ → Q' v σ) (hwp : wp e σ Q) : wp e σ Q' := by
  -- Coinduction: `fun e σ R => ∃ Q, (∀ v σ, Q v σ → R v σ) ∧ wp e σ Q` is `wpF`-closed.
  refine wp_coind (fun e σ R => ∃ Q, (∀ v σ, Q v σ → R v σ) ∧ wp e σ Q)
    (fun e σ R ⟨Q, hQR, hwpQ⟩ => ?_) e σ Q' ⟨Q, hQ, hwp⟩
  rw [wp_unfold_apply] at hwpQ
  rcases hwpQ with ⟨v, hv, hQv⟩ | ⟨hred, hstep⟩
  · exact .inl ⟨v, hv, hQR v σ hQv⟩
  · refine .inr ⟨hred, fun κ e' σ' efs hs => ?_⟩
    obtain ⟨hnil, hwp'⟩ := hstep κ e' σ' efs hs
    exact ⟨hnil, Q, hQR, hwp'⟩

/-! ## Bind / evaluation-context rule

`wp_bind` decomposes the wp of an expression sitting in an evaluation context:
evaluate the focus `e` to a value `v`, then continue with `K (ofVal v)`. Stated
for any `Language.Context K` (HeapLang provides `instContextFill` for
`fill K`). -/

theorem wp_bind {K : Exp → Exp} [Language.Context K] {e σ Q}
    (hwp : wp e σ (fun v σ' => wp (K (Exp.ofVal v)) σ' Q)) : wp (K e) σ Q := by
  -- Coinduct on: "already wp, or of the form `K e` with `e` running toward the
  -- continuation". The left disjunct lets the invariant absorb `wp`.
  refine wp_coind
    (fun a σ Q => wp a σ Q ∨
      ∃ e, a = K e ∧ wp e σ (fun v σ' => wp (K (Exp.ofVal v)) σ' Q))
    (fun a σ Q hI => ?_) (K e) σ Q (.inr ⟨e, rfl, hwp⟩)
  rcases hI with hwp | ⟨e, rfl, hwp⟩
  · -- already `wp a σ Q`: unfold and weaken each recursive position into the invariant
    rw [wp_unfold_apply] at hwp
    rcases hwp with hv | ⟨hred, hstep⟩
    · exact .inl hv
    · exact .inr ⟨hred, fun κ e' σ' efs hs =>
        (hstep κ e' σ' efs hs).imp id (.inl ·)⟩
  · -- `a = K e`: case on whether the focus `e` is already a value
    rw [wp_unfold_apply] at hwp
    rcases hwp with ⟨v, hv, hcont⟩ | ⟨hred, hstep⟩
    · -- focus is `ofVal v`: `K e = K (ofVal v)`, continue with `wp (K (ofVal v))`
      have : e = Exp.ofVal v := (ToVal.coe_of_toVal_eq_some hv).symm
      subst this
      -- `hcont : wp (K (ofVal v)) σ Q`; fold into the invariant via the left disjunct
      rw [wp_unfold_apply] at hcont
      exact hcont.imp id (fun ⟨hr, hs⟩ => ⟨hr, fun κ e' σ' efs hst =>
        (hs κ e' σ' efs hst).imp id (.inl ·)⟩)
    · -- focus reduces: `K e` is reducible, and successors stay in the invariant
      have hKred : Reducible (K e, σ) :=
        let ⟨obs, e', σ', eₜ, hst⟩ := hred
        ⟨obs, K e', σ', eₜ, Language.Context.primStep_fill hst⟩
      refine .inr ⟨hKred, fun κ Ke' σ' efs hs => ?_⟩
      have hnv : ToVal.toVal e = none := toVal_none_of_reducible hred
      obtain ⟨e', rfl, hes⟩ := Language.Context.primStep_fill_inv hnv hs
      obtain ⟨hnil, hwp'⟩ := hstep κ e' σ' efs hes
      exact ⟨hnil, .inr ⟨e', rfl, hwp'⟩⟩

/-- HeapLang specialization: bind over an evaluation context `fill K`. -/
theorem wp_bind_fill (K : List ECtxItem) {e σ Q}
    (hwp : wp e σ (fun v σ' => wp (ProgramLogic.fill K (Exp.ofVal v)) σ' Q)) :
    wp (ProgramLogic.fill K e) σ Q :=
  wp_bind (K := ProgramLogic.fill K) hwp

/-! ## Lifting base steps to `wp`

Generic backward rule: to prove `wp e σ Q` it suffices that `e` is reducible and
every (fork-free) successor is already `wp`-safe. Every primitive rule below is
an instance of this with the relevant `BaseStep` inverted. -/

/-- Backward step rule (the right disjunct of `wp_unfold`). -/
theorem wp_lift_step {e σ Q} (hred : Reducible (e, σ))
    (hcont : ∀ κ e' σ' efs, (e, σ) -<κ>-> (e', σ', efs) → efs = [] ∧ wp e' σ' Q) :
    wp e σ Q := by
  rw [wp_unfold_apply]; exact .inr ⟨hred, hcont⟩

open ProgramLogic EctxLanguage in
/-- A `load` of a bound location reduces to the stored value, leaving the state
unchanged. -/
theorem wp_load {l : Loc} {v : Val} {σ Q}
    (hl : σ.get? l = some (some v)) (hQ : Q v σ) :
    wp (.load (.ofVal (.lit (.loc l)))) σ Q := by
  have hbred : BaseStep.Reducible (Exp.load (.ofVal (.lit (.loc l))), σ) :=
    ⟨[], _, _, _, BaseStep.loadS l v σ hl⟩
  refine wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  -- the only base step of `load (loc l)` is `loadS`, giving `(ofVal v, σ, [])`
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with
  | loadS _ v' _ hl' =>
    rw [hl'] at hl; cases hl
    exact ⟨rfl, by rw [wp_unfold_apply]; exact .inl ⟨v, ToVal.toVal_coe v, hQ⟩⟩

open ProgramLogic EctxLanguage in
/-- A `store` to a bound location updates it and returns unit. -/
theorem wp_store {l : Loc} {v w : Val} {σ Q}
    (hl : σ.get? l = some (some v)) (hQ : Q (.lit .unit) (σ.initHeap l 1 (some w))) :
    wp (.store (.ofVal (.lit (.loc l))) (.ofVal w)) σ Q := by
  have hbred : BaseStep.Reducible (Exp.store (.ofVal (.lit (.loc l))) (.ofVal w), σ) :=
    ⟨[], _, _, _, BaseStep.storeS l v w σ hl⟩
  refine wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with
  | storeS _ v' _ _ hl' =>
    exact ⟨rfl, by rw [wp_unfold_apply]
                   exact .inl ⟨.lit .unit, ToVal.toVal_coe _, hQ⟩⟩

open ProgramLogic EctxLanguage in
/-- `if #true then e₁ else e₂` reduces to `e₁`. -/
theorem wp_if_true {e₁ e₂ σ Q} (hQ : wp e₁ σ Q) :
    wp (.if (.ofVal (.lit (.bool true))) e₁ e₂) σ Q := by
  have hbred : BaseStep.Reducible (Exp.if (.ofVal (.lit (.bool true))) e₁ e₂, σ) :=
    ⟨[], _, _, _, BaseStep.ifTrueS e₁ e₂ σ⟩
  refine wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with | ifTrueS => exact ⟨rfl, hQ⟩

open ProgramLogic EctxLanguage in
/-- `if #false then e₁ else e₂` reduces to `e₂`. -/
theorem wp_if_false {e₁ e₂ σ Q} (hQ : wp e₂ σ Q) :
    wp (.if (.ofVal (.lit (.bool false))) e₁ e₂) σ Q := by
  have hbred : BaseStep.Reducible (Exp.if (.ofVal (.lit (.bool false))) e₁ e₂, σ) :=
    ⟨[], _, _, _, BaseStep.ifFalseS e₁ e₂ σ⟩
  refine wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with | ifFalseS => exact ⟨rfl, hQ⟩

open ProgramLogic EctxLanguage in
/-- `free` of a bound location deallocates it and returns unit. -/
theorem wp_free {l : Loc} {v : Val} {σ Q}
    (hl : σ.get? l = some (some v)) (hQ : Q (.lit .unit) (σ.initHeap l 1 none)) :
    wp (.free (.ofVal (.lit (.loc l)))) σ Q := by
  have hbred : BaseStep.Reducible (Exp.free (.ofVal (.lit (.loc l))), σ) :=
    ⟨[], _, _, _, BaseStep.freeS l v σ hl⟩
  refine wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with
  | freeS _ _ _ _ =>
    exact ⟨rfl, by rw [wp_unfold_apply]; exact .inl ⟨.lit .unit, ToVal.toVal_coe _, hQ⟩⟩

open ProgramLogic EctxLanguage in
/-- Atomic exchange `xchg l v2`: returns the old value, stores `v2`. -/
theorem wp_xchg {l : Loc} {v1 v2 : Val} {σ Q}
    (hl : σ.get? l = some (some v1)) (hQ : Q v1 (σ.initHeap l 1 (some v2))) :
    wp (.xchg (.ofVal (.lit (.loc l))) (.ofVal v2)) σ Q := by
  have hbred : BaseStep.Reducible (Exp.xchg (.ofVal (.lit (.loc l))) (.ofVal v2), σ) :=
    ⟨[], _, _, _, BaseStep.xchgS l v1 v2 σ hl⟩
  refine wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with
  | xchgS _ v1' _ _ hl' =>
    rw [hl'] at hl; cases hl
    exact ⟨rfl, by rw [wp_unfold_apply]; exact .inl ⟨v1, ToVal.toVal_coe _, hQ⟩⟩

open ProgramLogic EctxLanguage in
/-- Compare-and-exchange. The stored value `vl` must be comparable to `v1`; the
boolean result `b = (vl == v1)` decides whether the store happens. The
continuation must cover both outcomes. -/
theorem wp_cmpXchg {l : Loc} {v1 v2 vl : Val} {σ Q}
    (hl : σ.get? l = some (some vl)) (hcmp : vl.compareSafe v1)
    (hQ : ∀ b : Bool, decide (vl = v1) = b →
      Q (.pair vl (.lit (.bool b))) (if b then σ.initHeap l 1 (some v2) else σ)) :
    wp (.cmpXchg (.ofVal (.lit (.loc l))) (.ofVal v1) (.ofVal v2)) σ Q := by
  have hbred : BaseStep.Reducible
      (Exp.cmpXchg (.ofVal (.lit (.loc l))) (.ofVal v1) (.ofVal v2), σ) :=
    ⟨[], _, _, _, BaseStep.cmpXchgS l v1 v2 vl σ _ hl hcmp rfl⟩
  refine wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with
  | cmpXchgS _ _ _ vl' _ b hl' _ hb =>
    rw [hl'] at hl; cases hl
    exact ⟨rfl, by rw [wp_unfold_apply]
                   exact .inl ⟨_, ToVal.toVal_coe _, hQ b hb⟩⟩

open ProgramLogic EctxLanguage in
/-- Fetch-and-add: atomically adds `i2` to the integer stored at `l`, returning
the old value. -/
theorem wp_faa {l : Loc} {i1 i2 : Int} {σ Q}
    (hl : σ.get? l = some (some (.lit (.int i1))))
    (hQ : Q (.lit (.int i1)) (σ.initHeap l 1 (some (.lit (.int (i1 + i2)))))) :
    wp (.faa (.ofVal (.lit (.loc l))) (.ofVal (.lit (.int i2)))) σ Q := by
  have hbred : BaseStep.Reducible
      (Exp.faa (.ofVal (.lit (.loc l))) (.ofVal (.lit (.int i2))), σ) :=
    ⟨[], _, _, _, BaseStep.faaS l i1 i2 σ hl⟩
  refine wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with
  | faaS _ i1' _ _ hl' =>
    rw [hl'] at hl; cases hl
    exact ⟨rfl, by rw [wp_unfold_apply]; exact .inl ⟨_, ToVal.toVal_coe _, hQ⟩⟩

open Std Iris.Std FromMathlib in
/-- Heap finiteness + `Loc` infinitude: every state has a location absent from
the heap. (Single cell; matches the freshness used by Iris's `wp_alloc`.) -/
theorem State.exists_fresh (σ : State) : ∃ l : Loc, σ.get? l = none := by
  refine ⟨(List.fresh σ.heap.keys).choose, ?_⟩
  have h := (List.fresh σ.heap.keys).choose_spec
  show σ.heap[_]? = none
  exact Std.ExtTreeMap.getElem?_eq_none (fun hm => h (Std.ExtTreeMap.mem_keys.mpr hm))

open ProgramLogic EctxLanguage in
/-- `allocN n v` with `0 < n` allocates a fresh array. Allocation is
nondeterministic in the base location, so the continuation must hold for **every**
valid fresh `l`; the `hfresh` premise witnesses that at least one exists (needed
for reducibility — discharge it from heap finiteness at the call site). -/
theorem wp_allocN {n : Int} {v : Val} {σ Q} (hn : 0 < n)
    (hfresh : ∃ l : Loc, ∀ i : Int, 0 ≤ i → i < n → σ.get? (l + i) = none)
    (hQ : ∀ l : Loc, (∀ i : Int, 0 ≤ i → i < n → σ.get? (l + i) = none) →
      Q (.lit (.loc l)) (σ.initHeap l n v)) :
    wp (.allocN (.ofVal (.lit (.int n))) (.ofVal v)) σ Q := by
  obtain ⟨l₀, hl₀⟩ := hfresh
  have hbred : BaseStep.Reducible (Exp.allocN (.ofVal (.lit (.int n))) (.ofVal v), σ) :=
    ⟨[], _, _, _, BaseStep.allocNS n v σ l₀ hn hl₀⟩
  refine wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with
  | allocNS _ _ _ l _ hfr =>
    exact ⟨rfl, by rw [wp_unfold_apply]
                   exact .inl ⟨.lit (.loc l), ToVal.toVal_coe _, hQ l hfr⟩⟩

/-- Single-cell allocation `ref v` (= `allocN 1 v`): premise-free, since a fresh
location always exists. The result location is universally quantified. -/
theorem wp_alloc {v : Val} {σ Q}
    (hQ : ∀ l : Loc, σ.get? l = none → Q (.lit (.loc l)) (σ.initHeap l 1 v)) :
    wp (.allocN (.ofVal (.lit (.int 1))) (.ofVal v)) σ Q := by
  have hl0 : ∀ l : Loc, l + (0 : Int) = l := fun l => by ext; simp
  refine wp_allocN (by decide) ?_ (fun l hfr => hQ l ?_)
  · obtain ⟨l, hl⟩ := σ.exists_fresh
    exact ⟨l, fun i _ h1 => by rw [show i = 0 by omega, hl0]; exact hl⟩
  · rw [← hl0 l]; exact hfr 0 (by decide) (by decide)

open ProgramLogic EctxLanguage in
/-- β-reduction: applying a recursive closure substitutes both binders. -/
theorem wp_beta {f x : Binder} {e1 : Exp} {v2 : Val} {σ Q}
    (hQ : wp ((e1.subst f (.rec_ f x e1)).subst x v2) σ Q) :
    wp (.app (.ofVal (.rec_ f x e1)) (.ofVal v2)) σ Q := by
  have hbred : BaseStep.Reducible (Exp.app (.ofVal (.rec_ f x e1)) (.ofVal v2), σ) :=
    ⟨[], _, _, _, BaseStep.betaS f x e1 v2 _ σ rfl⟩
  refine wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with | betaS _ _ _ _ _ _ heq => subst heq; exact ⟨rfl, hQ⟩

open ProgramLogic EctxLanguage in
/-- Recursive closures evaluate to themselves as values. -/
theorem wp_rec {f x : Binder} {e : Exp} {σ Q}
    (hQ : Q (.rec_ f x e) σ) : wp (.rec_ f x e) σ Q := by
  have hbred : BaseStep.Reducible (Exp.rec_ f x e, σ) := ⟨[], _, _, _, BaseStep.recS f x e σ⟩
  refine wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with
  | recS _ _ _ _ =>
    exact ⟨rfl, by rw [wp_unfold_apply]; exact .inl ⟨_, ToVal.toVal_coe _, hQ⟩⟩

open ProgramLogic EctxLanguage in
/-- Unary operator evaluation. -/
theorem wp_unop {op : UnOp} {v v' : Val} {σ Q}
    (hop : op.eval v = some v') (hQ : Q v' σ) :
    wp (.unop op (.ofVal v)) σ Q := by
  have hbred : BaseStep.Reducible (Exp.unop op (.ofVal v), σ) :=
    ⟨[], _, _, _, BaseStep.unOpS op v v' σ hop⟩
  refine wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with
  | unOpS _ _ v'' _ hop' =>
    rw [hop'] at hop; cases hop
    exact ⟨rfl, by rw [wp_unfold_apply]; exact .inl ⟨_, ToVal.toVal_coe _, hQ⟩⟩

open ProgramLogic EctxLanguage in
/-- Binary operator evaluation. -/
theorem wp_binop {op : BinOp} {v1 v2 v' : Val} {σ Q}
    (hop : op.eval v1 v2 = some v') (hQ : Q v' σ) :
    wp (.binop op (.ofVal v1) (.ofVal v2)) σ Q := by
  have hbred : BaseStep.Reducible (Exp.binop op (.ofVal v1) (.ofVal v2), σ) :=
    ⟨[], _, _, _, BaseStep.binOpS op v1 v2 v' σ hop⟩
  refine wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with
  | binOpS _ _ _ v'' _ hop' =>
    rw [hop'] at hop; cases hop
    exact ⟨rfl, by rw [wp_unfold_apply]; exact .inl ⟨_, ToVal.toVal_coe _, hQ⟩⟩

open ProgramLogic EctxLanguage in
/-- Pairing two values. -/
theorem wp_pair {v1 v2 : Val} {σ Q} (hQ : Q (.pair v1 v2) σ) :
    wp (.pair (.ofVal v1) (.ofVal v2)) σ Q := by
  have hbred : BaseStep.Reducible (Exp.pair (.ofVal v1) (.ofVal v2), σ) :=
    ⟨[], _, _, _, BaseStep.pairS v1 v2 σ⟩
  refine wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with
  | pairS _ _ _ =>
    exact ⟨rfl, by rw [wp_unfold_apply]; exact .inl ⟨_, ToVal.toVal_coe _, hQ⟩⟩

open ProgramLogic EctxLanguage in
/-- First projection. -/
theorem wp_fst {v1 v2 : Val} {σ Q} (hQ : Q v1 σ) :
    wp (.fst (.ofVal (.pair v1 v2))) σ Q := by
  have hbred : BaseStep.Reducible (Exp.fst (.ofVal (.pair v1 v2)), σ) :=
    ⟨[], _, _, _, BaseStep.fstS v1 v2 σ⟩
  refine wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with
  | fstS _ _ _ =>
    exact ⟨rfl, by rw [wp_unfold_apply]; exact .inl ⟨_, ToVal.toVal_coe _, hQ⟩⟩

open ProgramLogic EctxLanguage in
/-- Second projection. -/
theorem wp_snd {v1 v2 : Val} {σ Q} (hQ : Q v2 σ) :
    wp (.snd (.ofVal (.pair v1 v2))) σ Q := by
  have hbred : BaseStep.Reducible (Exp.snd (.ofVal (.pair v1 v2)), σ) :=
    ⟨[], _, _, _, BaseStep.sndS v1 v2 σ⟩
  refine wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with
  | sndS _ _ _ =>
    exact ⟨rfl, by rw [wp_unfold_apply]; exact .inl ⟨_, ToVal.toVal_coe _, hQ⟩⟩

open ProgramLogic EctxLanguage in
/-- Left injection. -/
theorem wp_injL {v : Val} {σ Q} (hQ : Q (.injL v) σ) :
    wp (.injL (.ofVal v)) σ Q := by
  have hbred : BaseStep.Reducible (Exp.injL (.ofVal v), σ) := ⟨[], _, _, _, BaseStep.injLS v σ⟩
  refine wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with
  | injLS _ _ =>
    exact ⟨rfl, by rw [wp_unfold_apply]; exact .inl ⟨_, ToVal.toVal_coe _, hQ⟩⟩

open ProgramLogic EctxLanguage in
/-- Right injection. -/
theorem wp_injR {v : Val} {σ Q} (hQ : Q (.injR v) σ) :
    wp (.injR (.ofVal v)) σ Q := by
  have hbred : BaseStep.Reducible (Exp.injR (.ofVal v), σ) := ⟨[], _, _, _, BaseStep.injRS v σ⟩
  refine wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with
  | injRS _ _ =>
    exact ⟨rfl, by rw [wp_unfold_apply]; exact .inl ⟨_, ToVal.toVal_coe _, hQ⟩⟩

open ProgramLogic EctxLanguage in
/-- `case` on a left injection takes the left branch (applied to the payload). -/
theorem wp_case_injL {v : Val} {e1 e2 σ Q} (hQ : wp (.app e1 (.ofVal v)) σ Q) :
    wp (.case (.ofVal (.injL v)) e1 e2) σ Q := by
  have hbred : BaseStep.Reducible (Exp.case (.ofVal (.injL v)) e1 e2, σ) :=
    ⟨[], _, _, _, BaseStep.caseLS v e1 e2 σ⟩
  refine wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with | caseLS _ _ _ _ => exact ⟨rfl, hQ⟩

open ProgramLogic EctxLanguage in
/-- `case` on a right injection takes the right branch (applied to the payload). -/
theorem wp_case_injR {v : Val} {e1 e2 σ Q} (hQ : wp (.app e2 (.ofVal v)) σ Q) :
    wp (.case (.ofVal (.injR v)) e1 e2) σ Q := by
  have hbred : BaseStep.Reducible (Exp.case (.ofVal (.injR v)) e1 e2, σ) :=
    ⟨[], _, _, _, BaseStep.caseRS v e1 e2 σ⟩
  refine wp_lift_step (primStep_reducible_of_baseStep_reducible hbred)
    (fun κ e' σ' efs hs => ?_)
  have hb := baseStep_of_primStep_of_baseStep_reducible hbred hs
  cases hb with | caseRS _ _ _ _ => exact ⟨rfl, hQ⟩

/-- The value rule: `wp (ofVal v) σ Q ↔ Q v σ`. -/
@[simp] theorem wp_val {v : Val} {σ Q} : wp (.ofVal v) σ Q ↔ Q v σ := by
  rw [wp_unfold_apply]
  constructor
  · rintro (⟨v', hv', hQ⟩ | ⟨hred, _⟩)
    · rw [ToVal.toVal_coe] at hv'; cases hv'; exact hQ
    · exact absurd (toVal_none_of_reducible hred) (by rw [ToVal.toVal_coe]; simp)
  · exact fun hQ => .inl ⟨v, ToVal.toVal_coe v, hQ⟩

open Lean.Order in
instance instWPPreExp : Std.Internal.Do.WP Exp Val (State → Prop) Std.Internal.Do.EPost.Nil where
  wpTrans e := ⟨fun Q _ σ => wp e σ Q⟩
  wp_trans_monotone e := by
    intro post post' _ _ _ hpost
    exact fun σ h => wp_mono (fun v s => hpost v s) h

end Iris.HeapLang
