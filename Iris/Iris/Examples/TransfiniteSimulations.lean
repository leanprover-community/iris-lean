/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Instances.UPred.Transfinite
public import Iris.ProofMode
public import Iris.Std.FromMathlib
public import Iris.Std.Relation
public import Iris.BI.Lib.Fixpoint

/-! # Simulations in step-indexed logic (Transfinite Iris, key ideas)

This file ports `theories/examples/keyideas/simulations.v` of Transfinite Iris, the running example
of Section 2 of the paper. A simulation `sim t s` between a target and a source transition system
is defined as a guarded fixpoint in the (generic) `UPred` model.

- `sim_is_rpr` (Lemma 2.1): `sim` implies *result* refinement, for every type of step-indices.
- `sim_is_tpr` (Lemma 2.2): `sim` implies *termination-preserving* refinement, provided the type
  of step-indices is large (`SIdxLarge`, e.g. the ordinals). The proof uses the existential
  property `UPred.satisfiable_exists` in each step.
- `sim_to_simFiniteRef`, `simFiniteRef_tpr`: with finite step-indices, `sim` only gives the
  weaker `SimFiniteRef`, which implies termination-preserving refinement if the source has
  finite nondeterminism.

The Rocq development uses `iProp Σ`; the construction only needs a satisfiable step-indexed BI
with guarded fixpoints, so we work in `UPred M` for an arbitrary unital camera `M`. Rocq's
coinductive `ex_loop` is replaced by the existence of an infinite execution (`ExLoop`).
-/

@[expose] public section

namespace Iris.Examples.TransfiniteSimulations
open Iris BI OFE FromMathlib

/-- An infinite execution starting at `x` (Rocq: `ex_loop`). -/
def ExLoop {X : Type _} (R : X → X → Prop) (x : X) : Prop :=
  ∃ f : Nat → X, f 0 = x ∧ ∀ n, R (f n) (f (n + 1))

theorem ExLoop.step {X : Type _} {R : X → X → Prop} {x : X} :
    ExLoop R x → ∃ x', R x x' ∧ ExLoop R x'
  | ⟨f, h0, hf⟩ => ⟨f 1, h0 ▸ hf 0, ⟨fun n => f (n + 1), rfl, fun n => hf (n + 1)⟩⟩

/-- A predicate that can always make a step along `R` gives an infinite execution. -/
theorem ExLoop.of_step {X : Type _} {R : X → X → Prop} (P : X → Prop)
    (hstep : ∀ x, P x → ∃ x', R x x' ∧ P x') {x : X} (hx : P x) : ExLoop R x := by
  let g : Nat → {x // P x} := fun n =>
    n.rec ⟨x, hx⟩ fun _ y => ⟨Classical.choose (hstep y.1 y.2), (Classical.choose_spec (hstep y.1 y.2)).2⟩
  exact ⟨fun n => (g n).1, rfl, fun n => (Classical.choose_spec (hstep (g n).1 (g n).2)).1⟩

section Simulations

variable {SI : Type _} [instSI : SIdx SI]
local stepindex SI

variable {M : Type _} [UCMRA M]
variable {S T V : Type _} (srcStep : S → S → Prop) (tgtStep : T → T → Prop)
  (valSrc : V → S) (valTgt : V → T)

/-- Result refinement (Rocq: `rpr`). -/
def Rpr (t : T) (s : S) : Prop :=
  ∀ v, Relation.ReflTransGen tgtStep t (valTgt v) → Relation.ReflTransGen srcStep s (valSrc v)

/-- Termination-preserving refinement (Rocq: `tpr`). -/
def Tpr (t : T) (s : S) : Prop :=
  Rpr srcStep tgtStep valSrc valTgt t s ∧ (ExLoop tgtStep t → ExLoop srcStep s)

/-- The generating function of the simulation (Rocq: `sim_pre`). -/
def simPre (sim : T → S → UPred M) (t : T) (s : S) : UPred M :=
  iprop((∃ v, ⌜valSrc v = s⌝ ∧ ⌜valTgt v = t⌝) ∨
    (∃ t', ⌜tgtStep t t'⌝) ∧ (∀ t', ⌜tgtStep t t'⌝ → ∃ s', ⌜srcStep s s'⌝ ∧ ▷ sim t' s'))

instance simPre_contractive :
    Contractive (simPre (M := M) srcStep tgtStep valSrc valTgt) where
  distLater_dist h _ _ :=
    or_ne.ne .rfl <| and_ne.ne .rfl <| forall_ne fun t' => imp_ne.ne .rfl <|
      exists_ne fun s' => and_ne.ne .rfl <|
        Contractive.distLater_dist (f := UPred.later) fun m hm => h m hm t' s'

/-- The simulation (Rocq: `sim`). -/
def sim : T → S → UPred M := fixpoint (simPre srcStep tgtStep valSrc valTgt)

theorem sim_unfold (t : T) (s : S) :
    sim (M := M) srcStep tgtStep valSrc valTgt t s =
      simPre srcStep tgtStep valSrc valTgt (sim srcStep tgtStep valSrc valTgt) t s :=
  congrFun (congrFun (fixpoint_unfold
    (simPre (M := M) srcStep tgtStep valSrc valTgt).toContractiveHom) t) s

theorem sim_plain_aux :
    ⊢@{UPred M} ∀ t s, sim srcStep tgtStep valSrc valTgt t s -∗
      ■ sim srcStep tgtStep valSrc valTgt t s := by
  iloeb as IH
  iintro %t %s Hsim
  rw [sim_unfold]; unfold simPre
  icases Hsim with (H | ⟨H1, H2⟩)
  · ileft
    iapply Plain.plain
    iexact H
  · iright
    isplit
    · iapply Plain.plain
      iexact H1
    · iintro %t' %Hstep
      icases H2 $$ %t' %Hstep with ⟨%s', %Hstep', Hsim⟩
      iexists s'
      isplit
      · ipureintro
        exact Hstep'
      · iapply later_plainly.mp
        inext
        iapply IH
        iexact Hsim

instance sim_plain (t : T) (s : S) : Plain (sim (M := M) srcStep tgtStep valSrc valTgt t s) where
  plain := by
    have h := sim_plain_aux (M := M) srcStep tgtStep valSrc valTgt
    iintro Hsim
    iapply h
    iexact Hsim

theorem sim_valid_satisfiable (t : T) (s : S) :
    UPred.satisfiable (sim (M := M) srcStep tgtStep valSrc valTgt t s) ↔
      (⊢@{UPred M} sim srcStep tgtStep valSrc valTgt t s) :=
  ⟨fun h => true_intro.trans (UPred.satisfiable_elim h),
   fun h => UPred.satisfiable_intro (true_intro.trans h)⟩

theorem satisfiable_pure {φ : Prop} (h : UPred.satisfiable (M := M) iprop(⌜φ⌝)) : φ :=
  UPred.pure_soundness (UPred.satisfiable_elim h)

variable {srcStep tgtStep valSrc valTgt}
variable (hvalIrred : ∀ v, ¬ ∃ t', tgtStep (valTgt v) t')

include hvalIrred in
/-- Executing a target step in a satisfiable simulation (Rocq: `sim_execute_tgt_step`). -/
theorem sim_execute_tgt_step [SIdxLarge.{u} SI] {S : Type u} {srcStep : S → S → Prop}
    {valSrc : V → S} {t t' : T} {s : S} (hstep : tgtStep t t')
    (hsat : UPred.satisfiable (sim (M := M) srcStep tgtStep valSrc valTgt t s)) :
    ∃ s', srcStep s s' ∧ UPred.satisfiable (sim (M := M) srcStep tgtStep valSrc valTgt t' s') := by
  have hQ : UPred.satisfiable (M := M)
      iprop(∃ s', ⌜srcStep s s'⌝ ∧ ▷ sim srcStep tgtStep valSrc valTgt t' s') := by
    refine UPred.satisfiable_mono hsat ?_
    rw [sim_unfold]; unfold simPre
    iintro (H | ⟨_, H⟩)
    · icases H with ⟨%v, %_, %hv⟩
      exact absurd ⟨t', hv ▸ hstep⟩ (hvalIrred v)
    · iapply H
      ipureintro
      exact hstep
  obtain ⟨s', hs'⟩ := UPred.satisfiable_exists hQ
  exact ⟨s', satisfiable_pure (UPred.satisfiable_mono hs' and_elim_l),
    UPred.satisfiable_later (UPred.satisfiable_mono hs' and_elim_r)⟩

include hvalIrred in
theorem sim_execute_tgt [SIdxLarge.{u} SI] {S : Type u} {srcStep : S → S → Prop}
    {valSrc : V → S} {t t' : T} (hsteps : Relation.ReflTransGen tgtStep t t') :
    ∀ {s}, UPred.satisfiable (sim (M := M) srcStep tgtStep valSrc valTgt t s) →
      ∃ s', Relation.ReflTransGen srcStep s s' ∧
        UPred.satisfiable (sim (M := M) srcStep tgtStep valSrc valTgt t' s') := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun hsat => ⟨_, .refl, hsat⟩
  | head hstep _ ih =>
    intro s hsat
    obtain ⟨s', hs, hsat'⟩ := sim_execute_tgt_step hvalIrred hstep hsat
    obtain ⟨s'', hs', hsat''⟩ := ih hsat'
    exact ⟨s'', .head hs hs', hsat''⟩

include hvalIrred in
/-- Lemma 2.1 of the paper: a simulation implies result refinement (Rocq: `sim_is_rpr`). -/
theorem sim_is_rpr [SIdxLarge.{u} SI] {S : Type u} {srcStep : S → S → Prop}
    {valSrc : V → S} (hinj : Function.Injective valTgt) {t : T} {s : S}
    (hsim : ⊢@{UPred M} sim srcStep tgtStep valSrc valTgt t s) :
    Rpr srcStep tgtStep valSrc valTgt t s := by
  intro v hsteps
  obtain ⟨s', hs', hsat⟩ := sim_execute_tgt hvalIrred hsteps
    ((sim_valid_satisfiable srcStep tgtStep valSrc valTgt t s).mpr hsim)
  suffices s' = valSrc v from this ▸ hs'
  refine satisfiable_pure (UPred.satisfiable_mono hsat ?_)
  rw [sim_unfold]; unfold simPre
  iintro (H | ⟨H, _⟩)
  · icases H with ⟨%v', %hs, %hv⟩
    ipureintro
    rw [← hs, hinj hv]
  · icases H with ⟨%t', %hstep⟩
    exact absurd ⟨t', hstep⟩ (hvalIrred v)

include hvalIrred in
/-- Lemma 2.2 of the paper: with large step-indices, a simulation implies termination-preserving
refinement (Rocq: `sim_is_tpr`). -/
theorem sim_is_tpr [SIdxLarge.{u} SI] {S : Type u} {srcStep : S → S → Prop}
    {valSrc : V → S} (hinj : Function.Injective valTgt) {t : T} {s : S}
    (hsim : ⊢@{UPred M} sim srcStep tgtStep valSrc valTgt t s) :
    Tpr srcStep tgtStep valSrc valTgt t s := by
  refine ⟨sim_is_rpr hvalIrred hinj hsim, fun hloop => ?_⟩
  refine ExLoop.of_step (fun s => ∃ t, ExLoop tgtStep t ∧
    UPred.satisfiable (sim (M := M) srcStep tgtStep valSrc valTgt t s)) ?_
    ⟨t, hloop, (sim_valid_satisfiable srcStep tgtStep valSrc valTgt t s).mpr hsim⟩
  rintro s ⟨t, hloop, hsat⟩
  obtain ⟨t', hstep, hloop'⟩ := hloop.step
  obtain ⟨s', hs, hsat'⟩ := sim_execute_tgt_step hvalIrred hstep hsat
  exact ⟨s', hs, t', hloop', hsat'⟩

end Simulations

/-! ## Simulations with finite step-indices

With finite step-indices, a simulation only gives `SimFiniteRef`: every target execution of length
`n` is matched by a source execution of length at least `n` (Rocq: `sim_finite_ref`). This implies
termination-preserving refinement only if the source has finite nondeterminism. -/

section FiniteSimulations

theorem Iterate.head_inv {X : Type _} {R : X → X → Prop} {n : Nat} {x z : X}
    (h : Relation.Iterate R (n + 1) x z) : ∃ y, R x y ∧ Relation.Iterate R n y z := by
  suffices ∀ k, ∀ {a} (h : Relation.Iterate R k a z), ∀ n, k = n + 1 →
      ∃ y, R a y ∧ Relation.Iterate R n y z from this _ h n rfl
  intro k a h
  induction h using Relation.Iterate.head_induction_on with
  | rfl => intro n h; cases h
  | head c h' h _ => intro n hn; cases hn; exact ⟨c, h', h⟩

theorem ExLoop.iterate {X : Type _} {R : X → X → Prop} {f : Nat → X}
    (hf : ∀ n, R (f n) (f (n + 1))) : ∀ n, Relation.Iterate R n (f 0) (f n)
  | 0 => .rfl _
  | n + 1 => .tail _ (ExLoop.iterate hf n) (hf n)

/-- Rocq: `ex_loop_sn`. -/
theorem exLoop_iff_not_sn {X : Type _} (R : X → X → Prop) (x : X) :
    ExLoop R x ↔ ¬ Relation.StronglyNormalizing R x := by
  constructor
  · rintro ⟨f, rfl, hf⟩ hsn
    suffices ∀ y, Relation.StronglyNormalizing R y → ∀ n, y ≠ f n from this _ hsn 0 rfl
    intro y hy
    induction hy with
    | intro y _ ih => intro n hn; subst hn; exact ih _ (hf n) (n + 1) rfl
  · refine ExLoop.of_step (fun x => ¬ Relation.StronglyNormalizing R x) fun x hx => ?_
    refine Classical.byContradiction fun h => hx ⟨x, fun y hy => ?_⟩
    exact Classical.byContradiction fun hy' => h ⟨y, hy, hy'⟩

/-- Rocq: `sn_finite_nondet_bounded`. -/
theorem sn_finite_nondet_bounded {X : Type _} (R : X → X → Prop) {x : X}
    (hfin : ∀ x, ∃ l : List X, ∀ x', R x x' ↔ x' ∈ l) (hsn : Relation.StronglyNormalizing R x) :
    ∃ n, ∀ x' m, Relation.Iterate R m x x' → m < n := by
  induction hsn with
  | intro x _ ih =>
    obtain ⟨l, hl⟩ := hfin x
    have key : ∀ y ∈ l, ∃ N, ∀ x' m, Relation.Iterate R m y x' → m < N :=
      fun y hy => ih y ((hl y).mpr hy)
    obtain ⟨N, hN⟩ : ∃ N, ∀ y ∈ l, ∀ x' m, Relation.Iterate R m y x' → m < N := by
      clear hl
      induction l with
      | nil => exact ⟨0, fun _ h => by cases h⟩
      | cons y l ihl =>
        obtain ⟨N1, h1⟩ := key y (.head _)
        obtain ⟨N2, h2⟩ := ihl fun z hz => key z (.tail _ hz)
        refine ⟨max N1 N2, fun z hz x' m hm => ?_⟩
        rcases List.mem_cons.mp hz with rfl | hz
        · exact Nat.lt_of_lt_of_le (h1 x' m hm) (Nat.le_max_left _ _)
        · exact Nat.lt_of_lt_of_le (h2 z hz x' m hm) (Nat.le_max_right _ _)
    refine ⟨N + 1, fun x' m hm => ?_⟩
    cases m with
    | zero => omega
    | succ m =>
      obtain ⟨y, hy, hm'⟩ := Iterate.head_inv hm
      exact Nat.succ_lt_succ (hN y ((hl y).mp hy) x' m hm')

/-- Rocq: `finite_nondet_ex_loop_diverge`. -/
theorem finite_nondet_exLoop_diverge {X : Type _} (R : X → X → Prop) {x : X}
    (hfin : ∀ x, ∃ l : List X, ∀ x', R x x' ↔ x' ∈ l)
    (hsteps : ∀ n, ∃ m, n ≤ m ∧ ∃ x', Relation.Iterate R m x x') : ExLoop R x := by
  refine (exLoop_iff_not_sn R x).mpr fun hsn => ?_
  obtain ⟨N, hN⟩ := sn_finite_nondet_bounded R hfin hsn
  obtain ⟨m, hle, x', hm⟩ := hsteps N
  exact absurd (hN x' m hm) (by omega)

/-- Rocq: `ex_loop_extract_finite_execution`. -/
theorem exLoop_extract_finite_execution {X : Type _} {R : X → X → Prop} {x : X} (n : Nat) :
    ExLoop R x → ∃ x', Relation.Iterate R n x x'
  | ⟨f, h0, hf⟩ => ⟨f n, h0 ▸ ExLoop.iterate hf n⟩

variable {SI : Type _} [instSI : SIdx SI]
local stepindex SI

variable {M : Type _} [UCMRA M]
variable {S T V : Type _} {srcStep : S → S → Prop} {tgtStep : T → T → Prop}
  {valSrc : V → S} {valTgt : V → T}

/-- Finite refinement (Rocq: `sim_finite_ref`). -/
def SimFiniteRef (srcStep : S → S → Prop) (tgtStep : T → T → Prop) (valSrc : V → S)
    (valTgt : V → T) (t : T) (s : S) : Prop :=
  ∀ n t', Relation.Iterate tgtStep n t t' →
    ∃ m s', Relation.Iterate srcStep m s s' ∧ n ≤ m ∧ ∀ v, valTgt v = t' → valSrc v = s'

theorem satisfiable_laterN {P : UPred M} :
    ∀ n, UPred.satisfiable iprop(▷^[n] P) → UPred.satisfiable P
  | 0, h => h
  | n + 1, h => satisfiable_laterN n (UPred.satisfiable_later h)

theorem sim_laterN_finite_ref (hvalIrred : ∀ v, ¬ ∃ t', tgtStep (valTgt v) t')
    (hinj : Function.Injective valTgt) {t' : T} :
    ∀ {n t}, Relation.Iterate tgtStep n t t' → ∀ s,
      sim (M := M) srcStep tgtStep valSrc valTgt t s ⊢
        ▷^[n] ⌜∃ m s', Relation.Iterate srcStep m s s' ∧ n ≤ m ∧
          ∀ v, valTgt v = t' → valSrc v = s'⌝ := by
  intro n t hsteps
  induction hsteps using Relation.Iterate.head_induction_on with
  | rfl =>
    intro s
    rw [sim_unfold]; unfold simPre
    iintro (H | ⟨H, _⟩)
    · icases H with ⟨%v', %hs, %hv⟩
      ipureintro
      exact ⟨0, s, .rfl _, Nat.le_refl _, fun v hv' => hs ▸ congrArg valSrc (hinj (hv'.trans hv.symm))⟩
    · icases H with ⟨%t'', %hstep⟩
      ipureintro
      exact ⟨0, s, .rfl _, Nat.le_refl _, fun v hv => absurd ⟨t'', hv ▸ hstep⟩ (hvalIrred v)⟩
  | @head n _ c hstep _ ih =>
    intro s
    rw [sim_unfold]; unfold simPre
    iintro (H | ⟨_, H⟩)
    · icases H with ⟨%v, %_, %hv⟩
      exact absurd ⟨c, hv ▸ hstep⟩ (hvalIrred v)
    · icases H $$ %c %hstep with ⟨%s', %hs', Hsim⟩
      have H : iprop(▷ sim srcStep tgtStep valSrc valTgt c s') ⊢
          ▷^[n + 1] ⌜∃ m s'', Relation.Iterate srcStep m s s'' ∧ n + 1 ≤ m ∧
            ∀ v, valTgt v = t' → valSrc v = s''⌝ :=
        later_mono <| (ih s').trans <| laterN_mono n <| pure_mono fun ⟨m, s'', hit, hle, hv⟩ =>
          ⟨m + 1, s'', hit.head hs', Nat.succ_le_succ hle, hv⟩
      iapply H
      iexact Hsim

/-- A simulation implies finite refinement (Rocq: `sim_to_sim_finite_ref`). This holds for every
type of step-indices; it is the best one can get for finite step-indices. -/
@[rocq_alias sim_to_sim_finite_ref]
theorem sim_to_simFiniteRef (hvalIrred : ∀ v, ¬ ∃ t', tgtStep (valTgt v) t')
    (hinj : Function.Injective valTgt) {t : T} {s : S}
    (hsim : ⊢@{UPred M} sim srcStep tgtStep valSrc valTgt t s) :
    SimFiniteRef srcStep tgtStep valSrc valTgt t s := fun n _ hsteps =>
  satisfiable_pure <| satisfiable_laterN n <|
    UPred.satisfiable_mono ((sim_valid_satisfiable srcStep tgtStep valSrc valTgt t s).mpr hsim)
      (sim_laterN_finite_ref hvalIrred hinj hsteps s)

/-- Finite refinement implies termination-preserving refinement if the source has finite
nondeterminism (Rocq: `sim_finite_ref_tpr`). -/
@[rocq_alias sim_finite_ref_tpr]
theorem simFiniteRef_tpr (hfin : ∀ s, ∃ l : List S, ∀ s', srcStep s s' ↔ s' ∈ l) {t : T} {s : S}
    (href : SimFiniteRef srcStep tgtStep valSrc valTgt t s) :
    Tpr srcStep tgtStep valSrc valTgt t s := by
  refine ⟨fun v hsteps => ?_, fun hloop => ?_⟩
  · obtain ⟨n, hn⟩ := Relation.ReflTrans_iff_exists_iterate.mp hsteps
    obtain ⟨m, s', hm, _, hv⟩ := href n _ hn
    exact Relation.ReflTrans_iff_exists_iterate.mpr ⟨m, hv v rfl ▸ hm⟩
  · refine finite_nondet_exLoop_diverge srcStep hfin fun n => ?_
    obtain ⟨t', ht'⟩ := exLoop_extract_finite_execution n hloop
    obtain ⟨m, s', hm, hle, _⟩ := href n t' ht'
    exact ⟨m, hle, s', hm⟩

end FiniteSimulations

/-! ## Generalized simulations

This section ports `theories/examples/keyideas/generalized_simulations.v`: the simulation is a
*least* fixpoint that may take target steps without matching source steps (finite stuttering), and
relates target values to source states by an arbitrary relation `φ`. -/

section GeneralizedSimulations

variable {SI : Type _} [instSI : SIdx SI]
local stepindex SI

variable {M : Type _} [UCMRA M]
variable {V : Type _} {S T : Type u} (srcStep : S → S → Prop) (tgtStep : T → T → Prop)
  (valTgt : V → T) (φ : V → S → Prop)

/-- Generalized termination-preserving refinement (Rocq: `gtpr`). -/
def Gtpr (t : T) (s : S) : Prop :=
  (∀ v, Relation.ReflTransGen tgtStep t (valTgt v) →
    ∃ s', Relation.ReflTransGen srcStep s s' ∧ φ v s') ∧
  (ExLoop tgtStep t → ExLoop srcStep s)

set_option synthInstance.checkSynthOrder false in
local instance : OFE (T × S) := OFE.ofDiscrete _

/-- The generating function of the generalized simulation (Rocq: `gsim_pre`). -/
abbrev gsimPre (sim : T × S → UPred M) (p : T × S) : UPred M :=
  iprop((∃ v, ⌜φ v p.2⌝ ∧ ⌜valTgt v = p.1⌝) ∨
    (∃ t', ⌜tgtStep p.1 t'⌝) ∧
    (∀ t', ⌜tgtStep p.1 t'⌝ → sim (t', p.2) ∨ ∃ s', ⌜srcStep p.2 s'⌝ ∧ ▷ sim (t', s')))

instance gsimPre_mono : BIMonoPred (gsimPre (M := M) srcStep tgtStep valTgt φ) where
  mono_pred {Φ Ψ} _ _ := by
    iintro #H %p Hp
    unfold gsimPre
    icases Hp with (H1 | ⟨H1, H2⟩)
    · ileft
      iexact H1
    · iright
      isplit
      · iexact H1
      · iintro %t' %ht
        icases H2 $$ %t' %ht with (H3 | ⟨%s', %hs, H3⟩)
        · ileft
          iapply H
          iexact H3
        · iright
          iexists s'
          isplit
          · ipureintro
            exact hs
          · inext
            iapply H
            iexact H3
  mono_pred_ne := ⟨fun _ _ _ h => by cases (h : _ = _); exact .rfl⟩

/-- The generalized simulation (Rocq: `gsim`). -/
abbrev gsim : T × S → UPred M := bi_least_fixpoint (gsimPre srcStep tgtStep valTgt φ)

theorem gsim_unfold (p : T × S) :
    gsim (M := M) srcStep tgtStep valTgt φ p =
      gsimPre srcStep tgtStep valTgt φ (gsim srcStep tgtStep valTgt φ) p :=
  least_fixpoint_unfold _

variable {srcStep tgtStep valTgt φ}
variable (hvalIrred : ∀ v, ¬ ∃ t', tgtStep (valTgt v) t')

include hvalIrred in
/-- Rocq: `gsim_execute_tgt_step`. -/
theorem gsim_execute_tgt_step [SIdxLarge.{u} SI] {t t' : T} {s : S} (hstep : tgtStep t t')
    (hsat : UPred.satisfiable (gsim (M := M) srcStep tgtStep valTgt φ (t, s))) :
    ∃ s', Relation.ReflTransGen srcStep s s' ∧
      UPred.satisfiable (gsim (M := M) srcStep tgtStep valTgt φ (t', s')) := by
  have hQ : UPred.satisfiable (M := M)
      iprop(∃ s', ⌜Relation.ReflTransGen srcStep s s'⌝ ∧
        ▷ gsim srcStep tgtStep valTgt φ (t', s')) := by
    refine UPred.satisfiable_mono hsat ?_
    rw [gsim_unfold]; unfold gsimPre
    iintro (H | ⟨_, H⟩)
    · icases H with ⟨%v, %_, %hv⟩
      exact absurd ⟨t', hv ▸ hstep⟩ (hvalIrred v)
    · icases H $$ %t' %hstep with (H | ⟨%s', %hs, H⟩)
      · iexists s
        isplit
        · ipureintro
          exact .refl
        · inext
          iexact H
      · iexists s'
        isplit
        · ipureintro
          exact .single hs
        · iexact H
  obtain ⟨s', hs'⟩ := UPred.satisfiable_exists hQ
  exact ⟨s', satisfiable_pure (UPred.satisfiable_mono hs' and_elim_l),
    UPred.satisfiable_later (UPred.satisfiable_mono hs' and_elim_r)⟩

include hvalIrred in
theorem gsim_execute_tgt [SIdxLarge.{u} SI] {t t' : T}
    (hsteps : Relation.ReflTransGen tgtStep t t') :
    ∀ {s}, UPred.satisfiable (gsim (M := M) srcStep tgtStep valTgt φ (t, s)) →
      ∃ s', Relation.ReflTransGen srcStep s s' ∧
        UPred.satisfiable (gsim (M := M) srcStep tgtStep valTgt φ (t', s')) := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun hsat => ⟨_, .refl, hsat⟩
  | head hstep _ ih =>
    intro s hsat
    obtain ⟨s', hs, hsat'⟩ := gsim_execute_tgt_step hvalIrred hstep hsat
    obtain ⟨s'', hs', hsat''⟩ := ih hsat'
    exact ⟨s'', hs.trans hs', hsat''⟩

include hvalIrred in
/-- Along an infinite target execution, a generalized simulation eventually takes a source step
(Rocq: `sim_execute_tgt_step`, the termination-preserving version). The finite stuttering is
handled by the induction principle of the least fixpoint. -/
theorem gsim_execute_loop_step [SIdxLarge.{u} SI] {t : T} {s : S} (hloop : ExLoop tgtStep t)
    (hsat : UPred.satisfiable (gsim (M := M) srcStep tgtStep valTgt φ (t, s))) :
    ∃ t' s', srcStep s s' ∧ ExLoop tgtStep t' ∧
      UPred.satisfiable (gsim (M := M) srcStep tgtStep valTgt φ (t', s')) := by
  let Φ : T × S → UPred M := fun p => iprop(⌜ExLoop tgtStep p.1⌝ → ∃ t' s', ⌜srcStep p.2 s'⌝ ∧
    ⌜ExLoop tgtStep t'⌝ ∧ ▷ gsim srcStep tgtStep valTgt φ (t', s'))
  have : NonExpansive Φ := ⟨fun _ _ _ h => by cases (h : _ = _); exact .rfl⟩
  have hind : gsim (M := M) srcStep tgtStep valTgt φ (t, s) ⊢ Φ (t, s) := by
    have h := least_fixpoint_ind (gsimPre (M := M) srcStep tgtStep valTgt φ) Φ
    iintro Hsim
    iapply h $$ [] %(t, s) Hsim
    iintro !> %p Hp %hloop
    icases Hp with (H | ⟨_, H⟩)
    · icases H with ⟨%v, %_, %hv⟩
      obtain ⟨t', hstep, _⟩ := hloop.step
      exact absurd ⟨t', hv ▸ hstep⟩ (hvalIrred v)
    · obtain ⟨t', hstep, hloop'⟩ := hloop.step
      icases H $$ %t' %hstep with (⟨H, -⟩ | ⟨%s', %hs, H⟩)
      · iapply H
        ipureintro
        exact hloop'
      · iexists t', s'
        isplit
        · ipureintro
          exact hs
        · isplit
          · ipureintro
            exact hloop'
          · inext
            icases H with ⟨-, H⟩
            iexact H
  have himp : Φ (t, s) ⊢ iprop(∃ t' s', ⌜srcStep s s'⌝ ∧ ⌜ExLoop tgtStep t'⌝ ∧
      ▷ gsim srcStep tgtStep valTgt φ (t', s')) :=
    (and_intro (true_intro.trans (pure_intro hloop)) .rfl).trans imp_elim_right
  have hQ := UPred.satisfiable_mono hsat (hind.trans himp)
  obtain ⟨t', hQ⟩ := UPred.satisfiable_exists hQ
  obtain ⟨s', hQ⟩ := UPred.satisfiable_exists hQ
  exact ⟨t', s', satisfiable_pure (UPred.satisfiable_mono hQ and_elim_l),
    satisfiable_pure (UPred.satisfiable_mono hQ (and_elim_r.trans and_elim_l)),
    UPred.satisfiable_later (UPred.satisfiable_mono hQ (and_elim_r.trans and_elim_r))⟩

include hvalIrred in
/-- Rocq: `sim_divergence`. -/
theorem gsim_divergence [SIdxLarge.{u} SI] {t : T} {s : S} (hloop : ExLoop tgtStep t)
    (hsat : UPred.satisfiable (gsim (M := M) srcStep tgtStep valTgt φ (t, s))) :
    ExLoop srcStep s := by
  refine ExLoop.of_step (fun s => ∃ t, ExLoop tgtStep t ∧
    UPred.satisfiable (gsim (M := M) srcStep tgtStep valTgt φ (t, s))) ?_ ⟨t, hloop, hsat⟩
  rintro s ⟨t, hloop, hsat⟩
  obtain ⟨t', s', hs, hloop', hsat'⟩ := gsim_execute_loop_step hvalIrred hloop hsat
  exact ⟨s', hs, t', hloop', hsat'⟩

include hvalIrred in
/-- A generalized simulation implies generalized termination-preserving refinement (Rocq:
`sim_is_tpr` in `generalized_simulations.v`). -/
theorem gsim_is_gtpr [SIdxLarge.{u} SI] (hinj : Function.Injective valTgt) {t : T} {s : S}
    (hsim : ⊢@{UPred M} gsim srcStep tgtStep valTgt φ (t, s)) :
    Gtpr srcStep tgtStep valTgt φ t s := by
  have hsat := UPred.satisfiable_intro (true_intro.trans hsim)
  refine ⟨fun v hsteps => ?_, fun hloop => gsim_divergence hvalIrred hloop hsat⟩
  obtain ⟨s', hs', hsat'⟩ := gsim_execute_tgt hvalIrred hsteps hsat
  refine ⟨s', hs', satisfiable_pure (UPred.satisfiable_mono hsat' ?_)⟩
  rw [gsim_unfold]; unfold gsimPre
  iintro (H | ⟨H, _⟩)
  · icases H with ⟨%v', %hφ, %hv⟩
    ipureintro
    exact hinj hv ▸ hφ
  · icases H with ⟨%t', %hstep⟩
    exact absurd ⟨t', hstep⟩ (hvalIrred v)

end GeneralizedSimulations

end Iris.Examples.TransfiniteSimulations
