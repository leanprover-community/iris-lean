/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Iris

/-! # `CondExpMap`: a non-extensional `PartialMap` observed through a conditional expectation

This file defines a `LawfulPartialMap` instance in which every key stores a **random variable**
— a function `f : Ω → V` on a fixed probability space `Ω` — and the observation `get?` reads it
back only through the **conditional expectation** `μ[f | m']` of `f` onto a fixed sub-σ-algebra
`m' ≤ m₀`, collapsed to an `Option V`.  This is the genuine measure-theoretic incarnation of the
"coarsening = projection onto a sub-σ-algebra" pattern (cf. `CoarseningMap.lean`, which used a
finite ℕ-partition): the conditional expectation is the orthogonal projection of `f` onto the
space of `m'`-measurable functions on `L²(μ)`, and two random variables with the same conditional
expectation (i.e. differing by an `m'`-conditionally-centered, mean-zero perturbation) are
**indistinguishable** to `get?`.

## Semantics: conditional expectation onto a sub-σ-algebra

Fix once and for all:

* the probability space `Ω := Bool` with its standard (discrete, `⊤`) σ-algebra `m₀`;
* the probability measure `μ := Measure.dirac true` (mass `1` at `true`, mass `0` at `false`);
* the sub-σ-algebra `m' := (⊥ : MeasurableSpace Bool)`, the *trivial information* `{∅, Ω}`.

Conditioning a random variable `f : Ω → ℝ` onto the trivial σ-algebra `⊥` returns the constant
random variable equal to its mean:

  `μ[f | ⊥]  =  fun _ ↦ ∫ ω, f ω ∂μ  =  fun _ ↦ f true`         (`condExp_bot`, `integral_dirac`).

So the conditional expectation `μ[f | ⊥]` *forgets everything about `f` except its `μ`-mean*,
which for `μ = dirac true` is exactly `f true`; the value `f false` is on a `μ`-null set and is
**invisible** to the conditional expectation.  This is the projection that `get?` exposes:

  `get? m k = some v`   iff   `μ[(stored fᵤ) | ⊥]` is a.e.-constant equal to `v`
                        iff   `(stored f) =ᵐ[μ] (fun _ ↦ v)`.

Because `μ = dirac true`, "a.e.-equal to the constant `v`" means precisely `f true = v`; two random
variables agreeing at `true` but differing at `false` have the *same* conditional expectation and
hence the *same* observation.  The forgetfulness does real work: it is the lookup map of a genuine
projection onto `L²(m', μ)`, not a discarded product factor — the stored payload `Ω → V` is strictly
richer than `Option V`.

## Why this is `get?`-polymorphic yet authentically `condExp`

`condExp` requires `[NormedAddCommGroup V] [NormedSpace ℝ V]`, but the `PartialMap` interface
quantifies `get?` over **all** value types `V`.  We therefore phrase the *polymorphic* observation
through almost-everywhere equality to a constant (`aeValue`, well-defined for every `V` because
`μ.ae = pure true` is `NeBot`), and prove, in the `ℝ`-typed section `Authentic`, that this a.e.
observation **coincides on the nose** with the genuine `MeasureTheory.condExp` projection:

  `condExp_bot_eq_aeValue : μ[f | ⊥] = fun _ ↦ v  ↔  aeValue f = some v`     (for `f : Ω → ℝ`).

So the a.e.-constant readback *is* the conditional-expectation readback wherever `condExp` is
defined; the polymorphic phrasing is merely the type-agnostic shadow of the same projection.

## Implementation

`CondExpMap V := Bool → Option (Bool → V)`.  `none` at a key means "absent"; `some f` stores the
random-variable representative `f`.  `get?` returns `aeValue f`, the unique `v` with
`f =ᵐ[dirac true] (fun _ ↦ v)` if one exists, else `none`.  Every *constructive* operation stores a
random variable that is **`m'`-measurable** (in fact constant, `fun _ ↦ v`), whose conditional
expectation is itself; so the seven laws reduce to the underlying function-map laws.
Non-extensionality is witnessed by a random variable agreeing with a constant `μ`-a.e. (at `true`)
but differing on the `μ`-null point `false`.
-/

@[expose] public section

namespace IrisMath.Instances

open Iris.Std Iris.Std.PartialMap Filter MeasureTheory

variable {V V' : Type _}

/-- A `CondExpMap` stores a *random-variable representative* (`Bool → V`) at every key.  `none`
means "absent".  Random variables with the same conditional expectation onto `m'` (i.e. agreeing
`μ`-a.e.) denote the same map. -/
def CondExpMap (V : Type _) : Type _ := Bool → Option (Bool → V)

namespace CondExpMap

/-- The fixed probability space: `Bool` with its standard discrete σ-algebra and the Dirac
measure at `true`.  `μ ω` sees `ω = true` with probability one; the point `false` is `μ`-null. -/
noncomputable def μ : Measure Bool := Measure.dirac true

instance : IsProbabilityMeasure μ := by unfold μ; infer_instance

/-- `ae μ = pure true`: a property holds `μ`-a.e. iff it holds at `true`.  In particular two random
variables are `μ`-a.e. equal iff they agree at `true`, so the observation below collapses random
variables differing only on the `μ`-null point `false`. -/
theorem ae_μ_eq : ae μ = pure true := by unfold μ; exact ae_dirac_eq true

instance : (ae μ).NeBot := by rw [ae_μ_eq]; infer_instance

/-- Two random variables are `μ`-a.e. equal iff they agree at `true`. -/
theorem eventuallyEq_iff {f g : Bool → V} : f =ᵐ[μ] g ↔ f true = g true := by
  unfold Filter.EventuallyEq; rw [ae_μ_eq, eventually_pure]

open Classical in
/-- The **conditional-expectation readback** of a random variable `f : Bool → V`: the unique `v`
such that `f` is `μ`-a.e. equal to the constant random variable `fun _ ↦ v`, if one exists.
Well-defined (`v` is unique) because `μ.ae` is `NeBot`.  For `μ = dirac true` this is just
`some (f true)`; the section `Authentic` shows it agrees with `MeasureTheory.condExp` onto `⊥`. -/
noncomputable def aeValue (f : Bool → V) : Option V :=
  if h : ∃ v, f =ᵐ[μ] (fun _ => v) then some h.choose else none

/-- For the `NeBot` filter `μ.ae`, two constant random variables that agree `μ`-a.e. have equal
constants. -/
theorem const_eq_of_ae {c c' : V} (h : (fun _ : Bool => c) =ᵐ[μ] (fun _ => c')) : c = c' :=
  eventuallyEq_iff.mp h

/-- If `f` is `μ`-a.e. constant `= v`, its `aeValue` is `some v`. -/
theorem aeValue_of_eventuallyEq {f : Bool → V} {v : V} (h : f =ᵐ[μ] (fun _ => v)) :
    aeValue f = some v := by
  have hex : ∃ v, f =ᵐ[μ] (fun _ => v) := ⟨v, h⟩
  rw [aeValue, dif_pos hex]
  exact congrArg some (const_eq_of_ae (hex.choose_spec.symm.trans h))

/-- The conditional-expectation readback of a constant random variable is that constant. -/
@[simp] theorem aeValue_const (v : V) : aeValue (fun _ : Bool => v) = some v :=
  aeValue_of_eventuallyEq (Filter.EventuallyEq.refl _ _)

/-- The readback evaluated through `f true`: `aeValue f = some (f true)` for every `f`. -/
theorem aeValue_eq_true (f : Bool → V) : aeValue f = some (f true) :=
  aeValue_of_eventuallyEq (eventuallyEq_iff.mpr rfl)

/-- **Conditional-expectation invariance**: random variables that agree `μ`-a.e. (equivalently,
that have the same conditional expectation onto `m'`) have the same readback.  This is the heart of
non-extensionality — the observation factors through `μ`-a.e. equality. -/
theorem aeValue_congr {f f' : Bool → V} (h : f =ᵐ[μ] f') : aeValue f = aeValue f' := by
  rw [aeValue_eq_true, aeValue_eq_true, eventuallyEq_iff.mp h]

/-- The forgetful denotation: read back the conditional-expectation value of the random variable
stored at `k`. -/
noncomputable def get? (m : CondExpMap V) (k : Bool) : Option V := (m k).bind aeValue

/-- Insert stores the *constant* random variable `fun _ ↦ v` (which is `m'`-measurable, so it is
its own conditional expectation). -/
def insert (m : CondExpMap V) (k : Bool) (v : V) : CondExpMap V :=
  fun k' => if k = k' then some (fun _ => v) else m k'

/-- Delete stores `none` (absent). -/
def delete (m : CondExpMap V) (k : Bool) : CondExpMap V :=
  fun k' => if k = k' then none else m k'

/-- The empty map: every key absent. -/
def empty : CondExpMap V := fun _ => none

/-- `bindAlter` applies `f` to the readback of each stored random variable, re-storing the result
as a constant random variable. -/
noncomputable def bindAlter (f : Bool → V → Option V') (m : CondExpMap V) : CondExpMap V' :=
  fun k => (get? m k).bind (fun v => (f k v).map (fun w => fun _ => w))

/-- `merge` combines the readbacks of two stored random variables, re-storing the result as a
constant random variable. -/
noncomputable def merge (op : Bool → V → V → V) (m₁ m₂ : CondExpMap V) : CondExpMap V :=
  fun k => (Option.merge (op k) (get? m₁ k) (get? m₂ k)).map (fun w => fun _ => w)

noncomputable instance instPartialMap : PartialMap CondExpMap Bool where
  get? := get?
  insert := insert
  delete := delete
  empty := empty
  bindAlter := bindAlter
  merge := merge

@[simp] theorem get?_eq (m : CondExpMap V) (k : Bool) :
    PartialMap.get? m k = (m k).bind aeValue := rfl

noncomputable instance instLawfulPartialMap : LawfulPartialMap CondExpMap Bool where
  get?_empty k := rfl
  get?_insert_eq {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, CondExpMap.insert, if_pos h, Option.bind_some,
      aeValue_const]
  get?_insert_ne {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, CondExpMap.insert, if_neg h]
  get?_delete_eq {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, CondExpMap.delete, if_pos h, Option.bind_none]
  get?_delete_ne {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, CondExpMap.delete, if_neg h]
  get?_bindAlter {V V' k m f} := by
    change (CondExpMap.bindAlter f m k).bind aeValue = (get? m k).bind (f k)
    unfold CondExpMap.bindAlter
    show ((get? m k).bind (fun v => (f k v).map (fun w => fun _ => w))).bind aeValue
      = (get? m k).bind (f k)
    cases hv : get? m k with
    | none => simp
    | some v =>
      simp only [Option.bind_some]
      cases hf : f k v with
      | none => simp
      | some w => simp [aeValue_const]
  get?_merge {V op m₁ m₂ k} := by
    change (CondExpMap.merge op m₁ m₂ k).bind aeValue
      = Option.merge (op k) (get? m₁ k) (get? m₂ k)
    unfold CondExpMap.merge
    show ((Option.merge (op k) (get? m₁ k) (get? m₂ k)).map (fun w => fun _ => w)).bind
      aeValue = Option.merge (op k) (get? m₁ k) (get? m₂ k)
    cases h : Option.merge (op k) (get? m₁ k) (get? m₂ k) with
    | none => simp
    | some w => simp [aeValue_const]

/-! ## Authentic conditional expectation (`V = ℝ`)

We now make precise that `aeValue` *is* the genuine conditional-expectation projection
`MeasureTheory.condExp` onto the trivial sub-σ-algebra `⊥`.  Conditioning onto `⊥` returns the
constant random variable equal to the `μ`-mean, which for `μ = dirac true` is `f true`. -/

section Authentic

/-- **Conditioning onto the trivial σ-algebra computes the mean.**  For a real random variable on
our probability space, the genuine `MeasureTheory.condExp` onto `m' = ⊥` is the constant random
variable equal to `f true` (the `μ`-mean).  This is `condExp_bot` followed by `integral_dirac`. -/
theorem condExp_bot_eq (f : Bool → ℝ) : μ[f | ⊥] = fun _ => f true := by
  rw [condExp_bot]
  funext _
  show ∫ ω, f ω ∂μ = f true
  unfold μ
  exact integral_dirac f true

/-- **The a.e. readback agrees with the genuine conditional expectation.**  For a real random
variable, `aeValue f = some v` exactly when the `MeasureTheory.condExp` projection of `f` onto the
trivial σ-algebra `⊥` is the constant `v`.  Hence `get?` genuinely observes `f` through
`condExp`. -/
theorem condExp_bot_eq_aeValue {f : Bool → ℝ} {v : ℝ} :
    μ[f | ⊥] = (fun _ => v) ↔ aeValue f = some v := by
  rw [condExp_bot_eq, aeValue_eq_true]
  constructor
  · intro h; exact congrArg some (congrFun h true)
  · intro h; have : f true = v := Option.some.injEq .. ▸ h; funext _; exact this

/-- The conditional expectation onto `⊥` is `μ`-a.e. equal to the constant given by `aeValue`,
making explicit that `get?` reads `f` only through its projection `μ[f | ⊥]`. -/
theorem condExp_bot_ae_eq_aeValue (f : Bool → ℝ) :
    ∃ v, aeValue f = some v ∧ μ[f | ⊥] =ᵐ[μ] (fun _ => v) :=
  ⟨f true, aeValue_eq_true f, by rw [condExp_bot_eq]⟩

end Authentic

/-! ## Non-extensionality

We exhibit two **distinct** `CondExpMap ℝ` representatives that are `PartialMap.equiv`
(observationally equal under `get?`) but not equal as Lean values.  The witness is a single key
storing two random variables with the *same conditional expectation*: the constant `fun _ ↦ 0` and
`centered`, which equals `0` at `true` (the `μ`-mass point) and `1` at `false` (a `μ`-null point).
Both have conditional expectation `μ[· | ⊥] = fun _ ↦ 0`, i.e. both read back to `some 0`, yet they
differ at `false` (which is `μ`-null, hence invisible to the conditional expectation).

This is genuine **type-I intrinsic** non-extensionality: the stored payload `Bool → V` is strictly
richer than `Option V`, and `get?` collapses it via the conditional-expectation projection — there
is no discarded product factor. -/

/-- A real random variable equal to `0` at the mass point `true` and `1` at the null point `false`.
It is a mean-zero (conditionally-centered) perturbation of the constant `0`: its conditional
expectation onto `⊥` is `0`, but it is not the constant function. -/
def centered : Bool → ℝ := fun b => if b then 0 else 1

/-- `centered` agrees with the constant-`0` random variable `μ`-a.e. (they coincide at `true`). -/
theorem centered_ae_eq_const : centered =ᵐ[μ] (fun _ => (0 : ℝ)) :=
  eventuallyEq_iff.mpr rfl

/-- The conditional expectation of `centered` onto `⊥` is the constant `0` — the same as that of
`fun _ ↦ 0` — even though `centered` is not constant.  This is the authentic-`condExp` content of
the non-extensionality witness. -/
theorem condExp_centered : μ[centered | ⊥] = fun _ => (0 : ℝ) := by
  rw [condExp_bot_eq]; rfl

/-- `centered` differs from the constant-`0` random variable at `false` (a `μ`-null point), proving
the two representatives are distinct Lean functions. -/
theorem centered_ne_const : centered ≠ (fun _ => (0 : ℝ)) := by
  intro h
  have := congrFun h false
  simp only [centered, Bool.false_eq_true, if_false] at this
  exact one_ne_zero this

/-- First witness: key `true` stores the constant-`0` random variable. -/
def m_const : CondExpMap ℝ := CondExpMap.insert CondExpMap.empty true 0

/-- Second witness: key `true` stores the `centered` random variable (same conditional expectation,
different representative). -/
def m_centered : CondExpMap ℝ := fun k => if k = true then some centered else none

/-- **Non-extensionality.**  `m_const` and `m_centered` are observationally equal
(`PartialMap.equiv`) — both denote "key `true` ↦ conditional-expectation value `0`, everything else
absent" — yet they are **distinct** Lean values, because the underlying stored random variables
(`fun _ ↦ 0` versus `centered`) differ on the `μ`-null point `false`.  This is impossible for any
`ExtensionalPartialMap`, so `CondExpMap` is genuinely non-extensional, and the non-extensionality
is *intrinsic* (the collapse is the conditional-expectation projection, not a projection of a
stored product). -/
theorem nonextensional :
    PartialMap.equiv (M := CondExpMap) m_const m_centered ∧ m_const ≠ m_centered := by
  refine ⟨fun k => ?_, ?_⟩
  · -- observationally equal: both give `some 0` at key `true`, `none` elsewhere
    by_cases hk : k = true
    · subst hk
      change ((m_const true).bind aeValue) = ((m_centered true).bind aeValue)
      have hc : m_const true = some (fun _ => 0) := by simp [m_const, CondExpMap.insert]
      have hr : m_centered true = some centered := by simp [m_centered]
      rw [hc, hr, Option.bind_some, Option.bind_some,
        aeValue_const, aeValue_congr centered_ae_eq_const, aeValue_const]
    · change ((m_const k).bind aeValue) = ((m_centered k).bind aeValue)
      have hc : m_const k = none := by
        simp [m_const, CondExpMap.insert, CondExpMap.empty, Ne.symm hk]
      have hr : m_centered k = none := by simp [m_centered, hk]
      rw [hc, hr]
  · -- distinct as Lean values: at key `true` the stored random variables differ off the mass point
    intro h
    have h0 : m_const true = m_centered true := congrFun h true
    have hc : m_const true = some (fun _ => 0) := by simp [m_const, CondExpMap.insert]
    have hr : m_centered true = some centered := by simp [m_centered]
    rw [hc, hr, Option.some.injEq] at h0
    exact centered_ne_const h0.symm

/-- Consequently this instance is genuinely non-extensional: `equiv` does NOT imply `=`. -/
theorem not_extensionalPartialMap :
    ¬ ∀ {m₁ m₂ : CondExpMap ℝ}, PartialMap.equiv m₁ m₂ → m₁ = m₂ := by
  intro h
  exact nonextensional.2 (h nonextensional.1)

end CondExpMap

/-! ## Applicability: a `HeapView` CMRA over conditional-expectation cells

Since `CondExpMap` is a `LawfulPartialMap CondExpMap Bool`, it slots directly into
`Iris.Algebra.HeapView` (`Iris/Algebra/HeapView.lean`, lines 314-495):

  `HeapView F Bool V H`  with  `H := CondExpMap` (this file) and `K := Bool`.

`HeapView` provides authoritative ownership `Auth (.own one) m` over the whole heap of
random-variable cells, and fragmental ownership `Frag k dq v` over a single cell's *conditional
expectation*; the view relation `HeapR` observes the heap **only** through `Std.PartialMap.get?`,
i.e. through this file's conditional-expectation readback `aeValue`.

### Information-theoretic reading

`condExp` is the orthogonal projection (a contraction, `‖μ[f | m']‖₂ ≤ ‖f‖₂`) of `L²(μ)` onto the
closed subspace `L²(m', μ)` of `m'`-measurable random variables; the sub-σ-algebra `m'` is exactly
the *information* currently revealed.  Two natural classes of update leave the observation fixed:

* **Refining the σ-algebra (revealing more information).**  Enlarging `m'` towards `m₀` can only
  make `condExp` finer.  Storing a cell as an already-`m'`-measurable (here, constant) random
  variable means its conditional expectation is itself, so the readback is stable under refinement.
* **A conditionally-centered (mean-zero) perturbation, applied invisibly.**  Replacing a stored
  random variable `f` by any `g` with `μ[g | m'] = μ[f | m']` — equivalently `g - f` has
  conditional expectation `0`, a mean-zero perturbation supported on `μ`-null structure off the
  observed cell — leaves the readback unchanged.  `centered` above is exactly such a perturbation of
  the constant `0`.

### An interesting frame-preserving update `~~>`

The conditional expectation makes a class of updates *free* (frame-preserving) that change real data
but leave the observation fixed: **replacing the stored random variable by any other with the same
conditional expectation** is the identity on conditional-expectation values.  Concretely, for
`H := CondExpMap`:

  `Auth (.own one) m₁ • Frag k (.own one) v  ~~>  `
  `Auth (.own one) (insert m₁ k v) • Frag k (.own one) v`,

an instance of `HeapView.update_replace` (`Iris/Algebra/HeapView.lean`, line 438): the new cell
value `v2 := v` is valid because `✓ v` already held, and the update is stated purely through
`get?`/`insert`, never term equality.  Because `insert` re-stores the constant (hence
`m'`-measurable) random variable with conditional expectation `v`, this is observationally an
identity on the CMRA element — yet the underlying random-variable storage has been refreshed by a
mean-zero perturbation.  More generally, `HeapView.update_of_local_update` lifts any local update
`(v, v) ~l~> (v, v')` on the conditional-expectation values; the "mean-zero refinement off the
observed cell" is invisible to the CMRA precisely because every `HeapView` operation only sees
`aeValue = condExp(· | m')`.  This is exactly the conditional-expectation intuition: changing a
random variable by something with zero conditional expectation does not change the conditional
expectation, hence does not change the observable resource. -/

section Applicability

open CondExpMap

/-- **Conditional-expectation invariance under mean-zero refinement**, machine-checked.  Replacing
the constant random variable at a key by *any* random variable with the same conditional expectation
(here: agreeing `μ`-a.e.) yields an `equiv` map.  Such a rewrite is therefore frame-preserving for
every `HeapView` update built on this instance (it is the denotation-level content of
`update_replace`/`update_of_local_update`). -/
theorem refine_meanZero_equiv (m : CondExpMap V) (k : Bool) (v : V) {g : Bool → V}
    (hg : g =ᵐ[μ] (fun _ => v)) :
    PartialMap.equiv (PartialMap.insert m k v) (fun k' => if k = k' then some g else m k') := by
  intro k'
  change ((CondExpMap.insert m k v) k').bind aeValue
    = ((fun k' => if k = k' then some g else m k') k').bind aeValue
  by_cases hk : k = k'
  · simp only [CondExpMap.insert, if_pos hk, Option.bind_some]
    rw [aeValue_const, aeValue_of_eventuallyEq hg]
  · simp only [CondExpMap.insert, if_neg hk]

end Applicability

end IrisMath.Instances
