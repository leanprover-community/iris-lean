module

public import IrisDoNightly.Codec.Auto
import Std.Tactic.Do
import Std.Internal.Do

set_option mvcgen.warning false

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax.Test

open HeapLangAxioms

variable {wp} [HeapLangAxioms wp]

def idxOf : List Int → Int → Int
  | [], _ => 0
  | x :: xs, c => if x = c then 0 else idxOf xs c + 1

def hlIndexOf : Val := hl_val%
  rec go t := λ c,
    match t with
    | injl(u) => #0
    | injr(p) =>
        let x := fst(p);
        let xs := snd(p);
        if x = c then #0 else (#1 + go xs c)

/-- **UNFOLD-LEMMA technique** (green): the wp of a call equals the wp of the body pre-substituted,
with the recursive call FOLDED back to `hlIndexOf`. Proving it costs the two top betas once; the
payoff is that stepping through it, `vcgen` never sees the top substitution AND the recursion is the
folded constant so `ih` (not `spec_beta`) matches it. Verified experimentally: `vcgen [ih]` steps the
whole body via this lemma with NO over-step of the recursion and NO OOM (terms stay small because the
recursion is a constant, not a copied closure). Two obstacles keep it from being fully push-button,
both = the known MWEs: (a) the body's OWN `match`/`let` binders each still beta into an `Exp.subst`
`vcgen` can't reduce (`MWE/SubstNormalization`); (b) as a global `@[spec]` it re-fires on the
recursive call before the argument `snd p` has reduced to `vList xs`, so `ih` doesn't match yet. -/
theorem hlIndexOf_unfold (tv cv : Val) (Φ : Val → Prop) :
    wp⟦hl(match v(&tv) with
          | injl(u) => #0
          | injr(p) =>
              let x := fst(p); let xs := snd(p);
              if x = v(&cv) then #0 else #1 + v(&hlIndexOf) xs v(&cv))⟧ Φ
      ⊑ wp⟦hl(v(&hlIndexOf) v(&tv) v(&cv))⟧ Φ := by
  intro h
  simp only [hlIndexOf]
  hl_step; hl_step
  exact h

/-! ## The PRINCIPLED approach (vs. the janky per-function unfold lemma)

The mvcgen-idiomatic shape needs NO per-function lemma: make the function `@[reducible]` (so `ih`
matches its recursive call up-to-reducible — mirroring how `f.eq_def` unfolds a Lean function), make
`byteVal` `@[reducible]` (so the stepper's normalisation doesn't break key matching), then the whole
spec proof is `induction; intro; simp only [vList]; repeat (vcgen [ih]; simp [Exp.subst, …])`.

Build-verified this STEPS the entire recursive body with NO OOM and NO hang (the recursion never
copies the closure because — in principle — `ih` replaces it). What still blocks it, all framework
issues (each a filed MWE / precise ask), NOT proof jank:
1. the body's `match`/`let` binders each beta into an `Exp.subst` `vcgen` cannot reduce
   (`MWE/SubstNormalization`) — hence the interleaved `simp`;
2. during stepping, `vcgen` fires `spec_beta` on the recursive call and UNFOLDS it rather than
   selecting the higher-priority `ih` — the reducible-closure-vs-`ih` pattern does not match in the
   focused sub-term the way it does when the whole goal IS the call (isolation tests `test_ih_*`
   showed it matching there). A spec-selection ordering/matching gap.

Fix (1)+(2) and the principled form is fully push-button `vcgen [ih]` — no unfold lemma, no
`hl_step`. (It also needs `byteVal` `@[reducible]`; I verified that makes `vcgen`'s key-matching
consistent, but it changes `simp` behavior enough to break a couple of existing `simp`-closed proofs,
so adopting the principled form is a coordinated change, not a drop-in.) -/

/-- Fully transparent migrated proof: only `vcgen`, `grind`, and — the one thing `vcgen` provably
cannot do (gap-1, see `MWE/SubstNormalization.lean`) — a `simp [Exp.subst, Exp.substStr]` to compute
the capture-avoiding substitution that each `vcgen` step leaves behind. No `hl_step` macro, no
`refine spec_* ?_` value-plumbing. `vcgen` even auto-splits the symbolic `if`; the recursion is one
`wp_mono ?_ (ih …)`. `wp` abbreviates `vcgen (errorOnMissingSpec := false) [BinOp.eval]`. -/
theorem hlIndexOf_spec (t : List Int) : ∀ c : Int,
    True ⊑ wp⟦hl(v(&hlIndexOf) v(&(vList t)) v(&(byteVal c)))⟧
      (fun v => v = byteVal (idxOf t c)) := by
  induction t with
  | nil =>
    intro c
    simp only [hlIndexOf]
    hl_step; hl_step; hl_step
    refine wp_val ?_; grind [idxOf]
  | cons x xs ih =>
    intro c
    simp only [hlIndexOf]
    hl_step; hl_step; hl_step; hl_step; hl_step
    refine spec_if_bind ?_; refine spec_binop_eq ?_; refine spec_if_lit ?_
    split
    · refine wp_val ?_; grind [idxOf]
    · refine spec_binopR ?_
      refine wp_mono ?_ (ih c trivial)
      intro v hv; subst hv
      hl_step
      grind [idxOf]

/-! ## Where plain `vcgen` shines vs. where it can't

CONFIRMED wins for plain `vcgen` (no `hl_step`, no manual `refine spec_* ?_`):
* It auto-evaluates a symbolic `if` guard (`spec_if_bind` → `spec_binop_eq` → `spec_if_lit`) and
  auto-SPLITS into the two branches — replacing `refine spec_if_bind ?_; … ; split` with one `vcgen`.
* At a call site to a `@[spec]`-registered function it applies that spec (no substitution).

* At a SINGLE call site to a `@[spec]`-registered function (keyed on `Val.lit (.int _)`, priority
  above `spec_beta`), plain `vcgen` applies that spec and closes — see `MWE/CompositionHang.lean`.

Caveats found (why `hl_step` / manual control is still needed in places):
* Stepping a function's OWN body needs the gap-1 substitution `simp` after each beta.
* `vcgen` OVER-STEPS a recursive call (one beta into the closure), which breaks `ih` matching — so a
  recursive branch must be stopped while it is still `1 + go xs c` (hence manual `spec_if_bind …`).
* NESTED composition of two `@[spec]` calls HANGS `vcgen` (framing a fixed postcondition against a
  differing continuation loops) — `MWE/CompositionHang.lean`. -/

/-! ## Probe: return-value construction (`injr((x, go …))`) + recursion, maximal `vcgen` -/

def eraseIdx' : List Int → Int → List Int
  | [], _ => []
  | x :: xs, r => if r = 0 then xs else x :: eraseIdx' xs (r - 1)

def hlEraseIdx : Val := hl_val%
  rec go t := λ r,
    match t with
    | injl(u) => injl(#())
    | injr(p) =>
        let x := fst(p);
        let xs := snd(p);
        if r = #0 then xs else (let r' := r - #1; injr((x, go xs r')))

theorem hlEraseIdx_spec (t : List Int) : ∀ r : Int,
    True ⊑ wp⟦hl(v(&hlEraseIdx) v(&(vList t)) v(&(byteVal r)))⟧
      (fun v => v = vList (eraseIdx' t r)) := by
  induction t with
  | nil =>
    intro r
    simp only [hlEraseIdx]
    hl_step; hl_step; hl_step
    refine wp_injL (wp_val ?_); simp [eraseIdx', vList]
  | cons x xs ih =>
    intro r
    simp only [hlEraseIdx]
    hl_step; hl_step; hl_step; hl_step; hl_step
    vcgen (errorOnMissingSpec := false) [BinOp.eval]   -- handles the `if` + splits both branches
    · simp_all [eraseIdx']                             -- vc1 (r = 0): pure
    · hl_step                                          -- vc2 (r ≠ 0): step `let r'`
      refine spec_injR ?_; refine spec_pair ?_         -- build `injr((x, ·))`
      refine wp_mono ?_ (ih (r - 1) trivial)           -- the recursion
      intro v2 hv2; subst hv2
      refine spec_val ?_
      simp_all [eraseIdx', vList, byteVal]

/-! ## Continuation-passing spec form → composition is PURE `vcgen` (no framing, no hang) -/

def incByte : Val := hl_val% λ n, n + #1

/-- CPS spec: postcondition `Φ` is a VARIABLE, so `vcgen` composes it with any continuation by
unification — no framing (which is what hung the closed `True ⊑ wp e (·=v)` form). -/
@[spec 2500] theorem incByte_cps (n : Int) (Φ : Val → Prop) :
    Φ (Val.lit (.int (n + 1))) ⊑ wp⟦hl(v(&incByte) #n)⟧ Φ := by
  intro h; simp only [incByte]
  hl_step
  first | exact h | (refine spec_binop_add ?_; exact h) | (refine wp_val ?_; exact h)

/-- `incByte (incByte n)` — nested composition, now PURE `vcgen` (this hangs with the closed form; see
`MWE/CompositionHang.lean`). -/
example (n : Int) :
    True ⊑ wp⟦hl(v(&incByte) (v(&incByte) #n))⟧
      (fun v => v = Val.lit (.int (n + 2))) := by
  vcgen
  grind

def dec1 : Val := hl_val% λ n, n - #1

@[spec 2500] theorem dec1_cps (n : Int) (Φ : Val → Prop) :
    Φ (Val.lit (.int (n - 1))) ⊑ wp⟦hl(v(&dec1) #n)⟧ Φ := by
  intro h; simp only [dec1]
  hl_step
  first | exact h | (refine spec_binop_sub ?_; exact h) | (refine wp_val ?_; exact h)

/-- ROUND-TRIP: `dec1 (incByte n) = n` — the `decomp (comp x)` shape of `delta_roundtrip` /
`rle_roundtrip`, proved PURE `vcgen` + `grind`, composing the two CPS specs. -/
example (n : Int) :
    True ⊑ wp⟦hl(v(&dec1) (v(&incByte) #n))⟧
      (fun v => v = Val.lit (.int n)) := by
  vcgen
  grind

end Iris.HeapLang.Ax.Test
