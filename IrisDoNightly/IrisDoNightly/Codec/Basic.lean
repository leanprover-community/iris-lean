module

public import IrisDoNightly.AxSem
import Std.Tactic.Do
import Std.Internal.Do

/-! # Shared codec model + stepping macros (heap-free codecs, approach 2) -/

set_option mvcgen.warning false

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax

open HeapLangAxioms

variable {wp} [HeapLangAxioms wp]

@[expose] public section

/-- Substituting into a value-expression is the identity: bridges the default simp normalisation
of `.val`→`.ofVal` so `substStr` reduces on `.ofVal` leaves. -/
@[simp] theorem substStr_ofVal (x : String) (v w : Val) :
    Exp.substStr x v (Exp.ofVal w) = Exp.ofVal w := rfl

attribute [simp] BinOp.eval

def byteVal (n : Int) : Val := .lit (.int n)

def vList : List Int → Val
  | [] => .injL (.lit .unit)
  | c :: cs => .injR (.pair (byteVal c) (vList cs))

end

/-! ## Shared stepping macros

The heap-free codec proofs (`Codec/*/Correctness.lean`) all symbolically execute their programs
with the same four steps, so they live here — the common ancestor every codec file imports — rather
than being re-declared per file. They are `scoped` to `Iris.HeapLang.Ax`, so importers get them by
opening the namespace (already done via `namespace Iris.HeapLang.Ax`).

`hl_beta` takes an optional trailing simp-lemma list so a codec can unfold its own model constants
during the post-substitution normalisation, e.g. `hl_beta [deltaEnc, deltaDec]`. -/

scoped syntax "hl_beta" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
scoped macro_rules
  | `(tactic| hl_beta) =>
    `(tactic| (vcgen until Exp.subst _ _ _; refine ⟨_, _, _, rfl, ?_⟩;
               simp [Exp.subst, Exp.substStr, vList]))
  | `(tactic| hl_beta [$ts,*]) =>
    `(tactic| (vcgen until Exp.subst _ _ _; refine ⟨_, _, _, rfl, ?_⟩;
               simp [Exp.subst, Exp.substStr, vList, $ts,*]))

scoped macro "hl_projlet" : tactic =>
  `(tactic| (vcgen; refine ⟨_, _, rfl, ?_⟩; hl_beta))

scoped macro "hl_binop" : tactic =>
  `(tactic| (vcgen; simp only [byteVal, BinOp.eval, Option.some.injEq, exists_eq_left']; hl_beta))

scoped macro "hl_call " t:term : tactic =>
  `(tactic| (refine spec_app ?_; refine wp_mono ?_ ($t trivial); intro _ hcall; subst hcall; hl_beta))

/-- `vcgen' [ih, …]` — what we expect `vcgen` itself to do *someday*, for codec specs in
*continuation-passing* form `Φ (vList (model …)) ⊑ wp⟦prog⟧ Φ` (postcondition a variable `Φ`). It runs
the ENTIRE obvious weakest-precondition computation and leaves only the pure mathematical side goals,
so a proof is `simp only [prog]; vcgen' [ih]` followed by discharging the side goals — no interleaving
of stepping and side-reasoning, no hand-tuned step counts.

The supplied terms (typically the induction hypothesis `ih`) are the specs applied at recursive calls;
`apply`-ing one leaves *its* hypotheses as side goals. It loops four progress-gated moves to a
fixpoint, over all goals (`any_goals`):
  A. reach a call boundary (any application `Exp.app _ _`) and `apply` a spec — fires only where a
     supplied spec unifies, i.e. the *recursive* call (the spec is keyed on the smaller argument);
     it also stops at each `let` and the top-level call, where `apply` fails and it falls through.
     The `Exp.app _ _` pattern is arity-generic: it matches the outermost application of a 1-, 2- or
     3-argument recursive call alike.
  B. `simp` a substitution / `substStr` guard / `vList` / `byteVal` (the documented subst-normalisation
     gap — the one thing here that is not already plain `vcgen`; see `AutoTest.lean`);
  C. step to the next substitution — crosses the top-level call and each `let`;
  D. one bare step — collapses a trailing value `wp`; reached only when no call/subst remains, so it
     never dives into (and unrolls) a recursive call.
`vcgen' []` (no specs) is the non-recursive/base case. For a codec whose recursion branches on an
index guard (e.g. Nat-recursion `if k=0`), close the vacuous branch with `(try (exfalso; grind))`
before the real-branch discharger. Once the framework prefers a registered spec over unrolling at a
call site, this collapses to plain `vcgen`. -/
scoped macro "vcgen'" " [" specs:term,* "] " : tactic =>
  `(tactic| repeat any_goals first
      | (vcgen (errorOnMissingSpec := false) [BinOp.eval] until Exp.app _ _
         first $[| apply $specs]* | fail)
      | simp [Exp.subst, Exp.substStr, substStr_ofVal, vList, byteVal]
      | vcgen (errorOnMissingSpec := false) [BinOp.eval] until Exp.subst _ _ _
      | vcgen (errorOnMissingSpec := false) [BinOp.eval])

@[expose] public section

def nthD : List Int → Int → Int
  | [], _ => 0
  | x :: xs, r => if r = 0 then x else nthD xs (r - 1)

def hlNth : Val := hl_val%
  rec go t := λ r,
    match t with
    | injl(u) => #0
    | injr(p) =>
        let x := fst(p);
        let xs := snd(p);
        if r = #0 then x else (let r' := r - #1; go xs r')

theorem hlNth_spec (t : List Int) : ∀ r : Int,
    True ⊑ wp⟦hl(v(&hlNth) v(&(vList t)) v(&(byteVal r)))⟧
      (fun v => v = byteVal (nthD t r)) := by
  induction t with
  | nil =>
    intro r
    simp only [hlNth]
    hl_beta; hl_beta
    vcgen
    refine Or.inl ⟨_, rfl, ?_⟩
    hl_beta
    vcgen
    simp [nthD, byteVal]
  | cons x xs ih =>
    intro r
    simp only [hlNth]
    hl_beta; hl_beta
    vcgen
    refine Or.inr ⟨_, rfl, ?_⟩
    hl_beta
    hl_projlet
    hl_projlet
    vcgen
    simp only [byteVal, BinOp.eval, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed,
      Bool.or_true, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨_, rfl, ?_⟩
    by_cases hr : r = 0
    · subst hr
      simp only [beq_self_eq_true, ite_true]
      vcgen
      simp [nthD]
    · have hb : (hl_val(#r) == hl_val(#(0:Int))) = false := by simp [hr]
      rw [hb]
      simp only [Bool.false_eq_true, ite_false]
      hl_binop
      refine wp_mono ?_ (ih (r - 1) trivial)
      intro v hv
      subst hv
      simp [nthD, ite_eq_right hr, byteVal]

end

end Iris.HeapLang.Ax
