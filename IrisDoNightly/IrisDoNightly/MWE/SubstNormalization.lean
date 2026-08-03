module

public import IrisDoNightly.AxSem
public import IrisDoNightly.Codec.Basic
import Std.Tactic.Do
import Std.Internal.Do

/-!
# `vcgen` does not normalise the program between spec applications

Object-language application reduces by capture-avoiding substitution: `spec_beta` rewrites
`(λ x, x) v` to `(body.subst f _).subst x v`, a *nested* `Exp.subst`. `vcgen` then stalls —

    No spec found for program Exp.substStr x v (Exp.subst f g body)

— because `reduceHead?` only reduces at reducible transparency (so it neither unfolds `Exp.substStr`
nor reduces the inner `Exp.subst` first), and simp lemmas passed as `vcgen [Exp.subst, …]` become
equational specs that rewrite only the program *head*, never under the outer `substStr`.

`stalls_here` vs `works_with_manual_simp` below isolate this: a plain `simp [Exp.subst, Exp.substStr]`
computes the substitution `vcgen` will not. Wanted: a `vcgen` mode that runs a user simp set over the
whole program term after each spec application, so a single `vcgen` steps a non-recursive body.
-/

set_option mvcgen.warning false

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax.MWE

open HeapLangAxioms

variable {wp} [HeapLangAxioms wp]

/-- Clean beta rule (no existential): a literal closure applied to a value. -/
@[spec 2000] theorem spec_beta {f x : Binder} {body : Exp} {v : Val} {Φ : Val → Prop} :
    wp⟦(body.subst f (.rec_ f x body)).subst x v⟧ Φ
      ⊑ wp⟦Exp.app (Exp.ofVal (Val.rec_ f x body)) (Exp.ofVal v)⟧ Φ := by
  intro h; exact wp_app (wp_val (wp_val ⟨f, x, body, rfl, h⟩))

def hlId : Val := hl_val% λ x, x

/-- Stalls: `vcgen` applies `spec_beta`, then leaves `Exp.substStr "x" #7 (Exp.subst …)` unreduced. -/
theorem stalls_here :
    True ⊑ wp⟦Exp.app (Exp.ofVal hlId) (Exp.ofVal (byteVal 7))⟧ (fun v => v = byteVal 7) := by
  simp only [hlId]
  vcgen (errorOnMissingSpec := false) [Exp.subst, Exp.substStr, byteVal]
  exact wp_val rfl

/-- Works: one manual `simp` reduces the substitution, then the goal closes. -/
theorem works_with_manual_simp :
    True ⊑ wp⟦Exp.app (Exp.ofVal hlId) (Exp.ofVal (byteVal 7))⟧ (fun v => v = byteVal 7) := by
  simp only [hlId]
  vcgen (errorOnMissingSpec := false) [Exp.subst, Exp.substStr, byteVal]
  simp [Exp.subst, Exp.substStr]
  exact wp_val rfl

end Iris.HeapLang.Ax.MWE
