/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

@[expose] public section

section gfp
open Lean.Order PartialOrder CompleteLattice

variable {α} [CompleteLattice α]

noncomputable def gfp (f : α → α) : α := sup (fun x => x ⊑ f x)

theorem le_gfp {f : α → α} {x : α} (h : x ⊑ f x) : x ⊑ gfp f := le_sup _ h

theorem gfp_postfixed {f : α → α} (hm : monotone f) : gfp f ⊑ f (gfp f) := by
  apply sup_le; intro y hy
  exact rel_trans hy (hm _ _ (le_sup _ hy))

theorem gfp_fix {f : α → α} (hm : monotone f) : gfp f = f (gfp f) :=
  rel_antisymm (gfp_postfixed hm) (le_gfp (hm _ _ (gfp_postfixed hm)))

end gfp
