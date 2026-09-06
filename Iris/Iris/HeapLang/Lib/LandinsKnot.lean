/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Bai, Klaus Kraßnitzer
-/
module

public import Iris.Instances.Lib.Invariants
public import Iris.Std.Namespaces
public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode

namespace Iris.HeapLang

open BI Iris ProgramLogic

@[expose] public section

namespace LandinKnot

def landinsKnot : Val := hl_val%
  λ f,
    let r := ref(λ x, x);
    r ← (λ x, f (!r) x);
    !r

def landinN : Namespace := ndot nroot "landin"

section Spec

variable {GF} [HeapLangGS hlc GF]

theorem wp_landinsKnot (P : Val → IProp GF) (Q : Val → Val → IProp GF) (F v1 : Val) :
    {{ (∀ (f v2 : Val),
          {{ (∀ (v3 : Val),
              {{ P v3 }} hl(&f &v3) {{ u, RET u; Q u v3 }}) ∗ P v2 }}
          hl(&F &f &v2)
          {{ u, RET u; Q u v2 }}) ∗
        P v1 }}
    hl(&landinsKnot &F &v1)
    {{ u, RET u; Q u v1 }} := by
  iintro %Φ ⟨#H, HP⟩ HQ
  wp_bind &landinsKnot _
  wp_rec
  wp_alloc r with Hr
  wp_store
  wp_load
  imod inv_alloc landinN ⊤ _ $$ Hr with #Hinv
  ihave HQ : ▷ (∀ u, Q u v1 -∗ Φ u) $$ [HQ]
  · inext; iexact HQ
  iloeb as IH generalizing %v1 %Φ
  wp_rec
  wp_bind !_
  iinv Hinv with >Hr
  wp_load
  imodintro; iframe
  iapply H $$ [$HP] [$]
  iintro %v3 !> %Φ HP HQ
  iapply IH $$ HP HQ

end Spec

end LandinKnot
end
