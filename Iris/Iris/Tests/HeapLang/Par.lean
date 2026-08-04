/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Klaus Kraßnitzer
-/
module

public import Iris.HeapLang.Lib.Par

@[expose] public section
namespace Iris.Tests.HeapLang.Par

open Iris.HeapLang BI Iris ProgramLogic Spawn Iris.HeapLang.Par

-- Regression test for
-- https://leanprover.zulipchat.com/#narrow/channel/490604-iris-lean/topic/Porting.20iris-tutorial/near/613886178
-- testing substitution into `par`
section
-- `l` is deliberately a free HeapLang variable so we can test that substitution works as intended
set_option linter.heapLang.freeVars false

example (v : Val) :
    Exp.substStr "l" v hl((l ← #21) ‖ (l ← #2))
      = hl(&par (λ _, v(&v) ← #21) (λ _, v(&v) ← #2)) := rfl

end

def par_client : Exp := hl%
  let l1 := ref(#0);
  let l2 := ref(#0);
  ((l1 ← #21) ‖ (l2 ← #2));
  let life := !l1 * !l2;
  (l1, l2, life)

example {hlc} {GF : BundledGFunctors} [HeapLangGS hlc GF] [SpawnG GF] :
    {{ True }} hl(&par_client)
      {{ (l1 l2 : Loc) (life : Int), RET hl_val((#l1, #l2, #life));
         l1 ↦ some hl_val(#21) ∗ l2 ↦ some hl_val(#2) ∗ ⌜life = 42⌝ }} := by
  iintro %Φ - K
  unfold par_client
  wp_alloc l1 with Hl1
  wp_pures
  wp_alloc l2 with Hl2
  wp_pures
  wp_bind &par _ _
  iapply wp_par (fun _ => l1 ↦ some hl_val(#21)) (fun _ => l2 ↦ some hl_val(#2))
    $$ [Hl1] [Hl2] [K]
  · wp_store; imodintro; iexact Hl1
  · wp_store; imodintro; iexact Hl2
  · iintro %r1 %r2 ⟨Hl1, Hl2⟩
    inext
    wp_pures
    wp_load
    wp_load
    wp_pures
    iintro !>
    iapply K
    iframe
    itrivial

end Iris.Tests.HeapLang.Par
end
