module

public import Iris.ProgramLogic.WeakestPre
public import Iris.HeapLang.ProofMode
public import Iris.HeapLang.PrimitiveLaws
public import Iris.Instances.Lib.Invariants

namespace Iris.HeapLang

public section

variable [HeapLangGS hlc GF]

@[rocq_alias heap_lang.nondet_bool]
def nondetBool := hl_val% λ _,
    let l := ref(#true);
    fork(
      l ← #false
    );
    !l

@[rocq_alias heap_lang.nondet_bool_spec]
theorem nondetBool.spec :
    {{ (True : IProp GF) }} hl(&nondetBool #()) {{ (b : Bool), RET hl_val(#b); True }} := by
  iintro %Φ - K
  unfold nondetBool
  wp_alloc l with Hl
  wp_pures
  imod inv_alloc `rnd ⊤ iprop(∃ (b : Bool), l ↦ hl_val(#b)) $$ [$Hl] with #Hinv
  wp_apply wp_fork $$ [K] []
  · wp_pures
    iinv Hinv with >⟨%b, Hl⟩
    wp_load
    iintro !> {$Hl}
    iapply K $$ [//]
  · iinv Hinv with >⟨%b, Hl⟩
    wp_store
    iframe
