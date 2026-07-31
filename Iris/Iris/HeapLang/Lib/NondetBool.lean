module

public import Iris.ProgramLogic.WeakestPre
public import Iris.HeapLang.ProofMode
public import Iris.HeapLang.PrimitiveLaws
public import Iris.Instances.Lib.Invariants

namespace Iris.HeapLang

public section

variable [HeapLangGS hlc GF]

def nondetBool := hl_val% λ _,
    let l := ref(#true);
    fork(
      l ← #false
    );
    !l

theorem nondetBool.spec : ⊢@{IProp GF}
    {{ True }} hl(&nondetBool #()) {{ (b : Bool), RET hl_val(#b); True }} := by
  iintro %Φ - K
  unfold nondetBool
  wp_alloc l with Hl
  wp_pures
  imod inv_alloc `n ⊤ iprop(∃ (b : Bool), l ↦ hl_val(#b)) $$ [$Hl] with #Hinv
  wp_bind fork(_)
  iapply wp_fork $$ [K] []
  · inext
    wp_pures
    iinv Hinv with >⟨%b, Hl⟩
    · simp; infer_instance -- TODO: iinv should solve this
    wp_load
    iintro !> {$Hl}
    iapply K $$ [//]
  · inext
    iinv Hinv with >⟨%b, Hl⟩
    · simp; infer_instance
    wp_store
    iframe
