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
  wp_pures
  wp_bind ref(_)
  iapply wp_alloc
  iintro %l !> Hl
  wp_pures
  iapply fupd_wp
  ihave >#inv := inv_alloc `rnd ⊤ iprop(∃ (b : Bool), l ↦ hl_val(#b)) $$ [Hl]
  · iexists ?_; iassumption
  iintro !>
  wp_bind fork(_)
  iapply wp_fork $$ [K] []
  · inext
    wp_pures
    iapply wp_atomic
    ihave >⟨⟨%b, Hl⟩, Hclose⟩ := inv_acc CoPset.subseteq_top $$ inv
    iintro !>
    iapply wp_load $$ Hl
    iintro !> Hl
    ihave aux :=  Hclose $$ [Hl]
    · iexists ?_; iassumption
    icases aux with >-
    iintro !>
    iapply K $$ [//]
  · inext
    iapply wp_atomic
    ihave >⟨⟨%b, Hl⟩, Hclose⟩ := inv_acc CoPset.subseteq_top $$ inv
    iintro !>
    iapply wp_store $$ Hl
    iintro !> Hl
    iapply Hclose
    iexists ?_
    iassumption
