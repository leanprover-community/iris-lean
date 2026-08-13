/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.HeapLang
public import Iris.HeapLang.Lib.NondetBool

/-! # The clairvoyant coin

The clairvoyant coin predicts all the values that it will *non-deterministically* choose
throughout the execution of the program. This can be seen in the spec. The predicate `coin c bs`
expresses that `bs` is the list of all the values of the coin in the future. The `readCoin`
operation always returns the head of `bs` and the `tossCoin` operation takes the `tail` of `bs`. -/

namespace Iris.HeapLang

-- type Coin := Ref Bool × ProphId
-- `@[rocq_alias heap_lang.new_coin]` clashes with `lazy_coin.v`'s `new_coin`.
def newCoin := hl_val%
  λ _, (ref(&nondetBool #()), newProph())

-- `@[rocq_alias heap_lang.read_coin]` clashes with `lazy_coin.v`'s `read_coin`.
def readCoin := hl_val% λ cp, !fst(cp)

@[rocq_alias heap_lang.toss_coin]
def tossCoin := hl_val%
  λ cp,
    let c := fst(cp);
    let p := snd(cp);
    let r := &nondetBool #();
    c ← r;
    resolveProph(p, r);
    #()

variable {hlc GF} [HeapLangGS hlc GF]

section Proofs

@[rocq_alias heap_lang.prophecy_to_list_bool]
def prophecyToListBool (vs : List (Val × Val)) : List Bool :=
  vs.map (·.2 = hl_val(#true))

-- No Rocq counterpart: upstream `destruct`s the tossed boolean at each use site instead.
@[simp, grind =]
theorem prophecyToListBool_cons (vs : List (Val × Val)) (v : Val) (b : Bool) :
    prophecyToListBool ((v, hl_val(#b)) :: vs) = b :: prophecyToListBool vs := by
  cases b <;> rfl

-- `@[rocq_alias heap_lang.coin]` clashes with `lazy_coin.v`'s `coin`.
/-- `cp` is a pair of `c` and `p`, where `p` is a prophecy predicting every future value of the
    coin, `bs` is the list of those values, and `c` points to the head of `bs`. -/
def coin (cp : Val) (bs : List Bool) : IProp GF := iprop%
  ∃ (c : Loc) (p : ProphId) (vs : List (Val × Val)),
  ⌜cp = hl_val((#c, #p))⌝ ∗ ⌜bs ≠ []⌝ ∗ ⌜bs.tail = prophecyToListBool vs⌝ ∗
  proph p vs ∗ bs.head?.elim iprop(∃ (b : Bool), c ↦ hl_val(#b)) (fun b => iprop(c ↦ hl_val(#b)))

-- `@[rocq_alias heap_lang.new_coin_spec]` clashes with `lazy_coin.v`'s `new_coin_spec`.
theorem newCoin.spec :
    {{ True }} hl(&newCoin #()) {{ c bs, RET c; coin (GF := GF) c bs }} := by
  iunfold coin
  iintro %Φ - K
  unfold newCoin
  wp_pures
  wp_bind newProph()
  iapply wp_new_proph
  iintro %p %pvs Hp
  wp_bind &nondetBool _
  iapply nondetBool.spec $$ [//]
  iintro !> %b -
  wp_alloc c with Hc
  wp_pures
  iintro !>
  iapply K $$ %_ %(b :: prophecyToListBool pvs)
  iexists c, p, pvs
  isimp
  iframe

-- `@[rocq_alias heap_lang.read_coin_spec]` clashes with `lazy_coin.v`'s `read_coin_spec`.
theorem readCoin.spec (cp : Val) (bs : List Bool) :
    {{ coin (GF := GF) cp bs }} hl(&readCoin &cp)
    {{ (b : Bool) bs', RET hl_val(#b); ⌜bs = b :: bs'⌝ ∗ coin cp bs }} := by
  iunfold coin
  iintro %Φ ⟨%c, %p, %pvs, %cp_eq, %hne, %htl, Hp, Hb⟩ K
  subst cp_eq
  obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hne
  isimp at Hb
  unfold readCoin
  wp_pures
  wp_load
  iintro !>
  iapply K $$ %b %bs
  isplitr; itrivial
  iexists c, p, pvs
  isimp [htl]
  iframe

@[rocq_alias heap_lang.toss_coin_spec]
theorem tossCoin.spec (cp : Val) (bs : List Bool) :
    {{ coin (GF := GF) cp bs }} hl(&tossCoin &cp)
    {{ (b : Bool) bs', RET hl_val(#()); ⌜bs = b :: bs'⌝ ∗ coin cp bs' }} := by
  iunfold coin
  iintro %Φ ⟨%c, %p, %pvs, %cp_eq, %hne, %htl, Hp, Hb⟩ K
  subst cp_eq
  obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hne
  isimp at Hb
  unfold tossCoin
  wp_pures
  wp_bind &nondetBool _
  iapply nondetBool.spec $$ [//]
  iintro !> %r -
  wp_store
  wp_bind resolveProph(_, _)
  iapply wp_resolve_proph $$ Hp
  iintro %pvs' %rfl Hp
  simp only [List.tail_cons, prophecyToListBool_cons] at htl
  wp_pures
  iintro !>
  iapply K $$ %b %bs
  isplitr; itrivial
  iexists c, p, pvs'
  isimp [htl]
  iframe

end Proofs
