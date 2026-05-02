/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.HeapLang

@[expose] public section
namespace Iris.Tests.HeapLang

open Iris.HeapLang

section test

variable (v : Val)
/-- info: hl((#1 + (#1 + v(v)))) : Exp -/
#guard_msgs in
#check hl(#1 + #1 + {.val v})
/--
info: Exp.binop BinOp.plus (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1)))))
  (Exp.binop BinOp.plus (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1)))))
    (Exp.val v)) : Exp
-/
#guard_msgs in
set_option pp.explicit true in
#check hl(#1 + #1 + {.val v})
/-- info: hl((#1 + (#1 + v(v)))) : Exp -/
#guard_msgs in
#check hl(#1 + (#1 + v(v)))

/-- info: hl(((#1 + #1) + v(v))) : Exp -/
#guard_msgs in
#check hl((#1 + #1) + v(v))

/-- info: hl((#1 = (v + v(v)))) : Exp -/
#guard_msgs in
#check hl(#1 = v + v(v))
/--
info: Exp.binop BinOp.eq (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1)))))
  (Exp.binop BinOp.plus (Exp.var "v") (Exp.val v)) : Exp
-/
#guard_msgs in
set_option pp.explicit true in
#check hl(#1 = v + v(v))

/-- info: hl((λ x y z, #1)) : Exp -/
#guard_msgs in
#check hl(λ x y z, #1)

/-- info: hl_val(λ x y z, #1) : Val -/
#guard_msgs in
#check hl_val(λ x y z, #1)

/--
info: Exp.rec_ Binder.anon (Binder.named "x")
  (Exp.rec_ Binder.anon (Binder.named "y")
    (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1)))))) : Exp
-/
#guard_msgs in
set_option pp.explicit true in
#check hl(λ x y, #1)

/-- info: hl((rec f x := x) #1) : Exp -/
#guard_msgs in
#check hl((rec f x := x) #1)

/--
info: (Exp.rec_ (Binder.named "f") (Binder.named "x") (Exp.var "x")).app
  (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1))))) : Exp
-/
#guard_msgs in
set_option pp.explicit true in
#check hl((rec f x := x) #1)

/-- info: hl((λ x y, let z := #1; #2; (x + (y + z)))) : Exp -/
#guard_msgs in
#check hl(λ x y, let z := #1; #2; x + y + z)

/--
info: Exp.rec_ Binder.anon (Binder.named "x")
  (Exp.rec_ Binder.anon (Binder.named "y")
    ((Exp.rec_ Binder.anon (Binder.named "z")
          ((Exp.rec_ Binder.anon Binder.anon
                (Exp.binop BinOp.plus (Exp.var "x") (Exp.binop BinOp.plus (Exp.var "y") (Exp.var "z")))).app
            (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 2) (@instOfNatBaseLit (nat_lit 2))))))).app
      (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1))))))) : Exp
-/
#guard_msgs in
set_option pp.explicit true in
#check hl(λ x y, let z := #1; #2; x + y + z)

/--
info: hl((λ x y,
      ((((#1 + (#2 +ₗ (#3 - (#4 * (#5 / (#6 % #7)))))) & #8) | (#9 ^ (#10 <<< (#11 >>> #12)))) ≤
          (#13 ≤ (#14 < (#15 = (#16 + ((-#17) + (~#18))))))))) : Exp
-/
#guard_msgs in
#check hl(λ x y, #1 + #2 +ₗ #3 - #4 * #5 / #6 % #7 & #8 | #9 ^ #10 <<< #11 >>> #12 <= #13 ≤ #14 < #15 = #16 + (-#17) + (~#18))

/--
info: Exp.rec_ Binder.anon (Binder.named "x")
  (Exp.rec_ Binder.anon (Binder.named "y")
    (Exp.binop BinOp.le
      (Exp.binop BinOp.or
        (Exp.binop BinOp.and
          (Exp.binop BinOp.plus (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1)))))
            (Exp.binop BinOp.offset
              (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 2) (@instOfNatBaseLit (nat_lit 2)))))
              (Exp.binop BinOp.minus
                (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 3) (@instOfNatBaseLit (nat_lit 3)))))
                (Exp.binop BinOp.mult
                  (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 4) (@instOfNatBaseLit (nat_lit 4)))))
                  (Exp.binop BinOp.tdiv
                    (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 5) (@instOfNatBaseLit (nat_lit 5)))))
                    (Exp.binop BinOp.tmod
                      (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 6) (@instOfNatBaseLit (nat_lit 6)))))
                      (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 7) (@instOfNatBaseLit (nat_lit 7)))))))))))
          (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 8) (@instOfNatBaseLit (nat_lit 8))))))
        (Exp.binop BinOp.xor (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 9) (@instOfNatBaseLit (nat_lit 9)))))
          (Exp.binop BinOp.shiftl
            (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 10) (@instOfNatBaseLit (nat_lit 10)))))
            (Exp.binop BinOp.shiftr
              (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 11) (@instOfNatBaseLit (nat_lit 11)))))
              (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 12) (@instOfNatBaseLit (nat_lit 12)))))))))
      (Exp.binop BinOp.le (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 13) (@instOfNatBaseLit (nat_lit 13)))))
        (Exp.binop BinOp.lt (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 14) (@instOfNatBaseLit (nat_lit 14)))))
          (Exp.binop BinOp.eq (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 15) (@instOfNatBaseLit (nat_lit 15)))))
            (Exp.binop BinOp.plus
              (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 16) (@instOfNatBaseLit (nat_lit 16)))))
              (Exp.binop BinOp.plus
                (Exp.unop UnOp.minus
                  (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 17) (@instOfNatBaseLit (nat_lit 17))))))
                (Exp.unop UnOp.neg
                  (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 18) (@instOfNatBaseLit (nat_lit 18))))))))))))) : Exp
-/
#guard_msgs in
set_option pp.explicit true in
#check hl(λ x y, #1 + #2 +ₗ #3 - #4 * #5 / #6 % #7 & #8 | #9 ^ #10 <<< #11 >>> #12 <= #13 ≤ #14 < #15 = #16 + (-#17) + (~#18))

/--
info: Exp.binop BinOp.shiftl (Exp.var "x").load
  (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1))))) : Exp
-/
#guard_msgs in
set_option pp.explicit true in
#check hl(!x <<< #1)

/-- info: hl(if #1 then #2 else #3) : Exp -/
#guard_msgs in
#check hl(if #1 then #2 else #3)

/--
info: hl(if if a then b else #(BaseLit.bool false) then #(BaseLit.bool true) else
    if c then d else #(BaseLit.bool false)) : Exp
-/
#guard_msgs in
#check hl(a && b || c && d)

/-- info: hl((#1, #2, #3)) : Exp -/
#guard_msgs in
#check hl((#1, #2, #3))

/--
info: (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1))))).pair
  ((Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 2) (@instOfNatBaseLit (nat_lit 2))))).pair
    (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 3) (@instOfNatBaseLit (nat_lit 3)))))) : Exp
-/
#guard_msgs in
set_option pp.explicit true in
#check hl((#1, #2, #3))

/-- info: hl_val((#1, #BaseLit.unit, #(BaseLit.bool true), #(BaseLit.int (-1)))) : Val -/
#guard_msgs in
#check hl_val((#1, #(), #true, #(.int (-1))))

/--
info: (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1)))).pair
  ((Val.lit (@OfNat.ofNat BaseLit (nat_lit 2) (@instOfNatBaseLit (nat_lit 2)))).pair
    (Val.lit (@OfNat.ofNat BaseLit (nat_lit 3) (@instOfNatBaseLit (nat_lit 3))))) : Val
-/
#guard_msgs in
set_option pp.explicit true in
#check hl_val((#1, #2, #3))

/-- info: hl(fst(snd((#1, #2, #3)))) : Exp -/
#guard_msgs in
#check hl(fst(snd((#1, #2, #3))))

/-- info: hl(match injl(injr(#1)) with | injl(_) => #1 | injr(y) => #2) : Exp -/
#guard_msgs in
#check hl(match injl(injr(#1)) with | injl(_) => #1 | injr(y) => #2)

/-- info: hl(match injl(injr(#1)) with | injl(y) => #2 | injr(_) => #1) : Exp -/
#guard_msgs in
#check hl(match injl(injr(#1)) with | injr(_) => #1 | injl(y) => #2)

/-- info: hl(match injr(injl(#BaseLit.unit)) with | injl(_) => #2 | injr(_) => #1) : Exp -/
#guard_msgs in
#check hl(match some(none()) with | some(_) => #1 | none() => #2)

/-- info: hl(match injr(injl(#BaseLit.unit)) with | injl(_) => #1 | injr(x) => #2) : Exp -/
#guard_msgs in
#check hl(match some(none()) with | none() => #1 | some(x) => #2)

/-- info: hl_val(injl(injr(#1))) : Val -/
#guard_msgs in
#check hl_val(injl(injr(#1)))

/-- info: hl_val(injr(injl(#BaseLit.unit))) : Val -/
#guard_msgs in
#check hl_val(some(none()))


/--
info: hl(let x := ref(#0);
    let y := allocn(!x, #0);
      x ← (!x + #1);
        fork(cmpXchg(x, #1, #2); snd(cmpXchg(x, #1, #2)); xchg(x, #2); faa(x, #4)); assert((!x = #0)); free(x)) : Exp
-/
#guard_msgs in
#check hl(let x := ref(#0); let y := allocn(!x, #0); x ← !x + #1; fork(cmpXchg(x, #1, #2); cas(x, #1, #2); xchg(x, #2); faa(x, #4)); assert(!x = #0); free(x))

/--
info: (Exp.rec_ Binder.anon (Binder.named "x")
      ((Exp.rec_ Binder.anon (Binder.named "y")
            ((Exp.rec_ Binder.anon Binder.anon
                  ((Exp.rec_ Binder.anon Binder.anon
                        ((Exp.rec_ Binder.anon Binder.anon (Exp.var "x").free).app
                          (Exp.binop BinOp.eq (Exp.var "x").load
                              (Exp.val
                                (Val.lit
                                  (@OfNat.ofNat BaseLit (nat_lit 0) (@instOfNatBaseLit (nat_lit 0)))))).assert)).app
                    ((Exp.rec_ Binder.anon Binder.anon
                            ((Exp.rec_ Binder.anon Binder.anon
                                  ((Exp.var "x").faa
                                    (Exp.val
                                      (Val.lit
                                        (@OfNat.ofNat BaseLit (nat_lit 4) (@instOfNatBaseLit (nat_lit 4))))))).app
                              ((Exp.var "x").xchg
                                (Exp.val
                                  (Val.lit (@OfNat.ofNat BaseLit (nat_lit 2) (@instOfNatBaseLit (nat_lit 2)))))))).app
                        ((Exp.var "x").cmpXchg
                          (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1)))))
                          (Exp.val
                            (Val.lit (@OfNat.ofNat BaseLit (nat_lit 2) (@instOfNatBaseLit (nat_lit 2))))))).fork)).app
              ((Exp.var "x").store
                (Exp.binop BinOp.plus (Exp.var "x").load
                  (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1))))))))).app
        ((Exp.var "x").load.allocN
          (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 0) (@instOfNatBaseLit (nat_lit 0)))))))).app
  ((Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 1) (@instOfNatBaseLit (nat_lit 1))))).allocN
    (Exp.val (Val.lit (@OfNat.ofNat BaseLit (nat_lit 0) (@instOfNatBaseLit (nat_lit 0)))))) : Exp
-/
#guard_msgs in
set_option pp.explicit true in
#check hl(let x := ref(#0); let y := allocn(!x, #0); x ← !x + #1; fork(cmpXchg(x, #1, #2); xchg(x, #2); faa(x, #4)); assert(!x = #0); free(x))

end test

end Iris.Tests.HeapLang
