/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Alex Keizer, Alvin Tang
-/
module

import Lean.Parser.Term
public meta import Iris.Std.DelabRule
public import Iris.Init

public meta section

namespace Iris.BI
open Lean Lean.Parser.Term PrettyPrinter Delaborator

/- `iprop(P)` embeds a separation logic proposition `P` into `term`. -/
syntax:max (name := iprop) "iprop(" term ")" : term
/- `term(t)` escapes from an `iprop(…)` embedding. -/
syntax:max "term(" term ")" : term

-- allow fallback to `term`
macro_rules
  | `(iprop(term($t))) => pure t
  | `(iprop($t))       => pure t

-- carry `iprop` over some `term` constructs
macro_rules
  | `(iprop(($P)))                  => ``((iprop($P)))
  | `(iprop(if $c then $t else $e)) => ``(if $c then iprop($t) else iprop($e))
  | `(iprop(($P : $t)))             => ``((iprop($P) : $t))
  | `(iprop(fun $xs* => $P))        => ``(fun $xs* => iprop($P))
  -- `iprop(match …)` expansion wraps the rhs of each match arm in `iprop(…)`
  | `(iprop(match $[$g:generalizingParam]? $[$m:motive]? $[$x:matchDiscr],* with
              $[$alts:matchAlt]*)) => do
        let alts ← alts.mapM <| fun
          | `(matchAltExpr| | $[$lhs]|* => $rhs) => `(matchAltExpr| | $[$lhs]|* => iprop($rhs))
          | _ => Macro.throwUnsupported
        `(match $[$g:generalizingParam]? $[$m:motive]? $[$x:matchDiscr],* with $[$alts:matchAlt]*)

macro:max "iprop(" P:term " : " t:term ")" : term => `((iprop($P) : $t))

/--
  `iprop% P` is `iprop(P)` without parentheses; it consumes the remainder of
  the term at minimum precedence.
-/
syntax:min "iprop% " term:min : term
macro_rules
  | `(iprop% $t) => `(iprop($t))

/-- Used by macro elaboration rules for linking source information to connectives. -/
meta def wrapIprop (tk : Syntax) (c : Name) : Ident :=
  mkCIdentFrom tk c (canonical := true)

/-- A variant of `wrapIprop` where the operator spans over two tokens (e.g. `⌜·⌝`). -/
meta def wrapIpropSpan (tk1 tk2 : Syntax) (c : Name) : Ident :=
  match tk1.getPos?, tk2.getTailPos? with
  | some pos, some endPos => ⟨(mkCIdent c).raw.setInfo (.synthetic pos endPos (canonical := true))⟩
  | none, _ => wrapIprop tk2 c
  | _, none => wrapIprop tk1 c

/-- Retain the syntax source information for correct delaboration. -/
def keepInfo (src : Syntax) (t : Term) : Term :=
  match src.getHeadInfo with
  | info@(.synthetic ..) => ⟨t.raw.setInfo info⟩
  | _                    => t

/-- Remove an `iprop` quotation from a `term` syntax object. -/
partial def unpackIprop [Monad m] [MonadRef m] [MonadQuotation m] (stx : Term) : m Term := do
  match stx with
  | `(iprop($P))             => return keepInfo stx (← `($P))
  | `($P:ident)              => `($P)
  | `(?$P:ident)             => `(?$P)
  | `(($P))                  => return keepInfo stx (← `(($(← unpackIprop P))))
  | `($P $[ $Q]*)            => return keepInfo stx (← ``($P $[ $Q]*))
  | `(if $c then $t else $e) =>
    let t ← unpackIprop t
    let e ← unpackIprop e
    `(if $c then $t else $e)
  | `(($P : $t))             => ``(($(← unpackIprop P) : $t))
  | `(match $[$g:generalizingParam]? $[$mot:motive]? $[$x:matchDiscr],* with $[$alts:matchAlt]*) =>
      -- The following type ascriptions look redundant, but, without them, the ``(match ...)`
      -- syntax quotation below fails with an error about types containing metavariables.
      let g : Option (TSyntax ``generalizingParam) := g
      let mot : Option (TSyntax ``motive) := mot
      let alts ← Array.mapM (as := alts) (m:=m) <| fun
        | `(matchAltExpr| | $[$lhs]|* => $rhs) => do
            let rhs ← unpackIprop rhs
            `(matchAltExpr| | $[$lhs]|* => $rhs)
        | alt => return ⟨alt⟩
      `(match $[$g:generalizingParam]? $[$mot:motive]? $[$x:matchDiscr],* with $[$alts:matchAlt]*)
  -- Fallback case
  | `($t)                    => `($t:term)

end Iris.BI
