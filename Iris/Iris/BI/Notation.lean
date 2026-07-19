/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Alex Keizer
-/
module

public meta import Lean.PrettyPrinter.Delaborator

meta import Lean.Parser.Term

public meta section

namespace Iris.BI
open Lean Lean.Macro Lean.Parser.Term

-- define `iprop` embedding in `term`
syntax:max "iprop(" term ")" : term
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
          | alt => return ⟨alt⟩
        `(match $[$g:generalizingParam]? $[$m:motive]? $[$x:matchDiscr],* with $[$alts:matchAlt]*)

macro:max "iprop(" P:term " : " t:term ")" : term => `((iprop($P) : $t))

-- paren-less form: eats the rest of the term at minimum precedence
syntax:min "iprop% " term:min : term
macro_rules
  | `(iprop% $t) => `(iprop($t))

/-- Remove an `iprop` quotation from a `term` syntax object. -/
partial def unpackIprop [Monad m] [MonadRef m] [MonadQuotation m] : Term → m Term
  | `(iprop($P))             => do `($P)
  | `($P:ident)              => do `($P)
  | `(?$P:ident)             => do `(?$P)
  | `(($P))                  => do `(($(← unpackIprop P)))
  | `($P $[ $Q]*)            => do ``($P $[ $Q]*)
  | `(if $c then $t else $e) => do
    let t ← unpackIprop t
    let e ← unpackIprop e
    `(if $c then $t else $e)
  | `(($P : $t))             => do ``(($(← unpackIprop P) : $t))
  | `($t)                    => `($t:term)
  | `(match $[$g:generalizingParam]? $[$mot:motive]? $[$x:matchDiscr],* with $[$alts:matchAlt]*) => do
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

end Iris.BI
