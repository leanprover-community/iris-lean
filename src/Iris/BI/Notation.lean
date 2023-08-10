/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Lean.PrettyPrinter.Delaborator

namespace Iris.BI
open Lean Lean.Macro

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
  | `(iprop($P $[ $Q]*))            => ``($P $[ $Q]*)
  | `(iprop(if $c then $t else $e)) => ``(if $c then iprop($t) else iprop($e))
  | `(iprop(($P : $t)))             => ``((iprop($P) : $t))

/-- Remove an `iprop` quotation from a `term` syntax object. -/
partial def unpackIprop [Monad m] [MonadRef m] [MonadQuotation m] : Term → m Term
  | `(iprop($P))             => do `($P)
  | `($P:ident)              => do `($P)
  | `(?$P:ident)             => do `(?$P)
  | `(($P))                  => do `(($(← unpackIprop P)))
  | `($P $[ $Q]*)            => do ``($P $[ $Q]*)
  | `(if $c then $t else $e) => do `(if $c then $(← unpackIprop t) else $(← unpackIprop e))
  | `(($P : $t))             => do ``(($(← unpackIprop P) : $t))
  | `($t)                    => `($t:term)

end Iris.BI
