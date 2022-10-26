import Lean.PrettyPrinter.Delaborator

namespace Iris.BI
open Lean Lean.Macro

-- define `iprop` embedding in `term`
syntax:max "`[iprop| " term "]" : term
syntax:max "`[term| " term "]" : term

-- allow fallback to `term`
macro_rules
  | `(`[iprop| `[term| $t]]) => ``($t)
  | `(`[iprop| $t])          => ``($t)

-- carry `iprop` over some `term` constructs
macro_rules
  | `(`[iprop| ($P)])                  => ``((`[iprop| $P]))
  | `(`[iprop| $P $[ $Q]*])            => ``(`[iprop| $P] $[ `[iprop| $Q]]*)
  | `(`[iprop| if $c then $t else $e]) => ``(if $c then `[iprop| $t] else `[iprop| $e])
  | `(`[iprop| ($P : $t)])             => ``((`[iprop| $P] : $t))

/-- Remove an `iprop` quotation from a `term` syntax object. -/
partial def unpackIprop [Monad m] [MonadRef m] [MonadQuotation m] : TSyntax `term → m (TSyntax `term)
  | `(`[iprop| $P])          => ``($P)
  | `($P:ident)              => ``($P)
  | `(($P))                  => do ``(($(← unpackIprop P)))
  | `($P $[ $Q]*)            => do ``($(← unpackIprop P) $[ $(← Q.mapM unpackIprop)]*)
  | `(if $c then $t else $e) => do ``(if $c then $(← unpackIprop t) else $(← unpackIprop e))
  | `(($P : $t))             => do ``(($(← unpackIprop P) : $t))
  | `(`[term| $t])           => ``(`[term| $t])
  | `($t)                    => ``(`[term| $t])

-- macro for adding unexpanders for function applications
open Lean.Parser.Term in
private def matchAlts' := leading_parser matchAlts

syntax "delab_rule" ident matchAlts' : command
macro_rules
  | `(delab_rule $f $[| $p => $s]*) => do
    let f := f.getId
    if f.isAnonymous then
      throwUnsupported
    let f ← match ← Macro.resolveGlobalName f with
      | [(name, [])] => pure name
      | _           => throwUnsupported

    let (p : TSyntaxArray `term) := p
    if p.any (· matches `(`($$_))) then
      `(@[appUnexpander $(mkIdent f)]
        def unexpand : Lean.PrettyPrinter.Unexpander
          $[| $p => $s]*)
    else
      `(@[appUnexpander $(mkIdent f)]
        def unexpand : Lean.PrettyPrinter.Unexpander
          $[| $p => $s]*
          | _ => throw ())

end Iris.BI
