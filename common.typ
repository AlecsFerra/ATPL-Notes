
#let True = "true"
#let False = "false"
#let unit = "unit"
#let app = " "
#let fn = "fn"
#let mif = "if"
#let then = "then"
#let melse = "else"
#let mtrue = "true"
#let mfalse = "false"
#let match = "match"
#let case = "case"
#let default = "default"
#let try = "try"
#let throw = "throw"
#let catch = "catch"
#let even = "even"
#let print = "print"
#let exn = "exn"
#let Types = "Types"
#let Bool = "Bool"
#let Nat = "Nat"

#let jud(ctx: $Gamma$, term, ty) = [
    $#ctx tack.r #term : #ty$
]

#let invlemma(ctx: $Gamma$, term, ty, ..consequences) = [
    If #jud(ctx: ctx, term, ty) is derivable, then #consequences.pos().join(" and ").
]

#let canon(ty, conclusion) = [
    If $v$ is a value and #jud(ctx: $nothing$, $v$, ty) then $v$ is #conclusion.
]
