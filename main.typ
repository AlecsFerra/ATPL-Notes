#import "common.typ": *
#import "typst-prooftree/prooftree.typ": *


= ATPL Notes

== Base

=== Terms
$
M :: & = && x \
     & | && n \
     & | && mtrue \
     & | && mfalse \
     & | && M + M \
     & | && mif M then M melse M \
     & | && fn x : T . M \
     & | && M M
$

=== Types
$
Types T :: & = && Bool \
           & | && Nat \
           & | && T -> T \
$

=== Substitution
$
x & {x := N} = N\
y & {x := N} = y\
n & {x := N} = n\
True & {x := N} = True\
False & {x := N} = False\
M_1 + M_2 & {x := N} = M_1{x := N} + M_2{x := N}\
mif M_1 then M_2 melse M_3 & {x := N} = mif M_1{x := N} then
    M_2{x := N} melse M_3 {x := N}\
(fn y : T M) & {x := N} = fn y : T . M {x := N} mif y in.not "fv"(N) \
(M_1 M_2) & {x := N} = M_1 {x := N} M_2 {x := N}
$

=== Values
$
"Values" v :: & = && n \
              & | && mtrue \
              & | && mfalse \
              & | && fn x : T . M \
$

=== Operational Semantics
#align(center)[
    #box(prooftree(
        label-side: right,
        axiom("(Sum)"),
        rule(label: $n = n_1 +_bb(N) n_2$, $n_1 + n_2 -> n$)
    ))
    #box(prooftree(
        axiom($M -> M'$),
        rule(label: "(Sum left)", $M + N -> M' + N$)
    ))
    #box(prooftree(
        axiom($M -> M'$),
        rule(label: "(Sum right)", $v + M -> v + M'$)
    ))
]

#align(center)[
    #box(prooftree(
        axiom("(If-true)"),
        rule($mif mtrue then M melse N -> M$)
    ))
    #box(prooftree(
        axiom("(If-false)"),
        rule($mif mfalse then M melse N -> N$)
    ))
]

#align(center)[
    #box(prooftree(
        axiom($M_1 -> M_1'$),
        rule($mif M_1 then M_2 melse M_3 -> mif M_1'
             then M_2 melse M_3$, label: "(If)")
    ))
]

#align(center)[
    #box(prooftree(
        axiom("(Beta)"),
        rule($(fn x : T . M) v -> M{x := v}$)
    ))
    #box(prooftree(
        axiom($M -> M'$),
        rule(label: "(App 1)", $M N -> M' N$)
    ))
    #box(prooftree(
        axiom($M -> M'$),
        rule(label: "(App 2)", $v M -> v M'$)
    ))
]

=== Typing
#align(center)[
    #box(prooftree(
        axiom("(T-True)"),
        rule(jud(mtrue, Bool))
    ))
    #box(prooftree(
        axiom("(T-False)"),
        rule(jud(mfalse, Bool))
    ))
    #box(prooftree(
        axiom("(T-Int)"),
        rule(jud($n$, Nat))
    ))
    #box(prooftree(
        label-side: right,
        axiom("(T-var)"),
        rule(label: $x : T in Gamma$, jud($x$, $T$))
    ))
]

#align(center)[
    #box(prooftree(
        axiom(jud($M$, $Nat$)),
        axiom(jud($N$, $Nat$)),
        rule(n:2, jud($M + N$, $Nat$), label: "(T-Sum)")
    ))
    #box(prooftree(
        axiom(jud($M_1$, $Bool$)),
        axiom(jud($M_2$, $T$)),
        axiom(jud($M_3$, $T$)),
        rule(n:3, jud($mif M_1 then M_2 melse M_3$, $T$), label: "(T-IfThenElse)")
    ))
]

#align(center)[
    #box(prooftree(
        axiom(jud(ctx: $Gamma, x: T_1$, $M$, $T_2$)),
        rule(jud($fn x : T_1 . M$, $T_1 -> T_2$), label: "(T-Fun)")
    ))
    #box(prooftree(
        axiom(jud($N$, $T_1 -> T_2$)),
        axiom(jud($N$, $T_1$)),
        rule(n: 2, jud($M N$, $T_2$), label: "(T-App)")
    ))
]

== Unit

=== Terms
$
M :: & = && .. \
     & | && unit
$

=== Types
$
Types T :: & = && ... \
           & | && unit
$

=== Substitution
$
unit & {x := N} = unit
$

=== Values
$
"Values" v :: & = && ... \
              & | && unit
$

=== Operational Semantics

=== Typing
#align(center)[
    #box(prooftree(
        axiom("(T-unit)"),
        rule(jud(unit, unit))
    ))
]

== Pairs
=== Terms
$
M :: & = && ... \
     & | && (M , M) \
     & | && M.\_1 \
     & | && M.\_2
$

=== Types
$
Types T :: & = && ... \
           & | && T * T
$

=== Substitution
$
(M_1 , M_ 2) & {x := N} = (M_1 {x:=N} , M_2 {x := N})
$

=== Values
$
"Values" v :: & = && ... \
              & | && (v, v)
$

=== Operational Semantics
#align(center)[
    #box(prooftree(
        axiom("(Pair 1)"),
        rule($(v_1 , v_2).\_1 -> v_1$)
    ))
    #box(prooftree(
        axiom("(Pair 2)"),
        rule($(v_1 , v_2).\_2 -> v_2$)
    ))
    #box(prooftree(
        axiom($M -> M'$),
        rule($M.\_1 -> M'.\_1$, label: "Project 1")
    ))
    #box(prooftree(
        axiom($M -> M'$),
        rule($M.\_2 -> M'.\_2$, label: "Project 2")
    ))
]

#align(center)[
    #box(prooftree(
        axiom($M_1 -> M_1'$),
        rule($(M_1 , M_2) -> (M_1', M_2)$, label: "Eval Pair 1")
    ))
    #box(prooftree(
        axiom($M_2 -> M_2'$),
        rule($(v_1 , M_2) -> (v_1, M_2')$, label: "Eval Pair 2")
    ))
]
=== Typing
#align(center)[
    #box(prooftree(
        axiom(jud($M_1$, $T_1$)),
        axiom(jud($M_2$, $T_2$)),
        rule(n: 2, jud($(M_1, M_2)$, $T_1 * T_2$), label: "(T-Pair)")
    ))
    #box(prooftree(
        axiom(jud($M$, $T_1 * T_2$)),
        rule(jud($M.\_1$, $T_1$), label: "(T-Project 1)")
    ))
    #box(prooftree(
        axiom(jud($M$, $T_1 * T_2$)),
        rule(jud($M.\_2$, $T_2$), label: "(T-Project 2)")
    ))
]

== Records
=== Terms
$
M :: & = && ... \
     & | && {l_i = M_i^(#h(5pt) i in 1..n)} \
     & | && M.l
$

=== Types
$
Types T :: & = && ... \
           & | &&  { l_i : T_i ^(#h(5pt) i in 1..n) }
$

=== Substitution
$
{ l_i = M_i ^(#h(5pt) i in 1..n) }& {x := N}
  = { l_i = M_i {x := N} ^(#h(5pt) i in 1..n) }
$

=== Values
$
"Values" v :: & = && ... \
              & | && {l_i = v_i ^(#h(5pt) i in 1..n)}
$

=== Operational Semantics
#align(center)[
    #box(prooftree(
        label-align: right,
        axiom("(Select)"),
        rule(label: $j in 1..n$, ${l_i = v_i^(#h(5pt) i in 1..n)}.l_j -> v_j$)
    ))
    #box(prooftree(
        axiom($M -> M'$),
        rule(label: "(Eval Select)", $M.l -> M'.l$)
    ))
]

#align(center)[
    #box(prooftree(
        axiom($M_j -> M_j'$),
        rule(${l_i = v_i^(#h(5pt) i in 1..j-1),
               l_j = M_j,
               l_k = M_k^(#h(5pt) i in j+1..n)}
              ->
              {l_i = v_i^(#h(5pt) i in 1..j-1),
              l_j = M_J',
              l_k = M_k^(#h(5pt) i in j+1..n)}$,
            label: "Eval Record")
    ))
]
=== Typing
#align(center)[
    #box(prooftree(
        axiom($forall i in 1..n quad #jud($M_i$, $T_i$)$),
        rule(jud(${l_i = M_i^(#h(5pt) i in 1..n)}$,
                 ${l_i : T_i^(#h(5pt) i in 1..n)}$),
            label: "(Type Record)")
    ))
    #box(prooftree(
        axiom(jud($M$,
                  ${l_i : T_i^(#h(5pt) i in 1..n)}$)),
        rule(jud($M.l_j$, $T_j$),
            label: "(Select)")
    ))
]

== Variant
=== Terms
$
M :: & = && ... \
     & | && angle.l l = M angle.r \
     & | && M match { case l_i = x_i => M_i ^(#h(5pt) i in 1..n) }
$

=== Types
$
Types T :: & = && ... \
           & | &&  angle.l l_i : T_i^(#h(5pt) i in 1..n) angle.r
$

=== Substitution
$
angle.l l = M angle.r & {x := N} = angle.l l = M {x := N} angle.r \
M match { case l_i = x_i => M_i ^(#h(5pt) i in 1..n) } & {x := M}
  = M {x := N} match { case l_i = x_i => M_i {x := N} ^(#h(5pt) i in 1..n) }
  " where " x eq.not x_i
$

=== Values
$
"Values" v :: & = && ... \
              & | && angle.l l = v angle.r
$

=== Operational Semantics
#align(center)[
    #box(prooftree(
        label-align: right,
        axiom("(Match)"),
        rule(label: $j in 1..n$, $
          angle.l l_j = v_j angle.r match { case l_i = x_i =>
                                            M_i ^(#h(5pt) i in 1..n) }
          ->
          M_j {x_i := v_j}
        $)
    ))
    #box(prooftree(
        axiom($M -> M'$),
        rule(label: "(Red Match)", $
          M match { case l_i = x_i =>
                    M_i ^(#h(5pt) i in 1..n) }
          ->
          M' match { case l_i = x_i =>
                     M_i ^(#h(5pt) i in 1..n) }
        $)
    ))
    #box(prooftree(
        axiom($M -> M'$),
        rule(label: "(Variant)", $angle.l l = M angle.r -> angle.l l = M' angle.r$)
    ))
]

=== Typing
#align(center)[
    #box(prooftree(
      axiom(jud($M$, $T_j$)),
      rule(label: "(Type variant) " + $j in 1..n$,
           jud($angle.l l_j = M angle.r$,
               $angle.l l_i : T_i ^(#h(5pt) i in 1..n) angle.r$))
    ))
    #box(prooftree(
      axiom(jud($M$, $angle.l l_i : T_i ^(#h(5pt) i in 1..n) angle.r$)),
      axiom(jud($M$, $forall i in 1..n quad #jud(ctx: $Gamma, x_i : T_i$,
                                                 $M_i$, $T$)$)),
      rule(n: 2, label: "(Type match)",
           jud($M match { case l_i = x_i => M_i ^(#h(5pt) i in 1..n) }$,
               $T$)
      )
    ))
]

== Subtyping
#align(center)[
    #box(prooftree(
      axiom(jud($M$, $S$)),
      axiom($S <: T$),
      rule(n: 2, label: "(Subsumption)", jud($M$, $T$))
    ))
]

#align(center)[
    #box(prooftree(
      axiom("(Reflex)"),
      rule($T <: T$)
    ))
    #box(prooftree(
      axiom($S <: U$),
      axiom($U <: T$),
      rule(n: 2, label: "(Trans)", $S <: T$)
    ))
]

=== Records
#align(center)[
    #box(prooftree(
      axiom("(Sub Width)"),
      rule(${l_i : T_i^(#h(5pt) i in I union I')} <: {l_i : T_i^(#h(5pt) i in I)}$)
    ))
    #box(prooftree(
      axiom($S_i <: T_i quad forall i in I$),
      rule(label: "(Sub Depth)", ${l_i : S_i^(#h(5pt) i in I)}
                                 <:
                                 {l_i : T_i^(#h(5pt) i in I)}$)
    ))
]

=== Arrows
#align(center)[
    #box(prooftree(
      axiom($T_1 <: S_2$),
      axiom($S_2 <: T_1$),
      rule(n: 2, label: "(Arrow)", $S_1 -> S_2 <: T_1 <: T_2$)
    ))
]

== Exceptions

=== Operational semantics

#align(center)[
    #box(prooftree(
      axiom($M -> M'$),
      rule(label: "(Try)", $try M catch N -> try M' catch N$)
    ))
    #box(prooftree(
      axiom(""),
      rule(label: "  (Try Handle)", $try throw v catch M -> M app v$)
    ))
    #box(prooftree(
      axiom(""),
      rule(label: "(Try Val)", $try v catch M -> v$)
    ))

    #box(prooftree(
      axiom($M -> M'$),
      rule(label: "(Raise 1)", $throw M -> throw M'$)
    ))
    #box(prooftree(
      axiom(""),
      rule(label: "  (Raise 2)", $throw (throw v) -> throw v$)
    ))
    #box(prooftree(
      axiom(""),
      rule(label: "(Raise App 1)", $(throw v) app M -> throw v$)
    ))
    #box(prooftree(
      axiom(""),
      rule(label: "  (Raise App 2)", $v_1 app (throw v_2) -> throw v_2$)
    ))
    #box(prooftree(
      axiom(""),
      rule(label: "(Raise IfElse)", $mif throw v then M melse N -> throw v$)
    ))

    #box(prooftree(
      axiom(""),
      rule(label: "(Raise Sum 1)", $throw v + M -> throw v$)
    ))
    #box(prooftree(
      axiom(""),
      rule(label: "  (Raise Sum 2)", $v_1 + throw v_2 -> throw v_2$)
    ))
]

=== Typing
#align(center)[
    #box(prooftree(
      axiom($Gamma tack.r M : T_exn$),
      rule(label: "(T-Raise)", $Gamma tack.r throw M : T$)
    ))

    #box(prooftree(
      axiom($Gamma tack.r M : T$),
      axiom($Gamma tack.r N : T_exn -> T$),
      rule(n:2, label: "(T-Try)", $Gamma tack.r try M catch N : T$)
    ))
]

== Definitions and stuff

- *$alpha$ equivalence*: Terms that differ only in the names of bound
variables are interchangeable in any context.

== Theorems for the base language

=== Inversion of typing
- #invlemma(mtrue, $T$, $T = Bool$)
- #invlemma(mfalse, $T$, $T = Bool$)
- #invlemma($n$, $T$, $T = Nat$)
- #invlemma($M + N$, $T$, $T = Nat$,
            jud($M$, Nat) + "is derivable", jud($N$, Nat) + "is derivable")
- #invlemma($mif M_1 then M_2 melse M_3$, $T$,
            jud($M_1$, Bool) + "is derivable", jud($M_2$, $T$) + "is derivable",
            jud($M_3$, $T$) + "is derivable")
- #invlemma($x$, $T$, $x : T in Gamma$)
- #invlemma($fn x : T_1 . M$, $T$,
            $exists T_2$ + " such that " + $T = T_1 -> T_2$,
            jud(ctx: $Gamma, x : T_1$, $M$, $T_2$) + "is derivable")
- #invlemma($M N$, $T$,
            $exists T_1$ + " such that " + jud($M$, $T_1 -> T$) + "is derivable",
            jud($N$, $T_1$) + "is derivable")

*Proof.* Immediate, observing that the typing rules are defined so that
for each term there is at most a single rule that applies, that is the
typing rules are _syntax-directed_.

=== Unicity of typing
If #jud($M$, $T_1$) is derivable and #jud($M$, $T_2$) is derivable
then $T_1 = T_2$.

=== Canonical forms
- #canon(Bool, "either " + $mtrue$ + " or " + $mfalse$)
- #canon(Nat, "an integer constant " + $n$)
- #canon($T_1 -> T_2$, $fn x : T_1 . M$)

*Proof.* Immediate.

=== Progress
Let $M$ be a closed and well-typed term, then either $M$ is a value
or $exists M'$ s.t. $M -> M'$.

*Proof.*
We proceed by induction on the height of the derivation
#jud(ctx: $nothing$, $M$, $T$).

Base cases:

We distinguis on the possible base cases, so on the axioms:
- (T-True) Then it must be that $M = mtrue$ and it's a value.
- (T-False) Then it must be that $M = mfalse$ and it's a value.
- (T-Nat) Then it must be that $M = n$ and it's a value.
- (T-Var) Then it must be that $M = x$ but this case it's impossible since
  $x : T in.not nothing$.

Inductive cases:

Let #jud(ctx: $nothing$, $M$, $T$) with derivation height $k + 1$,
we proceed by case analysis on the last rule applied in the derivation:
- (T-Sum) Then it must be that $M = M_1 + M_2$ thus the conclusion of the rule
  must be #jud(ctx: $nothing$, $M_1 + M_2$, $T$), by inversion lemma then
  we also know that $T = Nat$, #jud(ctx: $nothing$, $M_1$, Nat) and
  #jud(ctx: $nothing$, $M_2$, Nat) are derivable both with height $<= k$.
  We can apply on both of the derivation the inductive hypothesis and perform
  a case analysis on both the results:
    - $M_1 = v_1$ and $M_2 = v_2$ then we can apply the rule (Sum) and
      obtain $M_1 + M_2 -> m$ where $m = v_1 +_(NN) v_2$.
    - $M_1 = v_1$ and $M_2 -> M_2$ then we can apply the rule (Sum Right) and
      obtain that $M_1 + M_2 -> v_1 + M_2'$.
    - $M_1 -> M_1'$ then we can apply the rule (Sum Left) and obtain that
      $M_1 + M_2 -> M_1' + M_2$.

- (T-IfThenElse) Then it must be that $M = mif M_1 then M_2 melse M_3$ thus
  the conclusion of the rule must be
  #jud(ctx: $nothing$, $mif M_1 then M_2 melse M_3$, $T$), by inversion lemma
  we also know that #jud(ctx: $nothing$, $M_1$, Bool),
  #jud(ctx: $nothing$, $M_2$, $T$) and #jud(ctx: $nothing$, $M_3$, $T$) are
  derivable all with height $<= k$. We can apply the inductive hypothesis on
  the first judgment and perform a case analysis:
  - $M_1 -> M_1'$ then we can apply the rule (If) and obtain
    $mif M_1 then M_2 melse M_3 -> mif M_1' then M_2 melse M_3$.
  - $M_1 = v_1$ we have that #jud(ctx: $nothing$, $v_1$, $Bool$) and by canonical
    form lemma:
    - $m_1 = mtrue$ then we can apply the rule (If-True) and obtain that
      $mif mtrue then M_2 melse M_3 -> M_2$.
    - $m_1 = mfalse$ then we can apply the rule (If-False) and obtain that
      $mif mfalse then M_2 melse M_3 -> M_3$.

- (T-Fun) Then it must be that $M = fn x : T . M_1$ and it's a value.

- (T-App) Then it must be that $M = M_1 M_2$ thus the conclusion rule must be
  #jud(ctx: $nothing$, $M_1 M_2$, $T$), by inversion lemma we also know that
  #jud(ctx: $nothing$, $M_1$, $T_1 -> T$) and #jud(ctx: $nothing$, $M_2$, $T_1$)
  are derivable with height $<= k$ we can apply the inductive hypothesis on both
  of the judgments and perform a case analysis:
  - $M_1 -> M_1'$ then we can apply the rule (App 1) and obtain that
    $M_1 M_2 -> M_1' M_2$.
  - $M_1 = v_1$ and $M_2 -> M_2'$ then we can apply the rule (App 2) and
    obtain that $v_1 M_2 -> v_1 M_2'$.
  - $M_1 = v_1$ and $M_2 = v_2$ then by canonical form lemma
    $v_1 = fn x : T_1 . N$ and we can apply the rule (Beta) and obtain that
    $(fn x : T . N) v_2 -> N{x := v_2}$.

=== Permutation
If #jud($M$, $T$) is derivable and $Delta$ is a permutation of $Gamma$ then
#jud(ctx: $Delta$, $M$, $T$) is derivable with the same height.

*Proof.* By induction on the height of #jud($M$, $T$).

=== Weakening
If #jud($M$, $T$) is derivable and $x in.not "Dom"(Gamma)$ then
#jud(ctx: $Gamma, x : S$, $M$, $T$) is derivable with the same height.

*Proof.* By induction on the height of #jud($M$, $T$).

=== Substitution
#let judx(ctx: $Gamma, x : T$ ,term, ty) = [
    #jud(ctx: ctx, term, ty)
]

If #judx($M$, $T$) and #jud($N$, $S$) are derivable then
#jud($M{x := N}$, $T$) is derivable.

*Proof.*
We proceed by induction on the height of the derivation
#jud(ctx: $Gamma, x : S$, $M$, $T$).

Base cases:

We distinguis on the possible base cases, so on the axioms:
- (T-True) Then it must be that $M = mtrue$ and by inversion lemma we have that
  the jdgment is #judx(mtrue, Bool) and $mtrue{x := N} = mtrue$ and is well-typed
  by hypothesis.
- (T-False) Then it must be that $M = mfalse$ and by inversion lemma we have that
  the jdgment is #judx(mfalse, Bool) and $mfalse{x := N} = mfalse$ and is
  well-typed by hypothesis.
- (T-Int) Then it must be that $M = n$ and by inversion lemma we have that
  the jdgment is #judx($n$, Nat) and $n{x := N} = n$ and is well-typed
  by hypothesis.
- (T-Var) Then it must be that $M = y$ and by inersion lemma we have that
  #judx($y$, $T$) and $y : T in Gamma, x : S$, we distinguish by case:
  - $x = y$ then the judgment is actaully #judx($x$, $T$) with $x{x := N} = N$
    and we know by hypothesis that #jud($N$, $T$).
  - $x eq.not y$ then $y {x := N} = y$ and it is well typed by hypothesis.

Inductive cases:

Let #judx($M$, $T$) with derivation height $k + 1$,
we proceed by case analysis on the last rule applied in the derivation:
- (T-Sum) Then it must be that $M = M_1 + M_2$ thus the conclusion of the rule
  must be #judx($M_1 + M_2$, $Nat$), by inversion lemma then we also know that
  #judx($M_1$, Nat) and #judx($M_2$, Nat) are derivable both with height $<= k$.
  We can apply on both of the derivation the inductive hypothesis and obtain that
  #jud($M_1{x:=N}$, $Nat$) and #jud($M_2{x:=N}$, $Nat$).
  Now we can apply the typing rule (T-Sum) and obtain
  #jud($M_1{x:=N}+M_2{x:=N}$, $Nat$).

- (T-IfThenElse) Then it must be that $M = mif M_1 then M_2 melse M_3$ thus
  the conclusion of the rule must be
  #judx($mif M_1 then M_2 melse M_3$, $T$), by inversion lemma we also know
  that #judx($M_1$, Bool), #judx($M_2$, $T$) and #judx($M_3$, $T$) are
  derivable all with height $<= k$. We can apply the inductive hypothesis on
  the all of the judgments and obtain: #jud($M_1 {x:=N}$, Bool),
  #jud($M_2{X:=N}$, $T$) and #jud($M_3{x:=N}$, $T$).
  Now we can apply the typing rule (T-IfThenElse) and obtain
  #jud($mif M_1{x:=N} then M_2{X:=N} melse M_3{x:=N}$, $T$).

- (T-Fun) Then it must be that $M = fn y : T_1 . M_1$ thus the conslusion of the
  rule rule must bt #judx($fn y : T_1 . M_1$, $T$), by inversion lemma we know that
  $T = T_1 -> T_2$ and #jud(ctx: $Gamma, x : S, y : T_1$, $M_1$, $T_2$) with
  height $<= k$ and $x eq.not y$ and $y in.not Gamma$, by permutation lemma
  #jud(ctx: $Gamma, y : T_1, x : S$, $M_1$, $T_2$) and by weakening lemma
  #jud(ctx: $Gamma, y : T_1$, $N$, $S$) we can apply the inductive hypothesis
  and obtain #jud(ctx: $Gamma, y : T_1$, $M_1 {x:=N}$, $T_2$).
  Now we can apply the typing rule (T-Fun) and obtain
  #jud($fn y : T_1 . M_1 {x := N}$, $T$).

- (T-App) Then it must be that $M = M_1 M_2$ thus the conclusion rule must be
  #judx($M_1 M_2$, $T$), by inversion lemma we also know
  that #judx($M_1$, $T_1 -> T$) and #judx($M_2$, $T_1$) are derivable all with
  height $<= k$. We can apply the inductive hypothesis on the all of the
  judgments and obtain: #jud($M_1 {x:=N}$, $T_1 -> T$) and
  #jud($M_2{X:=N}$, $T_1$).
  Now we can apply the typing rule (T-App) and obtain
  #jud($M_1{x:=N} M_2{x:=N}$, $T$).

=== Subject reduction / Type preservation
if #jud($M$, $T$), and $M -> M'$ then #jud($M'$, $T$).

We proceed by induction on the height of the derivation $M -> M'$.

Base cases:

We distinguis on the possible base cases, so on the axioms:
- (Sum) Then it means that $M = n_1 + n_2$ and $M' = n$, by inversion lemma
  we know that $T = Nat$ and by applying (T-Int) we obtain #jud($n$, $Nat$).
- (If-True) Then it means that $M = mif mtrue then M_2 melse M_3$ and $M' = M_2$,
  by inversion lemma we know that #jud($M_2$, $T$) is derivable.
- (If-False) Then it means that $M = mif mfalse then M_2 melse M_3$ and $M' = M_3$,
  by inversion lemma we know that #jud($M_3$, $T$) is derivable.
- (Beta) Then it means thta $M = (fn x : T_1 . M_1) v_2$ and $M' = M_1{x:=v_2}$
  by inversion lemma we know that #jud(ctx: $Gamma, x : T_1$, $M_1$, $T$) and
  #jud($v_2$, $T_1$).
  We can apply the substiution lemma to get that #jud($M_1{x:=v_2}$, $T$).


Inductive cases:

Let $M -> M'$ with derivation height $k + 1$
we proceed by case analysis on the last rule applied in the derivation:

- (Sum Left) Then it means that $M = M_1 + M_2$, $M' = M_1' + M_2$ with
  $M_1 -> M_1'$ with height $<= k$, by inversion lemma we know that
  $T = Nat$, #jud($M_1$, $Nat$) and #jud($M_2$, $Nat$), we can apply the
  inductive hypothesis on the first judgment and obtain #jud($M_1'$, $Nat$).
  Now we can apply the typing rule (T-Sum) and get that #jud($M_1' + M_2$, $Nat$).

- (Sum Right) Then it means that $M = v_1 + M_2$, $M' = v_1 + M_2'$ with
  $M_2 -> M_2'$ with height $<= k$, by inversion lemma we know that
  $T = Nat$, #jud($v_1$, $Nat$) and #jud($M_2$, $Nat$), we can apply the
  inductive hypothesis on the second judgment and obtain #jud($M_2'$, $Nat$).
  Now we can apply the typing rule (T-Sum) and get that #jud($v_1 + M_2'$, $Nat$).

- (If) Then it means that $M = mif M_1 then M_2 melse M_3$,
  $M' = mif M_1' then M_2 melse M_3$ and $M_1 -> M_1'$ with height $<= k$,
  by inversion lemma we know that #jud($M_1$, Bool), #jud($M_2$, $T$) and
  #jud($M_3$, $T$) by inductive hypothesis on the first judgment we
  obtain #jud($M_1'$, $Bool$).
  Now we can apply the typing rule (T-If) and get that
  #jud($mif M_1' then M_2 melse M_3$, $T$).

- (App 1) Then it means that $M = M_1 M_2$, $M' =  M_1' M_2$ and
  $M_1 -> M_1'$ with height $<= k$, by inversion lemma we know that
  #jud($M_1$, $T_1 -> T$) and #jud($M_2$, $T_1$), we can apply the inductive
  hypothesis on the firts judment and obtain that #jud($M_1'$, $T_1 -> T$).
  Now we can apply the typing rule (T-App) anf get that #jud($M_1' M_2$, $T$).

- (App 1) Then it means that $M = v M_2$, $M' =  v M_2'$ and
  $M_2 -> M_2'$ with height $<= k$, by inversion lemma we know that
  #jud($v$, $T_1 -> T$) and #jud($M_2$, $T_1$), we can apply the inductive
  hypothesis on the second judment and obtain that #jud($M_2'$, $T_1$).
  Now we can apply the typing rule (T-App) anf get that #jud($v M_2'$, $T$).

=== Colorallary 1
If #jud(ctx: $nothing$, $M$, $T$) and $M ->^* M'$ then
#jud(ctx: $nothing$, $M'$, $T$).

*Proof.*
By induction on the number of steps in $M ->^* M'$:
- $"steps" = 0$ then $M = M'$.
- $"steps" = n + 1$ then $M ->* M_1$ in $n$ steps and $M_1 -> M'$
  by inductive hypothesis we get that #jud(ctx: $nothing$, $M_1$, $T$)
  and then by subject reduction #jud(ctx: $nothing$, $M'$, $T$).

=== Safety
If #jud(ctx: $nothing$, $M$, $T$) and $M ->^* M' arrow.r.not$ then $M'$ is
a value.

*Proof.* By corollary 1 we know that #jud(ctx: $nothing$, $M'$, $T$) then
by probress theorem either:
- $M'$ is a value
- $M' -> M''$ but that is a contraddicion.
