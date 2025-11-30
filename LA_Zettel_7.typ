#import "Preamble.typ": *

= LA Zettel 7
Bearbeitet von Leon Krasniqi, Christian Krause, Silas Gaschler (Tutorium: Gregor Teupke (Mi 16:15))

== Aufgabe 1
(i)
$(ZZ_3,+_3,dot_2)$
Da $3$ eine Primzahl ist, ist nach script $(ZZ_3,+_3,dot_3)$ ein Körper.
==== Bestimme Charakteristik
$ underbrace((1+1))_(2)+1 = 0 => "char"(ZZ_3,+_3,dot_3)= 3 $
==== Nullteilerfreiheit
$ZZ_3 = {0,1,2}$
$0*x = 0 forall x in ZZ_3$
$1*2 = 2*1 = 2$
$2*2 = 1$
$1*1 = 1$
$=> "Nullteilerfreiheit"$

=== (ii)

Bereits bewiesen
$ forall A,B in cal(P)(X): $
$(cal(P)(X),Delta) " ist abelsche Gruppe"$
$ A inter (B inter C)= (A inter B)inter C in cal(P)(X) $
$=> "Es handelt sich um einen Ring"$
Das Einselement ist $X$ da $A inter X = A$
Das Nullelement ist $emptyset$
==== Nullteilerfreiheit
Sei $A in cal(P)(X)$ und $emptyset != A$ dann existiert ($hash X > 1$) eine zu $A$ disjunkte Menge $B in cal(P)(X)$ mit $B!= emptyset$
$ => A inter B = emptyset $
$=>$ Falls $hash X > 1$ ist der Ring nicht Nullteilerfrei.

Falls $hash X = 1$ existiert maximal eine von $A$ disjunkte Teilmenge, und zwar  $emptyset$. Also ist der Ring für $hash X = 1$ Nullteilerfrei
==== Charakteristik



=== (iii)
Angenommen $(cal(P)(X),Delta,Delta)$ ist ein Ring, dann muss $forall A,B,C in X$ das Distributivgesetz gelten:
$ A Delta (B Delta C) = (A Delta B) Delta (A Delta C) $
Da $Delta$ assoziativ sein muss, und die inversen Elemente für die verknüpfung $Delta$ existieren müssen:
$ iff (A Delta B) Delta C = (A Delta B) Delta (A Delta C) $
$ iff (A Delta B) Delta C = (A Delta B) Delta (A Delta C) $
$ iff C = A Delta C iff A = emptyset $
Das ist ein Wiederspruch, also ist $(cal(P)(X),Delta,Delta)$ kein Ring
==== (iv)
Damit $(QQ^RR,+,compose)$ ein Ring ist, muss das Distributivgesetz gelten.
das heißt:
$ forall f_1,f_2,f_3 in QQ^RR; forall x_2,x_3 in RR: $
$ f_1 compose (f_2(x_2)+f_3(x_3)) = f_1 compose f_2(x_2)+f_1 compose f_3(x_3) $
Wähle $f_1 = f_2 = f_3 : RR in.rev x |-> 1 in QQ:$
$ f_(1)(f_(2)(x_(2))+f_(3)(x_(3)))!=f_(1)(f_(2)(x_(2)))+f_(1)(f_(3)(x_(3))) $
$ 1 != 1+1 $
Das ist ein Wiederspruch. Es handelt sich also um keinen Ring

== Aufgabe 2

=== b)
#proof[

  *$ (i)=> (i i): $*
  $ (i): forall a in R: a != 0_R => a dot b != 0_R $
  $ f: R in.rev a |-> a dot b in R $
  $ "Kern"(f) = {a|a dot b = 0_R} = {0_R} $
  $ I: R \/ {0_R}-> "Bild"(f) $
  $ a+"Kern"(f) = [a] |-> f(a) $
  Homomorphiesatz für Ringe
  $=>I$ ist ein Isomorphismus
  $ pi: R in.rev a-> [a] in R\/{0_R} $
  Da $ R \/{0_R} = {a+0_R = [a] a in R} = {a = [a]| a in R} $
  ist $pi$ injektiv.
  Es gilt außerden, das:
  $ f = I compose pi $
  Da $I,pi$ injektiv  $=> f$ injektiv

  *$ (i i) => (i i i) $*
  $ (i i): (forall a,c in R: f(a) = f(c)=> a = c) $
  $ <=> (forall a,c in R: a dot b = c dot b => a = c) $

  *$ (i i i)=> (i) $*
  $ (i i i):(forall a,b in R: a dot b = c dot b => a = c) $
  Es gilt außerdem $0_R dot b = 0_R$
  $ "Sei" a dot b = 0_R = 0_R dot b => a = 0_R $
  $=>$ b ist kein Rechtsnullteiler

  *$=> ((i)=> (i i)=> (i i i)=> (i)) => "Ringschluss"$*

]


== Aufgabe 3
=== b)
#lemma[

  Seien $(R_1,+_1,dot_1)$ und $(R_2,+_2,dot_2)$ Ringe mit den Nullelementen $0_(R_1)$ bzw. $0_(R_2)$ und $f: R_(1)-> R_(2)$ ein Homomorphismus, dann gilt
  - (i): $f$ ist injektiv
  - (ii): $"Kern"(f) = {0_(R_1)}$
  - (iii): Die einzige Lösung der Gleichung $f(a) = 0_(R_2)$ ist $a = 0_(R_1)$
]
#proof[

  *(i)$=>$(ii)*
  $ (i): (forall a,b in R_1: f(a)= f(b) => a = b) $
  $ forall a_(n) in R_1: f(a_(n))= f(a_(n)+_1 0_(R_1)) = f(a_(n))+_2 f(0_(R_1)) $
  Da wir $+_2$ Kürzen dürfen
  $ iff 0_(R_2) = f(0_(R_1)) $
  $ => 0_(R_1) in "Kern"(f) $

  $=> forall b in R_1 "mit" f(b) = 0_(R_2) =>f(b)= f(0_(R_1)) => b = 0_(R_1)$
  $ => "Kern"(f) = {0_(R_(1))} $
  *(ii)$=>$(iii)*
  $ (i i): "Kern"(f) = {0_(R_1)}= {a in R_1| f(a) = 0_(R_2)} $
  $ => forall a in R_1 "mit" f(a)=0_(R_2) => a in "Kern"(f) => a = 0_(R_1) $
  *(iii)$=>$(i)*

]

== Aufgabe 4

== Aufgabe 5
a)
#lemma[
  Jeder Körper $(K,+,dot)$ ist Nullteilerfrei.
]
#proof[

  Angenommen es existiert ein Linksnullteiler $a!= 0_K$
  $ exists b!=0_K in K: $
  $ a b = 0_K $
  $ a b = a 0_K $
  $ iff a^(-1) dot a dot b = a^(-1) dot a dot 0_K $
  $ iff b = 0_K $
  Das ist ein Wiederspruch
  $=>$ Jeder Körper ist Nullteilerfrei

]
#lemma[
  Es sei $(K,+,dot)$ ein Körper und $a,b in K$.
  $ (a-x) dot (b-x) = 0_K => x = a or x = b $


]
#proof[

  Wir haben bereit gezeigt, das jeder Körper Nullteilerfrei ist. Daraus folgt:
  $ underbrace((a-x), in K) dot underbrace((b-x), in K) = 0_K => a-x = 0_K or b-x = 0_K $
  $ iff x = a or x = b $


]
== b)
Wir beweisen zunächst einige Hilfslemmas. Zur besseren lesbarkeit wird verwendt: $1_K hat(=) 1$
#lemma[
  Sei $(K,+, dot)$ ein Körper mit  $"char"(K)=0$, dann gilt
  $ forall a,b in NN: a 1 = b 1 => a = b $
]
#proof[

  Falls $ a >= b $
  $ a 1 = b 1 iff b 1 + (a-b)1 = b 1 => a-b = "char"(K) = 0 => a = b $
  Falls $ a <= b $
  $ b 1 = a 1 iff a 1 + (b-a)1 = a 1 => b-a = "char"(K) = 0 => a = b $

]
#lemma[
  Sei $(K,+, dot)$ ein Körper mit  $"char"(K)=0$, dann gilt:
  $ a 1 + b 1 = (a+b) 1 $
  $a 1 + b (-1) = (a-b) 1$
  $ a 1 dot b 1 = (a dot b) 1 $
  $ (a 1)^(-1)dot (b 1)^(-1) = ((a dot b)1)^(-1) $


]
#proof[

  $ a 1 + b 1 = underbrace((1+...+1), a "mal") +underbrace((1+...+1), b "mal") = (a+b)1 $
  $
    1 + b 1 = underbrace((1+...+1), a "mal") +underbrace((-1-...-1), b "mal") = underbrace((1+...+1), a-b "mal") +underbrace((0_K+...+0_K), b "mal") = (a-b)1
  $
  $ a 1 dot b 1 = underbrace((1+...+1), a "mal") dot b 1= underbrace((b 1 +...+ b 1), a "mal") = (a dot b)1 $
  $ (a 1)^(-1)dot (b 1)^(-1) dot a 1 dot b 1 = 1 iff (a 1)^(-1)dot (b 1)^(-1) dot (a dot b) 1 = 1 $
  $ => (a 1)^(-1)dot (b 1)^(-1) = ((a dot b) 1)^(-1) $

]


#lemma[

  Sei $(K,+,dot)$ ein Körper mit $"char"(K)=0$, dann enthält $K$ einen Unterkörper, der isomorph zu $QQ$ ist.

]
#proof[

  Wir verwenden aus dem script:

  Jeder Homomorphismus zwischen Körpern ist injektiv

  Wir definieren:
  $ f: QQ-> K $$
    a/b |-> cases(a 1 dot (b 1)^(-1) "falls " a >0, 0_K "falls" a = 0, |a|(-1) dot (b 1)^(-1) "falls " a <0)
  $

  Wir zeigen, das $f$ ein Homomorphismus ist
  Zur besseren Lesbarkeit schreiben wir $n 1 hat(=) n$ und $(n 1)^(-1)hat(=)n^(-1)$
  $ f(a/b)+f(c/d) = a dot b^(-1)+c dot d^(-1) $
  $
    =b^(-1)(a+c dot b dot d^(-1))=b^(-1) dot d^(-1) dot (a dot d +c dot b) =(b dot d)^(-1 ) dot (a dot d + c dot b) = f((a d +c b)/(b d)) = f(a/b+b/c)
  $
  $ f(a/b) dot f(c/d) = a dot b^(-1)dot c dot d^(-1) = (a dot b )dot (b dot d)^(-1 )= f(a/b dot c/d) $
  $ => f" ist ein Homomorphismus" $
  $=> f "ist injektiv"$
  Wir definieren
  $ g: QQ-> "Bild"(f) $$
    a/b |-> cases(a 1 dot (b 1)^(-1) "falls " a >0, 0_K "falls" a = 0, |a|(-1) dot (b 1)^(-1) "falls " a <0)
  $
  $ => "g ist ein Isomorphismus" $
  Es gilt außerdem, da $"Bild"(f) subset.eq K$, dass das $"Bild"(f)$ einen zu $QQ$ isomorphen Unterkörper in $K$ bildet


]
== c)
#lemma[

  Kein endlicher Körper kann geordnet werden

]
#proof[

  In einem geordneten Körper gilt:
  $ 0_K < 1_K $
  $ alpha <= beta => alpha + gamma<=beta+gamma $
  Angenommen es existiert ein endlicher geordneter Körper $(K,+,dot)$, dann
  $ exists m = max(K) $
  Es gilt $forall a in K$
  $ a+1_K <=m $
  Wähle $a = m$
  $ =>m+1_K <= m iff m+1_K <= m +0_K $
  $ => 1_K <= 0_K $
  Das Wiederspricht den Rechenregeln in einem Körper

]
