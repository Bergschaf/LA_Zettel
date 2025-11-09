#import "Preamble.typ": *

= LA Zettel 3

Bearbeitet von Leon Krasniqi, Christian Krause, Silas Gaschler (Tutorium: Gregor Teupke(Mi 16:15))
== Aufgabe 4.1
- (i): $f$ ist injektiv
- (ii): $exists g: Y->X: g compose f = id_X$
- (iii) Für beliebige $X_0$ und beliebige $f_1,f_2: X_0 -> X$ gilt: Aus $f compose f_1=f compose f_2$ folgt $f_1=f_2$
#lemma[
  $ ("i")<=>("ii")<=>("iii") $
]
#proof[

  *$ ("i")=>("ii"): $*
  Definiere $g:Y->X$ wie folgt:
  $ g:={(y,x)in Y times X | f(x)= y} $
  $ => g compose f = {(x_1,x_2) in X times X|exists f(x) in Y: (x_1,f(x))in f and (f(x),x_2)in g} $
  mit

  $ ("i"): forall x_1,x_2in X:f(x_1)=f(x_2)=>x_1=x_2 $
  $ => g compose f = {(x,x) in X times X|exists f(x) in Y: (x,f(x))in f and (f(x),x)in g}=id_X $

  *(ii)$=>$(iii):*

  Es sein $X_0$ eine beliebige Menge und $f_1,f_2:X_0->X$ beliebige Abbildungen.

  $("ii"): exists g:Y->X: g compose f = id_X$ und $f compose f_1 = f compose f_2$
  $ =>g compose (f compose f_1) = g compose (f compose f_2) $
  $ <=> underbrace((g compose f), id_X)compose f_1=underbrace((g compose f), id_X)compose f_2 $
  $ => f_1 =f_2 $

  *$ ("iii")=>("i") $*
  $ ("iii"):f compose f_1 = f compose f_2 => f_1=f_2 $
  $ <=> forall x_0 in X_0: f(f_1(x_0))=f(f_2(x_0))=>f_1(x_0) = f_2(x_0) $
  Sei $x_1=f_1(x_0)$ und $x_2=f_2(x_0)$. Und da $f_1$ und $f_2$ frei wählbar sind, können sie auch surjektiv sein. Für surjektive $f_1,f_2$ folgt:
  $ forall x_1,x_2 in X: f(x_1)=f(x_2)=>x_1 =x_2 $
  *$ =>(("i")=>("ii")=>("iii")=>("i"))=>(("i")<=>("ii")<=>("iii")) $*

]

== Aufgabe 4.3
a)
Es könnte ein Index $in J_1 inter J_2$ existieren. Demnach wäre der Index nach der Vereinigung von $J_1$ und $J_2$ nicht mehr einer der Ursprünglichen Familien zuzuordnen. Indem wir $J_1$ und $J_2$ durch das jeweilige Kartesische Produkt mit zwei Mengen ${1},{2}$, generieren wir zwei disjunkte Indexmengen $J_1 times {1}$ und $J_2 times {2}$. So kann jedem Index immernoch eindeutig ein Element der Familie zugeordnet werden. So kann garantiert werden, das unsere Konkatenation/neue Familie alle Element der beiden Familien beinhaltet.

b)

Def:
$ ||_(i in I)F_i:union.dot.big({i}times J_i)->Y $
$ ||_(i in I)F_i(i,j):=F_i (j) $
c)
geg: $ Y=N_0;I = RR; $$ J_i= {A subset.eq ZZ|max(A)<=i}; $ $ F_i : J_i in.rev A |-> hash (A inter RR_(>0)) $

$=>$
$ ||_(i in I)F_i (15.7,{-10,10}) = hash({-10,10} inter RR_(>0)) = hash({10})= 1 $

== Aufgabe 4.4
(i) $ (RR^X,+) $
Da alle Fuktionswerte in $RR$ liegen gilt:
$ forall f_1,f_2 in RR^X: $
$ f_1(x)+f_2(x) = f_3(x) in RR^X $

Assoziativität:
Da die Addition assoziativ ist gilt:
$ forall f_n:X in.rev x |-> r in RR $
$ => f_1(x)+(f_2(x)+f_3(x)) = (f_1(x)+f_2(x))+f_3(x) $

neutrales Element:
$ f_0: X in.rev x |->0 in RR $
#proof[
  $ forall f_n in RR^X, forall x_0,x_n in X: $
  $ f_0(x_0)+f_n (x_n)=0+f_n (x_n) = f_n (x_n) $
]
$ =>(RR^X,+) "ist ein Monoid" $
(ii)$ (pset(X),inter) $
Monoid, da de Teilmengen wieder in der Ursprungsmenge sind, der Schnitt assoziativ ist und das neutrale Elemente gegeben ist durch:
$ A subset X $
$ A inter X =A $
$ => e=X $

(iii)
$ (pset(X),Delta) $
$ forall A,B in pset(X): A Delta B = {underbrace(\\B, in pset(X)) union underbrace(\\A, in pset(X))}in pset(X) $
Die symetrische Differenz ist assoziativ, da:
$
  (A triangle.t B) triangle.t C
  &= ((A without B) union(B without A)) triangle.t C \
  &= ((A without B) union(B without A)) without C med union med C without((A without B) union(B without A)) \
  &= (A without B without C) med union med(B without A without C) med union med((C without(A without B)) without(B without A)) \
  &= (A without B without C) med union med(B without A without C) med union med(((C without A) union(C inter B)) without(B without A)) \
  &= (A without B without C) med union med(B without A without C) med union med((C without A) without(B without A)) med union med((C inter B) without(B without A)) \
  &= (A without B without C) med union med(B without A without C) med union med(C without A without B) med union med(A inter B inter C)
$$
  A triangle.t(B triangle.t C)
  &= A triangle.t((B without C) union(C without B)) \
  &= A without((B without C) union(C without B)) med union med((B without C) union(C without B)) without A \
  &= ((A without(B without C)) without(C without B)) med union med(B without C without A) med union med(C without B without A) \
  &= (((A without B) union(A inter C)) without(C without B)) med union med(B without A without C) med union med(C without A without B) \
  &= ((A without B) without(C without B)) med union med((A inter C) without(C without B)) med union med(B without A without C) med union med(C without A without B) \
  &= (A without B without C) med union med(A inter B inter C) med union med(B without A without C) med union med(C without A without B)
$
$=> (A Delta B) Delta C = A Delta (B Delta C)$

Das neutrale Element ist die leere Menge, da:
$ forall A in pset(X): A Delta emptyset = {underbrace(A\\ emptyset, A) union underbrace(emptyset\\A, emptyset)} = A $
$=> (pset(X),Delta)$ ist ein Monoid.

(iv)$ (X^X,compose) $

Die Komposition von Funktionen ist assoziativ (nach Script)
$ forall f_1,f_2 in X^X: $
$ f_1(x)compose f_2(x) = f_1(f_2(x)) = f_3(x) in X^X $

(v)
$ (ZZ²,((x_1,x_2),(y_1,y_2))mapsto (x_1y_1,x_2+y_2)) $
Monoid, da Elemente wieder in der Menge sind und Assoziativität und das neutrales Element e gegeben ist durch:

Assoziativität:

1)$ (z_1,z_2)in ZZ^2 $
$ [(x_1,x_2),(y_1,y_2)],(z_1,z_2) |-> (x_1y_1,x_2+y_2),(z_1,z_2) $
$ |->(x_1y_1z_1,x_2+y_2+z_2) $

2) $ (x_1,x_2),[(y_1,y_2),(z_1,z_2)]|->(x_1,x_2),(y_1z_1,y_2+z_2) $
$ |->((x_1y_1z_1,x_2+y_2+z_2)) $
Neutrales Element:
$ forall (y_1,y_2) in ZZ^2: (1,0),(y_1,y_2)|->(1*y_1,y_2 + 0)=(y_1,y_2) $
$ => e=(1,0) $

(vi) $ (pset(X),(A,B)|->A^complement union B^complement) $

$ ((A,B)|->A^complement union B^complement,C)|->((A^complement union B^complement)^complement union C^complement) $
$ ((A,(B,C)|->B^complement union C^complement)|->(A^complement union (B^complement union C^complement)^complement) $

$=>$ keine Assoziativität $=>$ Keine Halbgruppe
