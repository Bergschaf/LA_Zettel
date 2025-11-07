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

(i) $ (RR^X,+) $
Monoid, da Elemente wieder in der Menge sind, Additin assoziativ ist und als neutrales Elemente e gilt:
$ X $
und so weiter halt jungs wie soll ich das tippen??

(ii)$ (pset(X),inter) $
Monoid, da de Teilmengen wieder in der Ursprungsmenge sind, der Schnitt assoziativ ist und das neutrale Elemente gegeben ist durch:
$ A subset X $
$ A inter X =A $
$ therefore e=X $

(iii)$ (pset(X),Delta) $

(iv)$ (X^X,compose) $

(v)$ (ZZ²,((x_1,x_2),(y_1,y_2))mapsto (x_1y_1,x_2+y_2)) $
Monoid, da Elemente wieder in der Menge sind und Assoziativität und das neutrales Element e gegeben ist durch:

Assoziativität:

1)$ (z_1,z_2)in ZZ^2 $
$ [(x_1,x_2),(y_1,y_2)],(z_1,z_2) |-> (x_1y_1,x_2+y_2),(z_1,z_2) $
$ |->(x_1y_1z_1,x_2+y_2+z_2) $

2) $ (x_1,x_2),[(y_1,y_2),(z_1,z_2)]|->(x_1,x_2),(y_1z_1,y_2+z_2) $
$ |->((x_1y_1z_1,x_2+y_2+z_2)) $
Neutrales Elemente:
$ (0,0),(0,0)|->(0,0+0)=(0,0) $
$ therefore e=(0,0) $

(vi) $ (pset(X),(A,B)|->A^complement union B^complement) $


