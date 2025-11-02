#import "Preamble.typ" : *

= Zettel 3
Bearbeitet von: Leon Krasniqi, Christian Krause, Silas Gaschler(Tutorium:Gregor Teupke(Mi 16:15))
== Aufgabe 1
=== a)
${(0,0),(1,0)} in R$

${(1,0),(2,0)} in R$

${(0,0),(2,0)} in.not R$

$=> "nicht transitiv"$
=== b)
$R := {(a,b) in X#sym.times X|  exists A in AA: a in A and b in A}$

#lemma[ 
$R$ ist eine Äqvivalenzrelation.
]
#proof[
Reflexivität:

da $AA$ eine Partition von $X$ ist, gilt für jedes $a in X: exists A in AA, a in A$
, darum ist $(a,a) in {(a,a)in X #sym.times X| exists A in AA, a in A and a in A} subset R$ 


Symmetrie:
$R = {(a,b) in X#sym.times X|  exists A in AA: a in A and b in A}$

$ R = {(b,a) in X#sym.times X|  exists A in AA: a in A and b in A} $
d. h. für alle $a,b in X$ gilt:
  $ (a,b) in R &<=> exists A in AA: a in A and b in A \
    &<=> exists A in AA: b in A and a in A \
  &<=> (b,a) in R $

Transitivität:
Für alle $a,b,c in X$ gilt:
$ (a,b) in R and (b,c) in R &<=> (exists A in AA: a in A and b in A) and (exists B in AA: b in B and c in B)  \ 
"Da A eine Partition von X ist, gilt: " & exists! A in AA, b in A quad "d.h. " A = B
  \
 & <=> exists A in AA: a in A and b in A and c in A \ 
&=> exists A in AA: a in A and c in A \
&<=> (a, c) in R $
]

#lemma[
  Sei $f: X -> Y$ eine Funktion und $A_1, A_2 subset.eq X$ $B_1, B_2 subset.eq Y$ Mengen:
  $ (i)quad  f(A_1) \\ f(A_2) subset.eq f(A_1 \\ A_2) $
  $ (i i)quad  f^(-1)(B_1 \\ B_2) = f^(-1)(B_1) \\ f^(-1)(B_2) $
]
#proof[
  zu i: Für alle $y in Y$ gilt
$ y in f(A_1) \\ f(A_2) &<=> y in {y in Y | exists a_1 in A_1, f(a_1) = y} \\ {y in Y | exists a_2 in A_2, f(a_2) = Y} \
  &<=> y in {y in Y | exists a_1 in A_1, f(a_1) = y} and y in.not {y in Y | exists a_2 in A_2, f(a_2) = y} \
 &<=> exists a_1 in A_1, f(a_1) = y and exists.not a_2 in A_2, f(a_2) = y \
 &<=> exists a_1 in A_1, f(a_1) = y and forall a_2 in A_2, f(a_2) eq.not y \
  &=> exists a_1 in A_1, f(a_1) = y and a_1 in.not A_2 \
  &=> exists a_1 in A_1 \\ A_2, f(a_1) = y quad "wichtig: hier gilt Äquivalenz im Allgemeinen nicht "\ 
  &<=> y in f(A_1 \\ A_2).
  $
Aus $y in f(A_1) \\ f(A_1) => y in f(A_1 \\ A_2)$ folgt $f(A_1) \\ f(A_2) subset.eq f(A_1 \\ A_2)$.$quad quad square$ \
\
 Zu (ii): für alle $x in X$ gilt
  $ x in f^(-1)(B_1 \\ B_2) &<=> x in {x in X | f(x) in B_1 \\ B_2} \
  &<=> f(x) in B_1 \\B_2 \
  &<=> f(x) in B_1 and f(x) in.not B_2 \
  &<=> x in {x in X | f(x) in B_1} and x in.not {x in X | f(x) in B_2} \
  &<=> x in f^(-1)(B_1) \\\f^(-1)(B_2) 
  $
  Aus der logischen Äquivalenz folgt die Gleichheit (ii).
]

#lemma[
  6.5b) Seien $(X_i)_(i in I)$ $I$ indizierte teilmengen von $X$ und eine Relation $R subset.eq X times Y$. 
  Es gilt: $ B_(r)(R, inter.big_(i in I)X_i) subset.eq inter.big_(i in I) B_r(R, X_i) $
]
#proof[
  Für alle $y in Y$ gilt:
$ y in B_(r)(R, inter.big_(i in I)X_i) &<=> exists a in inter.big_(i in I)X_i, (a, y)  in R \ 
&<=> exists a in X, forall i in I, a in X_i, (a,y) in R\
  &=> forall i in I, exists a in X_i, (a,y) in R \
  &<=> y in inter.big_(i in I) {b in Y | exists a in X_i, (a,b) in R} \
  &<=> y in inter.big_(i in I) B_r(R, X_i)
  $
]

#lemma[

  6.5d) Seien $(Y_i)_(i in I)$ $I$ indizierte Teilmengen von $Y$ mit der Relation $R subset.eq X times Y$.
  Aussage 6.5d) aus dem Skript gilt im Allegemeinen Fall nicht zwingend. 
]

#proof[
  *Gegenbeispiel* zur Verallgemeinerung von 6.5d):
  Sei $X = {a_1, a_1}$, $Y= {b_1, b_2}$ und $R = X times Y$
  Sei $Y_1 = {a_1}$ und $Y_2 = {a_2}$. Das heißt: 
  $ U_r(R, inter.big_(i in I) Y_i) = emptyset $
  Es gilt allerdings auch: $ inter.big_(i in I) U_r(R, Y_i) = X $
  Aus diesem Wiederspruch folgt, dass die obige Aussage im allgemeinen nicht gilt. Die schwächere Version mit $subset.eq$ statt $=$ würde allerdings gelten.
]

== c)
#lemma[
  Zurückziehen einer Äquivalenzrelation entlang einer Funktion: Sei $f : X -> Y$ eine Funktion und $~_Y$ eine Äquivalenzrelation auf $Y$. 
  $ x_1 ~_X x_2 := f(x_1) ~_Y f(x_2) $ definiert eine Äquivalenzrelation auf X.
]
#proof([
  *Reflexivität* \
  Für alle $x in X$ gilt: $x ~_X x$, da $f(x) ~_Y f(x)$, was aus den eigenschaften der Äquivelnzrelation $~_Y$ folgt. \
  *Symmetrie* \
  Für alle $x_1, x_2 in X$ gilt $x_1 ~_X  x_2 => x_2 ~_X x_1$, da $f(x_1) ~_Y f(x_2) => f(x_2) ~_Y f(x_1)$. Das folgt wieder aus den Eigenschaften der Äquivalenzrelation $~_Y$. \
  *Transitivität* \
  Für alle $X_1, x_2, x_3 in X$ gilt 
  $ x_1 ~_X x_2 and x_2 ~_X x_3 => x_1 ~_X x_3 $
  das ist Äuqivalent zu der Aussage: (aufgrund der Definition von $~_X$)
  $ f(x_1) ~_Y f(x_2) and f(x_2) ~_Y f(x_3) => f(x_1) ~_Y f(x_3) $
  diese Aussage folgt ebenfalls aus der transitivät von $~_Y$
])

== 3.4

a) $R = W times K$. Jede Waschmaschine wäscht die Wäsche von jedem Kunden. \
b) $R = W times emptyset$. Alle Waschmaschinen waschen gerade nichts. \
c) $R$ ist eine Abbildung: Jede Waschamschine wäscht die Wäsche von einem Kunden. \

d) $R$ ist surjektiv aber nicht injektiv: Alle Kunden werden bedient, d.h. die Wäsche von jedem Kunden wird von mindestens einer Waschamschine gewaschen. (Und es gibt mindestens einen Kunden, dessen Wäsche von mindetens zwei Maschinen gewaschen wird) \
e) $R$ ist injektiv: Die Wäsche von jedem Kunden wird von höchstens einer Waschmaschine gewaschen. \
f) $R$ ist bijektiv: Jede Waschmaschine wäscht die Wäsche von genau einem Kunden.

