#import "Preamble.typ" : *

= Zettel 3
Bearbeitet von:\
    Leon Krasniqi,
    Christian Krause,
    Silas Gaschler(Tutorium:Gregor Teupke(Mi 16:15))
== Aufgabe 1
=== a)
${(0,0),(1,0)} in R$

${(1,0),(2,0)} in R$

${(0,0),(2,0)} in.not R$


$=> "nicht transitiv"$
=== b)
$R := {(a,b) in X#sym.times X|  exists A in cal(A): a in A and b in A}$

#lemma[ 
$R$ ist eine Äqvivalenzrelation.
]
#proof[
Reflexivität:

da $AA$ eine Partition von $X$ ist, gilt für jedes $a in X: exists A in cal(A), a in A$
, darum ist $(a,a) in {(a,a)in X #sym.times X| exists A in cal(A), a in A and a in A} subset R$ 


Symmetrie:
$R = {(a,b) in X#sym.times X|  exists A in cal(A): a in A and b in A}$

$ R = {(b,a) in X#sym.times X|  exists A in cal(A): a in A and b in A} $
d. h. für alle $a,b in X$ gilt:
  $ (a,b) in R &<=> exists A in AA: a in A and b in A \
    &<=> exists A in cal(A): b in A and a in A \
  &<=> (b,a) in R $

Transitivität:
Für alle $a,b,c in X$ gilt:
$ (a,b) in R and (b,c) in R &<=> (exists A in cal(A): a in A and b in A) and (exists B in cal(A): b in B and c in B)  \ 
"Da A eine Partition von X ist, gilt: " & exists! A in cal(A), b in A quad "d.h. " A = B
  \
 & <=> exists A in cal(A): a in A and b in A and c in A \ 
&=> exists A in cal(A): a in A and c in A \
&<=> (a, c) in R $
]
=== z.z 
$ X \/ R = cal(A) $
#proof[

$   cal(A) subset X \/ R:$
$ "Da eine Partiotion nie " emptyset "enthält:" forall A in cal(A) exists a in A $
$ =>[a]_R= {x| exists B in cal(A) : a in B and x in B}  $
Da $cal(A)$ eine Partition ist, gilt $forall B in cal(A): a in B => A = B$
$ =>[a]_R= {x| a in A and x in A}  $
$ =>[a]_R = A $
$ forall A in cal(A): exists[a]=A $
$ =>  cal(A) subset X \/ R $
$$
$  X \/ R subset cal(A): $
$ [a] := {b | exists A in cal(A): b in A and a in A } $
$ =>forall [a] in X \/ R: exists A in cal(A): a in A $
$ => forall [a] in X \/ R exists A in cal(A) "mit" a in A: $
$ [a] = {b|b in A and a}$
$ => [a] = A $
$ => X \/ R subset AA $
]
== Aufgabe 2
=== a)
==== (i)
$A = {(x_1,x_2)in RR^2|x_1^2+x_2^2<=1 and x_1 <=0 and x_2 <=0}$
$R:= {((x_1,x_2),(y_1,y_2))in RR^2 #sym.times RR^2}$
==== Maxiumum bestimmen

Vermutung: Das Maximum ist $(0,0)$
#proof[

*z.z*\
$ forall (x_1,x_2) in A: ((x_1,x_2),(0,0)) in R $
$ <=> forall(x_1,x_2)in A: (x_1<0) or (x_1 = 0) and (x_2 <= 0) $
da $(x_1,x_2)in A$ ist $x_1 <= 0 and x_2 <= 0$
$ => (0,0)" ist das Maximum und Supremum und maximales Element von" A $

]
=== Miniaimale Elemente bestimmen
Vermutung: $(x_1,x_2):x_1+x_2 )= 1$ sind die minimalen Elemente von A

z.z $ forall(x_1,x_2)in A "mit" x_1^2+x_2^2=1: forall(y_1,y_2)in A: ((y_1,y_2),(x_1,x_2)in.not R) $
#proof[

Annahme: 
$ exists (y_1,y_2)in A: ((y_1,y_2),(x_1,x_2)) in R $
$ =>y_1 <=x_1 and y_2 <=x_2 $

Da $x_1,X_2,x_3,x_4<=0$ gilt:
$ => y_1^2>=x_1^2 and y_2^2>=x_2^2 $
$ => y_1^2>=1-x_2^2 and y_2^2 >=x_2^2 $
$ => y_1^2>=1-x_2^2 and y_2^2-x_2^2 >= 0 $
$ y_1^2+y_2^2 =>1underbrace(-x_2^2+y_2^2 , >0) $
$ y_1^2+y_2^2 >=1 $
$ (y_1,y_2)in.not A $
$=>$ Widerspruch

]

minimale Elemente sind also ${x_1,x_2|(x_1,x_2)in A and (x_1^2+x_2^2)=1}$
Es gibt kein Infimum, da es keine Vergleichbarkeit zwischen den minimalen Elementen gibt.
==== (ii)
Das Supremum kann nicht mehr eindeutig bestimmt weden, da $exists y in RR: forall(0,x)in A union({0} #sym.times RR)((0,x)<(0,y))$

=== b)
$prec.curly.eq$ ist eine Ordnungsrelation
$=>prec.curly.eq$ ist reflexiv, antisymetrisch und transitiv.
$ prec := prec.curly.eq\\Delta x $
z.z $prec$ ist irreflexiv, transitiv und antisymetrisch.
#proof[

$prec= {(a,b)in X #sym.times X| (a,b in prec.curly.eq and a eq.not b)}$
\
\
irreflexiv:

Annahme $prec$ ist nicht irreflexiv. Dann:
$ exists a in X: (a,a)in prec  $
$=> (a,a)in prec.curly.eq and a eq.not a$
$=>$ Widerspruch $=>prec$ ist irreflexiv.

\
antisymetrisch:

Annahme: $prec$ ist nicht antisymetrisch. Dann:
$ exists a,b in X: (a,b)in prec and (b,a)in prec $
$=>(a,b) in prec.curly.eq and (b,a)in prec.curly.eq$

Da $prec.curly.eq$ antisymetrisch ist, folgt:
$ a = b $
$=>$ Widerspruch den $prec$ ist irreflexiv $=> prec$ ist antisymetrisch.

\
transitiv:

$ (a,b) in prec and (b,c) in prec $
$ => (a,b) in prec.curly.eq and (b,c) in prec.curly.eq and a eq.not b and b eq.not c and a eq.not c $
($a eq.not c$ gilt da $prec$ irreflexiv)
$ => (a,c) in prec.curly.eq and a eq.not c $
$ => (a,c) in prec => "transitiv"$ 

]

==== (ii)
$prec$ ist transitiv, irreflexiv und antisymetrisch 
$ prec.curly.eq := prec union Delta x  = {(a,b)in X #sym.times X| (a,b) in prec.curly.eq or (a,b) in Delta x} $

z.z $ prec.curly.eq $ ist reflexiv, antisymetrisch und transitiv.
#proof[

reflexiv:

$ forall a in X: (a,a) in prec.curly.eq $
$ <=> forall a in X: (a,a)in prec or underbrace((a,a)in Delta x ,top) $
$=> prec.curly.eq$ ist reflexiv.

\
antisymetrisch:
Annahme: $ prec.curly.eq$ ist nicht antisymetrisch. Dann:
$ exists a,b in X: (a,b)in prec.curly.eq and (b,a)in prec.curly.eq  and a eq.not b $
$ => underbrace((a,b) in prec and (b,a)in prec,bot" da "prec "antisym.") or underbrace((a,b) in Delta x  and (b,a)in Delta x,bot"da" a eq.not b) $
$=>$ Widerspruch $=> prec.curly.eq$ ist antisymmetrisch.

\
transitiv:

Seien $(a,b) in prec.curly.eq$ und $(b,c) in prec.curly.eq$.

Wir unterscheiden 3 Fälle:

Liegt $(a,b)in Delta x$, so ist $a=b$ und damit $(a,c)=(b,c) in prec.curly.eq$.

Liegt $(b,c) in  Delta x$, so ist $b=c$ und damit $(a,c)=(a,b) in prec.curly.eq$.

Liegen $(a,b) in prec$ und $(b,c) in prec$, so folgt a $prec$ transitiv: 
  $(a,c) in prec subset.eq prec.curly.eq$.

In allen Fällen gilt $(a,c) in prec.curly.eq =>$ transitiv.

]

_Anmerkung: Die Transitivität folgt auch, da $prec union Delta x$ die reflexive Hülle von $prec$ bildet, und transitiv bei der Hüllenbildung erhalten bleibt._

== 3.3)

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
