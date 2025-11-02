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
_Anmerkung: Hier könnte ein Bild helfen_

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
