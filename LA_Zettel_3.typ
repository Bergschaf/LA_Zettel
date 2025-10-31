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
=== z.z 
$X \/ R = AA$
#proof[

$   AA subset X \/ R:$
$ "Da eine Partiotion nie " emptyset "enthält:" forall A in AA exists a in A $
$ =>[a]_R= {x| exists B in AA : a in B and x in B}  $
Da $AA$ eine Partition ist, gilt $forall B in AA: a in B => A = B$
$ =>[a]_R= {x| a in A and x in A}  $
$ =>[a]_R = A $
$ forall A in AA: exists[a]=A $
$ =>  AA subset X \/ R $
$$
$  X \/ R subset AA: $
$ [a] := {b | exists A in AA: b in A and a in A } $
$ =>forall [a] in X \/ R: exists A in AA: a in A $
$ => forall [a] in X \/ R exists A in AA "mit" a in A: $
$ [a] = {b|b in A and a}$
$ => [a] = A $
$ => X \/ R subset AA $
]
== Aufgabe 2
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
