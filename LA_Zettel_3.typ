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

