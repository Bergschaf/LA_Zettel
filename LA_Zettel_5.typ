#import "Preamble.typ": *

= LA Zettel 5
Bearbeitet von Leon Krasniqi, Christian Krause, Silas Gaschler (Tutorium Gregor Teupke)



== Aufgabe 2
= Aufgabe 5.2

=== (i)
Das Tupel $(R^X, +)$ ist abelsch, denn:

$forall f_1, f_2 in R^X, forall x_1, x_2 in X:
f_1(x_1) + f_2(x_2) = f_2(x_2) + f_1(x_1)$

Dies gilt, da Addition in $R$ kommutativ ist.

=== (ii)
$(P(X), inter)$ ist keine Gruppe.

=== (iii)
$(P(X), Delta)$, wobei
$A Delta B = (A \\ B) inter (B \\ A)$:

$A Delta B
= A \\ B inter B \\ A
= B \\ A inter A \\ B
= B Delta A$

Daher: abelsche Gruppe.

=== (iv)
Keine Gruppe.

=== (v)
Keine Gruppe.

== b)
#lemma[
  Jede Gruppe mit höchstens vier Elementen ist abelsch.
]
#proof[

  Sei $(G, star)$ eine Gruppe und $e$ das neutrale Element.
  === Fall 1:
  $ G = {e} $
  Einzig mögliche Verknüpfung:
  $ e star e = e $
  Elemente mit sich selber Verknüpft sind abelsch $=>$ für Fall 1 ist $(G,star)$ abelsch
  === Fall 2:
  $ G = { e, a } $

  $ a star e = a = e star a $

  $=>$ Gruppe ist abelsch.

  === Fall 3:
  $ G = { e, a, b } $

  Angenommen: $ a star b != b star a $


  Es gilt:

  $ a star a' = a' star a and b star b' = b' star b $
  $ => a' != b and b' != a $

  Daraus folgt $a star b != e and b star a != e$.

  Somit:

  $ a star b != e and a star b != a and a star b != b $

  $ =>a * b in.not G $
  $ => "Wiederspruch" $

  === Fall 4:
  $G = { e, a, b, c }$

  Annahme wie bei Fall 3:

  Es gilt also weiterhin:

  $ b star a != e and b star a != a and b star a != b $

  $ a star b != b star a $
  Falls
  $ b star a = c => b star a in.not G $
  Falls
  $ a star b = c => b star a in.not G $

  $ =>"Widerspruch"=>"Gruppe ist abelsch" $

  $ => "Eine Gruppe mit maximal 4 Elementen ist abelsch" $

]


== Aufgabe 5.6
#lemma[
  $hash U | hash G$
]
#proof[

  $ forall a in G: exists a star U $
  $ forall a,b in G "gilt" a star U " und" b star U " sind entweder gleich oder disjunkt" $
  $ => [a_n] = {a in G| a star U = a_n star U} $
  $ => union.big_n [a_n]= G $
  Es gilt:
  $ hash A union B = hash A + hash B $
  $ forall a in G : hash a*U = hash U $
  $
    => hash G = hash union.big_n [a_n] = hash [a_1] union [a_2] union...union[a_n] = hash [a_1] + hash[a_2]+ ...+hash [a_n] = hash U + hash U +...+ hash U = n*hash U
  $

  $ => hash G = n * hash U => hash U | hash G $

]
