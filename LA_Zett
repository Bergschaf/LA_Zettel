#import "Preamble.typ": *

= LA Zettel 5

= Nr.I-5.3

$ sigma := $
Fehlstände:
$ (2,5),(2,6),(2,7),(2,8),(3,5),(3,6),(3,7),(3,8),(4,5),(4,6),(4,7),(4,8),(5,8),(6,8),(7,8) $
Signum:
$ s g n(sigma)=(-1)^k $
$ k=15 $
$ =>s g n(sigma)=(-1)^15=-1 $
Transpositionen:
#proof[
  $ tau(8, 6)compose tau(7, 5)compose tau(8, 4)compose tau(7, 3)compose tau(6, 2)compose sigma = id $
  $ => sigma= id compose tau(6, 2)compose tau(7, 3)compose tau(8, 4)compose tau(7, 5)compose tau(8, 6) $]

= Nr.I-5.4
(a) Sei $X$ eine nichtleere Menge und $A subset X$ sowie $n in NN$, dann gelten:
#lemma[$(pset(A), triangle)$ ist eine Untergruppe der Gruppe $(pset(X) triangle)$]
#proof[
  1. $pset(A)$ ist nicht leer, da es mindestens das neutrale Element $e=nothing$ enthält
  2. $forall a,b in pset(A):a triangle b in pset(A)$
  3. Es gilt $forall a,b'in pset(A)$, da für $triangle$ alle Elemente selbstinvers sind und 2. gilt: $ a triangle a = (a without a) inter (a without a)= nothing $
]
#lemma[$(A_n,compose)$ mit $A_n= ({sigma in S_n|s g n (sigma)=1})$ ist eine Untergruppe der Gruppe $(S_N,compose)$]
#proof[
  1. $A_n$ ist nichtleer, da mindestens das neutrale Element $id$ enthalten ist:
  $ s g n (id)= (-1)^0=1 $
  $ =>id in A_n $
  2. Seien $sigma_a,sigma'_b in A_n$ mit
  $ sigma_a= tau_a_1 compose tau_a_2 compose ...compose tau_a_n compose id $ $
    sigma'_b= tau_b_k compose tau_b_(k-1)compose ...compose tau_b_1 compose id
  $
  wobei $n,k in NN$ sind und gerade sind. Dann ist $s g n(sigma_a compose sigma'_b)=1$, da
  $ sigma_a compose sigma'_b = tau_a_1 compose ... tau_a_n compose id compose tau_b_k compose ... compose tau_b_1 compose id $ $n+k$ Transpositionen, also eine gerade Anzahl an Transpositionen hat, und somit ist
  $ sigma_a compose sigma'_b in A_n $
]

(b) Sei $(G,star)$ eine Gruppe mit neutralem Element e und $(U_i,star)_(i in I)$ eine Familie von Untergruppen, wobei $I$ nicht die leere Menge ist, dann gilt:
#lemma[
  $(inter_(i in I)U_i,star)$ ist eine Untergruppe von $(G,star)$
]
#proof[
  1. Neutrales Element: $inter_(i in I)U_i$ ist nicht leer, da nach Lemma 7.43 des Skripts in jeder Untergruppe das gleiche neutrale Element e enthalten ist.
    2. Inverses: $forall a in inter_(i in I)U_i:forall i in I, a in U_i and a' in U_i$
  $ => a' in inter_(i in I)U_i $
  3. Abgeschlossenheit: $forall a,b in inter_(i in I)U_i: forall i in I, a in U_i and b in U_i$
  $ => a star b in U_i $
  $ => a star b in inter_(i in I)U_i $
]
(c) Sei $(G,star)$ eine Gruppe und $(U_1,star),(U_2,star)$ Untergruppen, dann gilt:
#lemma[
  $(U_1 union U_2,star)$ ist genau dann eine Untergruppe von $(G,star)$, wenn
  $ U_1 subset U_2 or U_2 subset U_1 $
]
#proof[
  Annahme:
  $ U_1 subset.not U_2 and U_2 subset.not U_1 $
  $ => exists a in U_1: a in.not U_2 and exists b in U_2: b in.not U_1 $
  $ => a star b in (U_1 union U_2, star) $
  $ => a star b in U_1 and a star b in U_2 $
  1. $=> a' star a star b in U_1$
  $ => b in U_1 $
  2. $a star b star b' in U_2$
  $ => a in U_2 $
  Das ist widersprüchlich zur Annahme, weshalb $U_1 subset U_2 or U_2 subset U_1$ gilt.
]
