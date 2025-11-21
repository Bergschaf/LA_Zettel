#import "Preamble.typ": *
= LA Zettel 6
Bearbeitet von Leon Krasniqi, Christian Krause, Silas Gaschler (Tutorium: Gregor Teupke(Mi 16:15))
= Aufgabe 6.3
a)
$ ZZ\/RR = {[a] = a + ZZ| a in RR} $
$ [a]tilde(+)[c] = [a + c] $
$ =>"neutrales Element" e = [0] $
Gesucht ist $b in RR$, sodass:
$ n[b] = [0]; n in NN $
$ iff b+...+b =n b= 0 ;n in NN $
$ => b = 0 $
$=>$ Das einzige Element mit endlicher Ordnung in $RR\/ZZ$ ist [0].

b)
#lemma[

  Sei $(G star)$ eine Gruppe und $E subset.eq G$ mit $chevron E chevron.r=G$ und $(N,star)$ untergruppe von $G$.

  Dann gilt: $N$ ist genau dann normalteiler von $(G,star)$, wenn $a star N = N star a$ für alle $a in E$ gilt.


]
#proof[

  $ forall a_(n)in E: N = a'_(n)star N star a_(n) (iff a_(n) star N = N star a_(n)) $
  Da $E$ ein Erzeugendensystem von $G$ ist, gilt auch:
  $ forall b in G: b = a_(1)star ...star a_(n) $
  $ b' = a'_(n)star...star a'_(1) $
  $
    => b' star N star b =underbrace(a'_(n)star underbrace(...star underbrace(a'_(1) star N star a_(1), N) star ..., N) star a_(n), N) = N
  $



]

c)

geg:
$ (G,star)" ist eine Gruppe" $
$ (N_(1),star),(N_(2),star) "sind Untergruppen von "G $
$ N_(1) subset.eq N_(2) $

#lemma[

  $ (G \/N_(2),tilde(star))" ist Untergruppe von " (G \/N_(1),tilde(star)) $

]
#proof[

  Da $N_(1) subset.eq N_(2)$ gilt:
  $ N_(1)=N_(2)or exists n in N_(2) : n in.not N_(1) $
  Falls $N_(1)=N_(2)$ dann ist auch $(G \/N_(2),tilde(star)) = (G \/N_(1),tilde(star))$

  Falls $exists n in N_(2) : n in.not N_(1)$ gilt:
  $ forall a in G: a star n in a star N_(2) and a star n in.not a star N_(1) $
  $ => a star N_(2) != a star N_(1) $
  $ => (G \/N_(2),tilde(star))" ist nicht Untergruppe von " (G \/N_(1),tilde(star)) $

]
d)
$
  \( G \, star.op \) upright(" Gruppe") \, #h(2em) \( N \, star.op \) upright(" Normalteiler") \, #h(2em) a star.op N = N star.op a
$

#lemma[
  $G \/ N$ ist abelsch, wenn $K \( G \) subset.eq N$.


]
Es gilt für alle $a in G$: $ a star.op N = N star.op a . $

$
  G \/ N = { thin a star.op N divides a in G thin } \, #h(2em) \[ a \] thin hat(star.op) thin \[ b \] = \[ a star.op b \] = \( a star.op b \) star.op N .
$
#proof[

  Zu zeigen:
  $
    \[ a \] thin tilde(star.op) thin \[ b \] = \[ b \] thin tilde(star.op) thin \[ a \] quad arrow.l.r.double quad K \( G \) subset.eq N .
  $

  $ \[ a \] thin tilde(star.op) thin \[ b \] = \[ b \] thin tilde(star.op) thin \[ a \] $

  $ arrow.l.r.double quad \[ a star.op b \] = \[ b star.op a \] $

  $ arrow.l.r.double quad \( a star.op b \) star.op N = \( b star.op a \) star.op N $

  $ arrow.l.r.double quad N star.op \( a star.op b \) = N star.op \( b star.op a \) . $

  $
    arrow.l.r.double { thin c star.op a star.op b divides c in N thin } = { thin d star.op b star.op a divides d in N thin }
  $

  $ arrow.l.r.double forall c in N #h(0em) exists d in N : #h(0em) c star.op a star.op b = d star.op b star.op a $

  $
    arrow.l.r.double forall c in N #h(0em) exists d in N : #h(0em) c star.op a star.op b star.op \( b star.op a \)' = d .
  $

  Da $c' in N$:
  $
    arrow.l.r.double forall c in N #h(0em) exists d in N : #h(0em) a star.op b star.op a' star.op b' = underbrace(c' star.op d, in N) .
  $

  $ arrow.l.r.double quad a star.op b star.op a' star.op b' in N quad arrow.l.r.double quad K \( G \) subset.eq N . $

]
