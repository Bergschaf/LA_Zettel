#import "Preamble.typ": *
= LA Zettel 6
Bearbeitet von Leon Krasniqi, Christian Krause, Silas Gaschler (Tutorium: Gregor Teupke(Mi 16:15))
= Aufgabe 6.3
a)

b)

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

