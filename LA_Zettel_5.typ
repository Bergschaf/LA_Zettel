#import "Preamble.typ" : *

= LA Zettel 5
== Aufgabe 1
Entscheiden, ob die Beispiele aus Aufgabe 4. Gruppen sind. \
(i): Der Monoid $(RR^X, +)$ ist eine Gruppe, das invers kann punktweise gebildet werden: Für alle $g in RR^X$ gilt $g^(-1)(x) = -g(x)$ und damit $g(x) + g^(-1)(x)= g(x) - g(x) = 0$ \

(ii): Der Monoid $(pset(cal(X)), inter)$ ist keine Gruppe, weil alle Elemente (außer $X$) kein Inverses besitzen, da für alle $a,b in pset(cal(X))$ gilt:
$ a inter b = X => a = b = X $
(iii): Der Monoid $(pset(cal(X)), triangle)$ ist eine Gruppe, da jedes Element invertierbar ist. Für alle $x in pset(cal(X))$ gilt $x^(-1) = x$, da
$ x triangle x = (x \\ x union x \\ x) = emptyset union emptyset = emptyset $
(IV): Der Moniod $(X^X, compose)$ ist im allgemeinen (für $\# X > 1$) keine Gruppe, da nicht alle Funktionen $f : X -> X$ invertierbar sind (Ein gutes Beispiel dafür sind konstante Funktionen) und damit nicht alle Elemente des Monoids ein inverses Element besitzen.

(V): Der Monoid $(ZZ^2, ((x_1, x_2), (y_1, y_2)) mapsto (x_1 dot y_1, x_2 + y_2)))$ ist keine Gruppe, da nicht alle Elemente invertierbar sind. Zum Beispiel das Element $(2,2)$. Es müsste ein Element $(x_1, x_2) in ZZ^2$ geben, sodass $x_1 * 2 = 1$ und $x_2 + 2 = 0$. Ein solches $x_1$ gibt es allerdings nicht in $ZZ$ \
=== b)

$(pset(cal(G)), tilde(star))$ ist keine Gruppe. Sei $G$ die gruppe der ganzen Zahlen $ZZ$ mit der addition $+$.
Die Menge ${0} in pset(ZZ)$ wäre das Neutrale Element der Gruppe $(pset(cal(G)), tilde(star))$, da $ {a + 0 | a in A} = A quad forall A in pset(ZZ) $
Es sind aber nicht alle Elemente der Gruppe $(pset(ZZ), tilde(+))$ invertierbar, da $ a + b = a + c => b = c quad forall a b c in ZZ $
Wenn wir also eine Beliebige Menge $A in pset(ZZ)$ mit $\# A > 1$ punktweise mit einer einelementigen Menge ${c}$ addieren, dann gilt $\# (A tilde(+) {c}) = \#A$.\
Für eine Menge $B in pset(ZZ)$ mit $B = C union D$ gilt $A tilde(+) B = A tilde(+) C union A tilde(+) D$.
Daraus folgt, dass die Kardinalität von $A$ durch die Punktweise Addition einer anderen Menge nur steigen kann:\
Sei $B in pset(ZZ)$ mit $B = {c} union D$:
$ \# (A tilde(+) B) = \# (A tilde(+) {c} union A tilde(+) D)
>= \# (A tilde(+) {c}) = \# A $
Da das neutrale Element die Menge ${0}$ ist, gibt es für alle Mengen $A in pset(ZZ)$ mit $\# A > 1$ kein inverses Element, da es dafür eine Menge $B in pset(ZZ)$ geben müsste, sodass $\# (A tilde(+) B) = 1$, was aber nicht möglich ist.\

Notitz: Oben wurde angenommen, dass $\# B >= 1$. Falls $B = emptyset$ gilt $A tilde(+) emptyset = emptyset$. Damit kann $emptyset$ auch nicht das inverse Element von $A$ sein. $emptyset$ kann auch nicht das neutrale Element sein, da $A tilde(+) emptyset = emptyset eq.not A$

#let links_a = $attach(*, bl: a)$

=== c)

#lemma[
  Ist $(G, star)$ eine Gruppe, dann sind alle Links- und Rechtstranslationen #links_a und $star_a$ bijektionen für alle $a in G$.
]
#proof([

  Für alle $a in G$ ist zu zeigen:\
  Die Funktion $#links_a : G -> G := x mapsto a star x$ ist invertierbar. \
  Die inverse Funktion von #links_a ist gegeben durch $attach(*, bl: a^(-1))$, da: $a star (a^(-1) star x) = x$ und $a^(-1) star (a star x) = x$ für alle $x in G$ gilt und $a^(-1)$ aufgrund der Gruppenstruktur exsitiert. \
  Das selbe gilt für die Rechtstranslation: Das Inverse der Funktion $star_a$ ist gegeben durch $star_(a^(-1))$, da $(x * a) * a^(-1) = x$ und $(x * a^(-1)) * a = x$ für alle $x in G$.
])

#lemma[
  Sei $(H, star)$ eine nichtleere Halbgruppe. Wenn für alle $a in H$, die Links- und Rechtstranslationen #links_a und $star_a$ surjektive Abbildungen sind, dann ist $(H, star)$ eine Gruppe.
]
#proof([
  Aus der Surjektivität von #links_a und $star_a$ folgt:
  $ forall a, x in H, exists y in H, a * y = x quad (i) $
  $ forall a, x in H, exists y in H, y * a = x quad (i i) $
  Sei $a in H$ beliebig aber fest. Es gibt ein $e in H$, sodass $a * e = a$ (folgt aus $(i)$).
  Weiter gibt es für jedes $g in H$ ein $y in H$, sodass $y * a = G$ (folgt aus $(i i)$).
  Es gilt also $ g * e = (y * a) * e = y * (a * e) = y * a = g $
  Da $g$ beliebig gewählt war ist $e$ Rechtsneutral zu allen Elementen von H. \
  Analog erhält man ein $e'$, das Linksneutral zu allen Elementen von H ist, es gilt also
  $ g * e = e' * g = g quad forall g in H $
  Daraus folgt: $e = e' * e = e'$. Es gibt also ein Neutrales Element in $H$, das wir nun als $e$ bezeichnen werden. \
  Um zu zeigen, dass $(H, star)$ eine Gruppe ist, fehlt noch, dass es für jedes Element ein inverses gilt. \
  Aus $(i)$ folgt, dass es für jedes $a in H$, ein Element $a'$ gibt, sodass $a * a' = e$.
  Aus $(i i)$ folgt, dass es für jedes $a in H$ ein Element $a''$ gibt, sodass $a'' * a  = e$.
  $ &a * a' = e  \
   <=>& a'' * (a * a') = a'' \
   <=>&  (a'' * a) * a' = a'' \
    <=>& e * a' = a'' \
 <=>&  a ' = a''
  $
  Es gibt also für jedes $a in H$ ein inverses Element $a'$, sodass $a * a' = a' * a = e$




])

== Aufgabe 4
Es sei $(G, *)$ eine Gruppe.
#let ord = emph[ord]
#lemma[
  $ord(a) = ord(a^(-1))$
]

#proof[
Fall 1: $ord(a)$ ist endlich:
Sei $n = ord(a)$. Es gilt
  $ a^n = 1$. \
  Außerdem gilt $ 1 = a^n * (a^(-1))^n = 1 *  (a^(-1))^n = (a^(-1))^n $
  Daraus folgt, dass $ord(a^(-1))$ maximal n ist.
  Im Folgenden zeigen wir, dass $ord(a^(-1))$ mindestens n ist. \
  Sei also $ord(a^(-1)) = m$ für ein $m < n$. Dann gilt $(a^(-1))^m = 0$ und
  $ 1 = a^m * (a^(-1))^m = a^m * 1 = a^m $
  Da $ord(a) > m$ ist dies ein Widerspruch.

Fall 2: $ord(a)$ ist unendlich, d.h. es gibt kein $n in NN$, sodass $a^n = 1$.\
  Wir zeigen nun durch einen Widerspruch, dass $ord(a^(-1))$ auch unendlich sein muss.\
  Sei also $(a^(-1))^m = 1$ für ein $m in NN$. Dann gilt für alle $n > m$:
  $ 1 = a^n * (a^(-1))^n = a^n * (a^(-1))^(n-m) = a^m $
  Das ist ein Widerspruch, da $ord(a)$ unendlich ist, es kann also kein $m$ geben, sodass $a^m = 1$.
]


#lemma[
  $ [(K(G), *) = ({1}, *)] <=> (G, *) "ist abelsch" $
]
#proof[
  $==>$:
  Aus $[(K(G), *) = ({1}, *)]$ folgt, dass $ {a * b * a^(-1) * b^(-1) | a,b in G} = {1} $
  da die Erzeugermenge der Gruppe $({1}, *)$ die Menge mit ausschließlich dem leeren Element ist.\
  Es gilt also:
  $ a * b * a^(-1) * b^(-1) = 1 quad forall a,b in G \
<=> a * b * a^(-1) * b^(-1) * b * a = b * a quad forall a,b in G \
  <=> a * b = b * a quad forall a,b in G $
  Das ist genau die Bedingung, die $G$ zu einer abelschen Gruppe macht. \
  $<==$: In einer abelschen Gruppe gilt $a * b * a^(-1) * b^(-1) = 1$ für alle $a,b in G$.
  Damit ist $ K(G) = angle.l {a * b * a^(-1) * b^(-1) | a,b in G} angle.r=angle.l {1 | a,b in G}angle.r = angle.l{1}angle.r = {1} $
 da die von ${1}$ erzeugte Untergruppe von $G$: $({1},*)$ ist.

]
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
