#import "Preamble.typ" : *

= LA Zettel 5
== Aufgabe 1
Entscheiden, ob die Beispiele aus Aufgabe 4. Gruppen sind. \
(i): Der Monoid $(RR^X, +)$ ist eine Gruppe, das invers kann punktweise gebildet werden: Für alle $g in RR^X$ gilt $g^(-1)(x) = -g(x)$ und damit $g(x) + g^(-1)(x)= g(x) - g(x) = 0$ \

(ii): Der Monoid $(pset(cal(X)), inter)$ ist keine Gruppe, weil alle Elemente (außer $X$) kein Inverses besitzen, da für alle $a,b in pset(cal(X))$ gilt:
$ a inter b => a = b = X $
TODO genauer \
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


=== c)
TODO

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
