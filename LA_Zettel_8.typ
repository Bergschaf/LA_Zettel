#import "Preamble.typ": *

= LA Zettel 7
Bearbeitet von Leon Krasniqi, Christian Krause, Silas Gaschler (Tutorium: Gregor Teupke (Mi 16:15))


== Aufgabe 4

#let span(var) = $angle.l #var angle.r$

#lemma[
Es sei $(K, +, dot)$ ein Körper, $(V, +, dot)$ ein Vektorraum über K und $E subset.eq V$.
  Es gilt:
  $ span("E") = {sum_{i=1}^n a_i v_i bar exists n in NN_0, forall i in [|1, dots, n|] (v_i in span(E), alpha_i in K)} =: M $
]
#proof[
  + $ span("E") subset.eq M$: Trivial mit $n = 1$ und  $alpha_1 = 1$
  + Zu zeigen $ M subset.eq span("E") $:
    Gilt genau dann, wenn:
    $ 
{sum_{i=1}^n a_i v_i bar exists n in NN_0, forall i in [|1, dots, n|] (v_i in span(E), alpha_i in K)}   subset.eq {sum_{i=1}^n a_i v_i bar exists n in NN_0, forall i in [|1, dots, n|] (v_i in E, alpha_i in K)} $ 
Zu zeigen: $ forall n in NN_0, v_i in span(E), alpha_i in K, exists n' in NN_0, exists v_i' in E, exists alpha_i' in K,quad  sum_(i = 1)^n alpha_i v_i = sum_(j = 1)^(n') alpha_j' v_j' $
Wir wissen, dass alle $v_i in span(E)$ als Linearkombination von Elementen aus E dargestellt werden können: 
$ exists n_i in NN_0, exists alpha_(i k) in K, exists v_(i k) in E, sum_(k = 0)^n_i alpha_(i k) v_(i k) = v_i $
  Wir können also schreiben:
  $ sum_(i = 1)^n alpha_i v_i = sum_(i = 1)^n alpha_i (sum_(k = 1)^n_i alpha_(i k) v_(i k)) quad "mit " v_(i k) in E $
  Um die zwei Summen in eine Zusammenzufassen schreiben wir: $n' = sum_(i = 1)^n n_i$. Um die Indizierung von $alpha_(i k)$ zu vereinfachen führen wir $j_(i k) = sum_(x = 1)^(i-1) n_i + k $ ein.
  Damit definieren wir $alpha_(j_(i j)) = alpha_i dot alpha_(i k)$ und $v_(j_(i k)) = v_(i k) $
  Insgesamt gilt dann:
  $ sum_(i = 1)^n alpha_i (sum_(k = 1)^n_i alpha_(i k) v_(i k)) = sum_(j = 1)^n' alpha_j v_j $
  Damit ist die zweite Inklusion bewiesen, da so jede Linearkombination von Elementen aus #span("E") als Linearkombination von Elementen aus $E$ dargestellt werden kann.
]

#lemma[
  $ span("E") = union.big { span(E_0) | E_0 subset.eq E, E_0 "ist endlich"} $
]

#proof[
  "$supset.eq$": Gilt, da $span(E_0) subset.eq span(E)$ für alle $E_0 subset.eq E$. \
  "$subset.eq$": Gilt, da $span(E)$ nur endliche Linearkombinationen erzeugt. Für alle $e in span(E)$ gibt es also ein $n$, sodass $e = sum_i^n alpha_i x_i$ mit ${x_i | i in [|1,n|]} subset.eq E$. 
  Da ${x_i | i in [|1,n|]}$ endlich ist, gibt es ein endliches $E_0 subset.eq E$ mit ${x_i | i in [|1,n|]} subset.eq E_0$. 
  Somit gibt es für jedes $e in span(E)$ ein $E_0 subset.eq E$, sodass $e in span(E_0)$.
]

== b)
=== i)

$ span((1,2)) "in " RR times QQ "über" QQ $
$ span((1,2)) = {(q, 2q) | q in QQ} $

== ii)

$ span({QQ \\ ZZ, ZZ}) "in" (pset(QQ, Delta, dot.circle)) "über" (ZZ_2, +_2, dot_2) $

$ span({QQ \\ ZZ, ZZ}) = {QQ \\ ZZ, ZZ, emptyset} $
== Aufgabe 5
=== a)
==== i)
Die Menge $E = {(1,2,3), (sqrt(2),sqrt(2),sqrt(2)),(1,1,1)}$ in $RR^3$ über $QQ$ ist linear unabhängig, da gelten muss:
$ 1 dot q_1 + sqrt(2) dot q_2 + 1 dot q_3 = 0 $
Da $sqrt(2) dot q$ für alle $q$ irrational ist, muss gelten:
$ q_3 = -q_1$ und $q_2 = 0$.
Mit der Gleichung für die zweite komponente folgt allerdings:
$ 2 dot q_1 - 1 dot q_1 = 0 => q_1 = q_3 = q_1 = 0 $ 
Damit ist $E$ linear unabhängig. 

==== II)
Die Menge $E = {e_x | x in X} union {1}$ in $(K^X, +, dot)$ über einem Körper $(K, +, dot)$ ist linear unabhängig, wenn $X$ nicht endlich ist.
+ Wenn $X$ endlich ist, gibt es endlich viele Charakteristische Funktionen $e_x$ und es gilt $sum_x e_x = 1$. Damit lösst sich 1 als endliche linearkombination der Vektoren $e_x$ darstellen und $E$ ist nicht linear unabhängig.
+ Wenn $X$ allerdings endlich ist, ist $sum_x e_x = 1$ eine undendlich linearkombination. 
  Da die Menge der charakteristischen Funktionen trivialerweise linear unabhängig ist, ist $E$ somit auch linear unabhängig.

==== iii)
Die Menge $E = {X \\ {x} | x in X} $ in $(pset(X), Delta, dot)$ über $(Z_2, +_2, dot_2)$ ist linear unabhängig, wenn $pset(X)$ unendlich ist:
+ Wenn $pset(X)$ endlich ist, kann die Menge $X \\ {y}$ ($y in X$ beliebig) als linearkombination von ${E \\ (X \\ {y})}$ dargestellt werden, da:
  $ (*) quad  (X \\ {a}) Delta (X \\ {b}) = (((X \\  {a}) \\ (X \\ {b})) union ((X \\ {b}) \\ (X \\ {a}))) = {a, b} $
  Damit gilt: 
  $ sum_(X \\ {x} in E \\ (X \\ {y})) X \\ {x} = union.big {x | X \\ {y}} = X \\ {y} $
  $E$ ist also nicht linear unabhängig.
+ Wenn $pset(X)$ unendlich ist, ist $E$ linear unabhängig, da jede endliche (!!) linearkombination aus Elementen von $E$ eine Menge von endlicher Mächtigkeit erzeugt (siehe $(*)$).
  Jedes Element von $E$ ist aber nicht endlich (da $X \\ {x}$ nicht endlich ist, wenn $X$ nicht endlich ist) und kann daher nicht als endliche linearkombination von Elementen von $E$ dargestellt werden.
  

=== b)

#lemma[
  In einer Linear unabhängigen Familie kann kein Elmement doppelt vorkommen.
]
#proof[
  Sei $f : I -> V$ eine Familie mit $f_i = f_j$. 
  Dann gilt $1 dot f_i - 1 dot f_j = 0$. 
  Die Implikation $ sum_i a_i v_i = 0 =>forall i, a_i = 0 $ kann also nichtmehr gelten, womit $f$ nicht linear unabhängig sein kann.
]

=== c)
#lemma[
  $V$ ist ein $K$ Vektorraum. Folgende Aussagen sind äquivalent:
  + $E subset.eq V$ ist eine linear abhängige Menge
  + Es gibt einen Vektor $v in E$ der als linearkombination von $E \\ {v}$ dargestellt werden kann.
]
#proof[
  "$=>$": 
    Wenn $E$ nicht linearabhängig ist gilt: $exists a_w, sum_(w in E) a_w w = 0$ mit $a_w eq.not 0$ für mindestens einen Vektor $w in E$. 
  Sei $v$ ein solcher Vektor mit $a_v eq.not 0$.
  $ sum_(w in E) a_w w = 0 \
    sum_(w in E) a_w w - a_v v = -a_v v \
    sum_(w in E \\ {v}) a_w w = -a_v v \
    sum_(w in E \\ {v}) (a_w dot (-a_v^(-1))) w = v \
  $
  $v$ kann also als Linearkombination von $E \\ {v}$ dargestellt werden.

  "$arrow.l.double$":
    Es gilt: $v = sum_(w in E \\ {v}) a_w w$ für ein bestimmtes $v$ und eine bestimmte Menge $a_w$. Nun kann die selbe Rechnung von oben rückwärts durchgeführt werden:
$ v = sum_(w in E \\ {v}) a_w w \
0 = sum_(w in E \\ {v}) a_w w - v \
0 = sum_(w in E) a_w quad "mit " a_v = -1
  $
  Damit gilt die Implikation $sum_(w in E) a_w w = 0 => forall w, a_w = 0$ nicht, da $a_v = -1$. 
  $E$ ist also linear abhängig.

]







