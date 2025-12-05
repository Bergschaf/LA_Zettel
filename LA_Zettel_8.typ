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



