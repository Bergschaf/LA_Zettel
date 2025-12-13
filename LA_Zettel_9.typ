#import "Preamble.typ": *

= LA Zettel 8
Bearbeitet von Leon Krasniqi, Christian Krause, Silas Gaschler (Tutorium: Gregor Teupke (Mi 16:15))
#pagebreak()

= Aufgabe 2

Sei $(K, +, dot)$ ein Körper, $X$ eine nichtleere Menge und $(K^X, + ,dot)$ der Vektorraum der Funktionen von X nach K über K mit den Punktweisen verknüpfungen.

#lemma[
  Falls $X$ endlich ist gilt:
  $ dim_K (K^X) = \# X $

]
#proof[
  Sei $B_X$ folgende Familie in $K^X$: $ B(x_0) : X -> K^X := x mapsto cases(1_k "falls" x = x_0, 0_k "sonst") $
  Zu zeigen: $B_X$ ist eine Basis von $K^X$ und $\# B_X = \# X$.
  Die zweite Aussage ist trivial, für die erste Aussage benötigen wir zunächst die Lineare Unabhängigkeit von B.

  Sei 
  $ sum_(x_0 in X) alpha_x B(x_0) = 0_(K^X) $
  Das gilt, wenn 
  $ forall x' in X, (sum_(x_0 in X) alpha_x_0 B(x_0))(x') = 0_K $
  Da alle Summenglieder mit $x' eq.not x_0$ sowieso verschwinden, können wir auch schreiben:
  $ forall x' in X, alpha_x' B(x_')(x') = alpha_x' dot 1_K = 0_K $
  Damit ist $B_X$ linear unabhängig.

  Nun gilt es noch zu zeigen, dass $angle.l B_X angle.r = K^X$.
  Sei $f in K^X$. Dann setzen wir $a_x = f(x)$.
  Es gilt nun:
  $ sum_(x_0 in X) alpha_x_0 B_x_0 = f \
<=>  (sum_(x_0 in X) f(x_0) B_x_0)(x) = f(x) quad forall x in X \
<=> f(x) B(x) = f(x) dot 1_k = f(x) quad forall x
$
  Damit können alle Elemente von $K^X$ durch die Basis erzeugt werden.
]
#lemma[
  Falls $X$ unendlich ist gilt:
  $ dim_K (K^X) = infinity $
]
#proof[
  Zu zeigen: Es gibt eine Unendliche linear unabhängige Familie $B_X subset.eq K^X$. Damit kann es keine endliche Basis geben, wodurch die Unendlichkeit der Dimension gezeigt ist.
  Sei $B_X$ dafür folgende Familie in $K^X$: $ B(x_0) : X -> K^X := x mapsto cases(1_k "falls" x = x_0, 0_k "sonst") $.
  Zu zeigen: $B_X$ ist linear unabhängig. Das funktioniert genau gleich wie im Beweis drüber.
]
=== (ii)
Sei nun:
$ U := {f in K^X | f(x_0) = 0} $
$ W := {f in K^X | f(x) = f(y) forall x, y in X} $

#lemma[
  $dim_K(U) = dim_K(K^X) - 1$ (also $infinity$ falls $X$ unendlich ist)
]
#proof[
  Sei $X' = X \\ {x_0}$. 
  Sei $B_X'$ folgende Familie in $K^X'$: $ B(x') : X' -> K^X := x mapsto cases(1_k "falls" x = x', 0_k "sonst") $
  Zu zeigen: $B_X'$ ist eine Basis von U: Gilt offensichtlich, da alle Elemente außer $x_0$ einmal mit der $1_K$ getroffen werden.
  Damit ist $ dim_K (U) = \# B_X' = \# X' = \# X - 1 = dim_K (K^X) $
]
#lemma[
  $dim_K(W) = 1$
]
#proof[
  Die Menge der Konstanten Funktionen $W$ wird durch die Menge $B = {x mapsto 1_k}$ erzeugt. Damit hat $W$ eine Dimension von 1.
]

#lemma[
  $ dim_K (U inter W) = dim_K ({x mapsto 0_K}) = 0 $
]
#proof[
  Gilt, da $U inter W$ nur den Nullvektor enthält und damit $U inter W = angle.l {} angle.r $
]

== b)
#lemma[
Sei $(K, +, dot)$ und $(V, +, dot)$ ein K-Vektorraum. $V$ ist genau dann K-endlichdimensional, wenn $V$ endlich ist.

Dann gilt außerdem: $\# V = \# K^(dim_K (V))$.
]
#proof[
  Sei $B$ eine Basis von $V$. Da eine Basis Vektoren eindeutig erzeugt, gilt:
  $ V = union.big_(b in B) b dot K = union.big.plus_(b in B) b dot K $
  ($union.plus$ meint die Disjunkte Vereinigung).\

 "$=>$":
  Wenn $B$ endlich ist (also $V$ endlichdimensional), dann ist $V$ offensichtlich endlich, da jede Skalarmultiplikation $b dot K$ nur endlich viele Elemente ertzeugt. \
  "$arrow.double.l$": Wenn V endlich ist, dann muss auch $B$ endlich sein, da die disjunkte Vereinigung sonst unendlich viele Elemente erzeugen würde. Da $B$ endlich ist, ist dann auch $V$ endlichdimensional. \

  Wenn $B$ (und damit auch $V$) endlich ist, gilt:
  $ \# V = \# union.big.plus_(b in B) b dot K = product_(b in K) \# b dot K = product_(b in K) \# K = (\# K)^(\# B) = (\# K)^(dim_K (V)) $ 
  

   
]
