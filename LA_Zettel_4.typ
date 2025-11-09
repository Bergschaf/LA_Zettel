#import "Preamble.typ" : *
= LA Zettel 3

== Aufgabe 2
Es seien $X$ eine überabhählbare Menge und $Y subset.eq X$ eine abzählbar unendliche Menge.
#lemma[
  $X \\ Y$ ist überabzählbar
]
#proof[
  Contraposition: Zu zeigen: Wenn $X \\ Y$ nicht überabzählbar ist, dann ist $X$ nicht überabzählbar. \
Wir wissen $X = X \\ Y union Y$. Wenn $X \\ Y$ abzählbar ist (und $Y$ laut annahme abzählbar ist), dann ist $X$ als vereinigung von abzählbaren Mengen auch abzählbar, also nicht überabzählbar.
]
#lemma[
  Jede überabzählbare Menge $X$ enthält eine abzählbar unendliche teilmenge.
]<lemma2>
#proof[
Sei $f : #pset (X \\ Y) -> X$ eine Auswahlfunktion (Existenz folgt aus AOC). Definiere die Folge
  $ x_0 := f(X) \
    x_n := f(X \\ {x_0, x_1, dots, x_(n-1)}) $
  Die Folge ist wohldefiniert, da $X \\ A$ für jede abzählbare Menge A überabzählbar groß ist.
  Die Folgenglieder $(x_n)_(n in NN)$ bilden eine abzählbar unendliche Teilmenge von $X$, da sie sich nicht wiederholen.
]
#corollary([
  Die überabzählbare Menge $X \\ Y$ enthält eine abzählbar unendliche Teilmenge.
])

#lemma[
  $X$ und $X \\ Y$ sind gleichmächtig.
]
#proof[
  Wir müssen eine Bijektion $f : X -> X\\Y$ angeben.
  Sei $A subset.eq X \\Y$ eine abzählbar unendliche Teilmenge von $X \\Y$, die nach Lemma @lemma2 existiert.
  Da die Mengen $Y$ und $A$ abzählbar sind, können sie durch die bijektiven Funktionen: $Y_n : NN -> Y$ und $A_n : NN -> A$ beschrieben werden.
  $ f^(-1)(x) &= cases(x "falls " x in X \\ Y \\ A, A_n "falls" exists n in NN : A_(2n) = x, Y_n "falls" exists n in NN : A_(2n + 1) = x)  \
   f(x)& = cases(x "falls" x in X \\ Y \\ A, A_(2n) "falls" exists n in NN : A_(n) = x, A_(2n + 1) "falls" exists n in NN : Y_n = x ) $    
  Auf $X \\ Y \\A$ sind $f$ und $f^(-1)$ offensichtlich invers zueinander. \
  $ f^(-1)(f(A_n)) = f^(-1)(A_(2n)) = A_n quad forall n in NN $
  $ f^(-1)(f(Y_n)) = f^(-1)(A_(2n+1)) = Y_n quad forall n in NN $
  $ f(f^(-1)(A_(2n))) = f(A_n) = A_(2n) quad forall n in NN $
  $ f(f^(-1)(A_(2n + 1))) = f(Y_n) = A_(2n + 1) quad forall n in NN $
  $f$ besitzt mit $f^(-1)$ ein links- und rechtsinverses $=>$ $f : X -> X \\ Y$ ist eine Bijektion, also sind $X$ und $X \\ Y$ gleichmöchtig.
]

== Aufgabe 5

#lemma[
  Linksinverse in Monoiden sind im allgemeinen nicht Eindeutig.
]
#proof[
  Wir betrachten den Monoid $(NN_0^NN_0, compose)$ der Funktionen auf den Natürlichen Zahlen (mit der 0) verknüpft durch verkettung mit dem Neutralen Element $id : x mapsto x$.
  Sei $f(n) = n + 2$. Die Funktionen $ g(n) = cases(n "für " n > 1, 0 "für " n = 0) \
  h(n) = cases(n "für" n > 1, 42 "für" n = 0) $
  sind beide linke Inverse zu $f$, sie sind auf dem Wertebereich von f gleich. 
  Es gilt aber trotzdem $g eq.not h$, da $g(0) eq.not h(0)$
]

#lemma[
  Wenn $a$ links- und rechtsinvertierbar ist, dann ista invertierbar und jedes links- oder rechtsinverse Element zu a gleicht dem einedeutigen Inversen von $a$.
]
#proof[
  Sei $l in H$ ein Linksinverses von a, also $l star a = e$ und $r in H$ ein Rechtsinverses von a, also $a star r = e$.
  $ (l star a) star r = e star r = r $
  $ l star (a star r) = l star e = l $
  Da $(l star a) star r = l star (a star r)$ (Assoziativität) gilt, gilt $r = l$. Also gibt es ein Element $a' = r = l$, für das gilt $a star a' = a' star a = e$. Damit ist a invertierbar.
  Da für $l$ und $r$ vorher beliebige links- und rechtsinverse gewählt wurden, folgt, dass alle links- und rechtsinversen von a, gleich $a'$ sind.
]
