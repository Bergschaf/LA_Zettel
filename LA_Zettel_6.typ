#import "Preamble.typ": *
= LA Zettel 6
Bearbeitet von Leon Krasniqi, Christian Krause, Silas Gaschler (Tutorium: Gregor Teupke (Mi 16:15))
= Aufgabe I-6.1 (Homomorphismen)

(a)

(i)
#lemma[
  $f: (RR_(>0), dot) -> (RR,+), f(x):= ln(x)$ ist ein Gruppenisomorphismus.
]
#proof[
  1. $(RR_(>0),dot),(RR,+)$ sind Gruppen.
  2. Homomorphiesatz ist erfüllt:
  $ forall a,b in RR_(>0): ln(a dot b) = ln(a) + ln(b) $
  3. $f(x)=ln(x)$ ist auf $RR_(>0) -> RR$ bijektiv.
]
(ii)
#lemma[
  $f: (QQ,+) -> (RR,+), f(x):=3x+1$ ist kein Homomorphismus.
]
#proof[
  $ forall a,b in QQ: $
  $ f(a+b)=3(a+b)+1 $
  $ f(a)+f(b)=3a+1+3b+1=3(a+b)+2 $
  $ => f(a+b)!=f(a)+f(b) $
  Der Homomorphiesatz ist somit nicht erfüllt.
]
(iii)
#lemma[
  $f:(ZZ_2,+_2) -> ({top, bot}, X O R),f(z):=(x>0)$ ist ein Gruppenisomorphismus.
]
#proof[
  1. $(ZZ_2,+_2),({top,bot},X O R)$ sind abelsche Gruppen.
  2. Homomorphiesatz mit $f(a+_2 b)=f(a) X O R f(b)$ ist für alle $a,b in ZZ_2$ erfüllt:
  Fall 1: $a=b=0$:
  $ f(0+_2 0)=f(0) =(0>0) = bot $
  $ f(0)X O R f(0)=(0>0)X O R (0>0)=bot X O R bot = bot $
  $ => f(0+_2 0)=f(0) X O R f(0) $
  Fall 2: $a=0,b=1$, bzw. $a=1,b=0$:
  $ f(1+_2 0)=f(1)=(1>0)=top $
  $ f(0)X O R f(1)=(0>0)X O R (1>0)=bot X O R top= top $
  $ => f(1+_2 0)=f(1)X O R f(0) $
  Fall 3: $a=b=1$:
  $ f(1+_2 1)=f(0)=(0>0)=bot $
  $ f(1)X O R f(1)=top X O R top=bot $
  $ => f(1+_2 1)=f(1) X O R f(1) $
  3. Die Bijektivität ist gegeben, da die  3 Fälle alle Möglichkeiten abdecken.
]
(iv)
#lemma[
  $f:(S_3,compose) -> (pset(RR),triangle)$ ist ein Monoidhomomorphismus.
]
#proof[
  1. $(S_3,compose)$ ist eine Gruppe, aber $(pset(RR),triangle)$ ist nur ein Monoid, da nicht jedes Element ein Inverses und als neutrales Element $e=emptyset$ besitzt.
  2. Homomorphiesatz mit $f(sigma_a compose sigma_b)=f(sigma_a) triangle f(sigma_b)$ ist für alle $sigma_a sigma_b in S_3$ erfüllt:
  Fall 1: $sigma_a,sigma_b in.not A_3$ mit $A_3:={sigma in S_3 | s g n(sigma)=1}$:
  $ f(sigma_a compose sigma_b)=[0,- s g n(sigma_a compose sigma_b)]=[0,-1]=emptyset $
  $ f(sigma_a)triangle f(sigma_b)=[0,1] triangle [0,1]= emptyset $
  $ => f(sigma_a compose sigma_b) = f(sigma_a) triangle f(sigma_b) $
  Fall 2: $sigma_a in.not A_3,sigma in A_3$ bzw. $sigma_a in A_3, sigma_b in.not A_3$:
  $ f(sigma_a compose sigma_b) = [0,-s g n(sigma_a compose sigma_b)]=[0,1] $
  $ f(sigma_a) triangle f(sigma_b)=[0,-s n g(sigma_a)] triangle [0,-s n g(sigma_b)]= [0,1] triangle [0,-1]=[0,1] $
  $ => f(sigma_a compose sigma_b)= f(sigma_a) triangle f(sigma_b) $
  Fall 3: $sigma_a,sigma_b in A_3$
  $ f(sigma_a compose sigma_b)=[0, -s g n(sigma_a compose sigma_b)]=[0,-1]=emptyset $
  $ f(sigma_a) triangle f(sigma_b)= [0,-s g n(sigma_a)] triangle [0,-s g n(sigma_b)]= [0,-1] triangle [0,-1]= emptyset $
  $ => f(sigma_a compose sigma_b)=f(sigma_a) triangle f(sigma_b) $
  3. Die Abbildung $f(sigma)=[0,-s g n(sigma)]$ ist nicht surjektiv, da nicht auf alle Intervalle aus $pset(RR)$ abgebildet wird, sondern nur auf $emptyset,[0,-1] in pset(RR)$.
]
(b) Es seien $f: G_1->G_2$ un $g: G_2->G_3$ (Halbgruppen-, Monoid-, Gruppen-)isomorphismen mit $(G_1,star),(G_2,square)$ und $(G_3, circle.filled)$ und $a_1,b_1 in G_1$, $a_2,b_2 in G_2$.
#lemma[
  Dann ist auch $f^(-1)$ ein solcher Isomorphismus.
]
#proof[
  $ f^(-1)(a_2) star f^(-1)(b_2)=a_1 star b_1 $
  $ =f^(-1)(f(a_1 star b_1)) $
  $ =f^(-1)(f(a_1) square f(b_1)) $
  $ =f^(-1)(a_2 square b_2) $
  $ => f^(-1)(a_2) star f^(-1)(b_2) = f^(-1)(a_2 square b_2) $
]
#lemma[
  Dann ist auch $g compose f$ ein solcher Isomorphismus.
]
#proof[
  $ g(f(a_1 star b_1))=g(f(a_1)square f(b_1)) $
  $ = g(a_2 square b_2) $
  $ = g(a_2) circle.filled (b_2) $
  $ =g(f(a_1)) circle.filled g(f(b_1)) $
  $ => g(f(a_1 star b_1))=g(f(a_1)) circle.filled g(f(b_2)) $
]
