#import "Preamble.typ" : *

= LA Zettel 7
Bearbeitet von Leon Krasniqi, Christian Krause, Silas Gaschler (Tutorium: Gregor Teupke (Mi 16:15))

== Aufgabe 1

== Aufgabe 2

== Aufgabe 3

== Aufgabe 4
=== a)
==== i)
$NN$ bildet kein Ideal in $(ZZ, +, dot)$, da $NN$ kein Unterring ist (nicht unter additiver Inversbildung abgeschlossen). $-42 in.not NN$

==== ii)
$2ZZ = {2k | k in ZZ}$
#lemma[
Die ganzen geraden Zahlen $2ZZ$ bilden ein Ideal in $(ZZ, +, dot)$. ]
#proof[
  Die ganzen geraden Zahlen sind ein Unterring von $(ZZ, +, dot)$:\
  Zu zeigen:
  $ a - b in 2ZZ, forall a, b in 2ZZ$. Gilt, da $exists k_a in ZZ, a = 2k, forall a in 2ZZ$.
  $ 2k_a - 2k_b = 2(k_a-k_b) in 2ZZ $
  Zu zeigen: $a dot b in 2ZZ, forall a,b in 2ZZ$. Gilt, da
   $ 2k_a dot 2k_b = 2 dot (2 dot k_a dot k_b) in 2ZZ $
  Zu zeigen: $z dot a in 2ZZ and a dot z in 2ZZ, forall a in 2ZZ, z in ZZ$ 
  $ z dot a = z dot 2 k_a = 2 (z dot k_a) in 2ZZ $
  $ a dot z = 2 k_a dot z = 2(k_a dot z) in 2ZZ $
]

== iii)
TODOTODOTODOTDOTODOTODO
== b)

#lemma[
  Es sei $(R, +, dot)$ ein Ring und $E subset.eq R$.
  $ (E) = {sum_i^n a_i | exists n in NN_0, forall i = 1, dots, n quad (a_i  in E union -E union R E union E R union R E R)} = M $ (Wir nennen die Menge rechts ab sofort M). Sei außerdem $M_0 = E union -E union R E union E R union R E R$.
]
#proof[
  1. Zu zeigen $ (E) subset.eq M$. Es genügt zu zeigen, dass $M$ ein Ideal in $R$ ist und $E subset.eq M$.
  Zu zeigen: $a - b in M, forall a, b in M$. 
  $ a - b = (sum_i^n a_i) - (sum_j^m b_j) \ 
  = (sum_i^n a_i) + (sum_j^m -b_j) \
  "Sei " a_(i+n) = -b_j quad forall j in [|1,m|] \
  = sum_i^(n + m) a_i
  $
  Zu zeigen: $-b_j in M_0 quad forall b_j in M_0 $
    + $b_j in E => -b_j in -E$ 
    + $b_j in -E => -b_j in E$
    + $ b_j in R E => exists r in R, exists e in E, b_j = r dot e \
        -b_j = -(r dot e) = -r dot e in R E quad "da " -r in R  $
    + $ b_j in E R => exists r in R, exists e in E, b_j = e dot r \
        -b_j = -(e dot r) = e dot (-r) in R quad "da " -r in R $
    + $ b_j in R E R => exists r_1, r_2 in R, exists e in E, b_j = r_1 dot e dot r_2 \
      -b_j = -(r_1 dot e dot r_2) = -r_1 dot e dot r_2 in R quad "da " -r_1 in R $
  Zu zeigen: $r dot m in M and m dot r in M quad forall m in M forall r in R$.
    $ r dot m = r dot (sum_i^n m_i) = sum_i^n r dot m_i $
    Zu zeigen: $r dot m_i in M_0 quad forall m_i in M_0$
    + $m_i in E => r dot m_i in R E $
    + $ m_i in -E => exists e in E, m_i = (-e), quad r dot  m_i = r dot (-e) = -r dot e in R E quad "da " -r in R $ 
    + $ m_i in R E => exists r_1 in R, exists e in E, r dot m_i = r dot (r_1 dot e) = (r dot r_1) dot e in R E quad "da " r dot r_1 R $
    + $ m_i in E R => exists r_1 in R, exists e in E, r dot m_i = r dot (e dot _r_1) = r dot e dot r_1 in R E R quad "da " r, r_1 in R $
    + $m_i in R E R => exists r_1, r_2 in R, exists e in E, r dot m_i = r dot (r_1 dot e dot r_2) = (r dot r_1) dot e dot r_2 in R E R $ 
  Da $E subset.eq M$ trivial ist, wissen wir nun, dass M ein Ideal in R mit $E subset.eq M$ ist, d.h. nach der Definition eines erzeugten Integrals gilt $(E) subset.eq M$
  #line()
  Zu zeigen: $M subset.eq (E)$ d.h. $forall a_i in M_0, sum_i^n a_i in (E)$.
  Da $(E)$ unter endlicher Addition abgeschlossen sein muss, genügt es zu zeigen, dass alle $a_i in M_0$ in $(E)$ enthalten sind.
  + $a_i in E => "trivial"$
  + $a_i in -E => a_i in E quad "da " (E) "unter additiver inversbildung abgeschlossen sein muss"$
  + $a_i in R E ... $
]

== Aufgabe 5

== Aufgabe 6

== Aufgabe 7
