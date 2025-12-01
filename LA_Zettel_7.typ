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
#lemma[
  Seien $X$ und $Y$ Mengen mit $Y subset.eq X$. $pset (Y)$ bildet ein Ideal in $(pset (X), Delta, inter)$.
]
#proof[
  + Zu zeigen: $a Delta b in pset (Y) quad forall a,b in pset (Y)$. \
    $ a Delta b = a \\ b inter b \\ a subset.eq a union b subset.eq Y => a Delta b in pset (Y) $
  + Zu zeigen $ a inter x in pset (Y) quad forall a in pset (Y), forall x in pset (X)$
    $ a inter x subset.eq a subset.eq Y => a inter x in pset (Y) $

]
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
  + $a_i in -E => a_i in (E) quad "da " (E) "unter additiver inversbildung abgeschlossen sein muss"$
  + $a_i in R E, exists r_1 in R, exists e in E, a_i = r dot e in (E) quad "folgt aus kriterium für ideale" $
  + $a_i in E R, exists r_1 in R, exists e in E, a_i = e dot r in (E) quad "folgt aus kriterium für ideale" $
  + $ quad  a_i in R E R, exists r_1, r_2 in R, exists in E, a_i = r dot e dot r in (E) quad "folgt aus kriterium für ideale (zweimal)" $
  #line()
  Da wir nun beide Richtungen der Inklusion gezeigt haben folgt: $(E) = M$
]
  In einem Ring mit 1 gilt:
  
  $ E union -E union R E union E R union R E R = R E R $ 
da 
  + $E = 1 dot E dot 1$
  + $-E = -1 dot E dot 1$
  + $ R E = R dot E dot 1$
  + $ E R = 1 dot E dot R$
  + $ R E R$ ist sowieso enthalten

In einem kommutativen Ring gilt:
$ E union -E union R E union E R union R E R = E union -E union R E $
+ $E$, $-E$ und $R E$ sind sowieso enthalten.
+ $E R = R E$
+ $R E R = R R E = R E$

=== c)
Sei $(R, + , dot)$ ein unitärer, kommutativer Ring.
#lemma[
  Folgende Aussagen sind equivalent:
  + $(R, +, dot)$ ist ein Körper
  + $(R, +, dot)$ hat genau die trivialen Ideale (die übereinstimmen)
]
#proof[
  "$=>$" $(R,+,dot)$ ist ein Körper.
  Ein Ideal $I$ muss die Bedingung $R I = I$ erfüllen. 
  $I$ kann nun entweder das Nullideal $I = {0}$ oder das Ideal des ganzen Körpers $I = R$ sein. 
  Zu zeigen: $ R I = I => I = {0} or I = R $
  Entweder gilt, $I \# < 1$, dann gilt $I = {0}$. \
  Sei im folgenden $\# I > 0$.  
  Zu zeigen $R I = R$. Dafür genügt es zu zeigen $R I supset.eq R$, also 
  $ r in R => exists r_1 in R, i in I, r_1 dot i = r $ 
  Sei $r_1 = i^(-1) dot r$ (Multiplikatives Invers existiert in dem Körper). \
  Es gilt $r_1 dot i = i^(-1) dot r dot i = r$. \
  #line()
  "$arrow.double.l$"\
  Wenn $(R, +, dot)$ nur die zwei trivialen Ideale hat, dann folgt 
  $ (r) = R or (r) = (0)  quad forall r in R " mit" r eq.not 0 $
  $(r) = (0)$ ist aber nicht möglich, da $r in.not (0) quad forall r in R "mit" r eq.not 0$.
  Es gilt also:

  $ (1) = (r) = R quad forall r in R $
  Zu zeigen ist: Für jedes $r in R$ existiert ein Multiplikatives Inverses $r^(-1)$ mit $r dot r^(-1) = r^(-1) dot r = 1 $. \
  Da $(1) = (r)$ gilt, wissen wir $exists r_1 in R, r_1 dot r = 1$, was für jedes $r$ ein Multiplikatives Invers erzeugt.

]
=== d)
#lemma[
  Es sei $X$ eine Menge mit  $Y subset.eq X$. 
  Der Faktorring $#pset (X) \/ pset (Y) $ von $(pset (X), Delta, inter)$ ist isomorph zu $(pset (X \\ Y), Delta, inter)$.
]
#proof[
   Sei $ f : pset (X) -> pset (X \\ Y) := x mapsto x \\ Y $
  Zu zeigen: 
  + $f$ ist RingHom: \
    $ f(a Delta b) = (a Delta b) \\ Y = (a \\ b inter b \\ a) \\ Y = (a \\ b) \\ Y inter (b \\ a) \\ Y  \
  = (a \\ Y) \\ b inter (b \\ Y) \\ a \
  = (a \\ Y) \\ (b \\ Y) inter (b \\ Y) \\ (a \\ Y) \
  =  a \\ Y Delta b \\ Y = f(a) Delta f(b) $

  $ f(a inter b) = (a inter b) \\ Y = a \\ Y inter b \\ Y = f(a) inter f(b)
  $

  $ f(X) = f(X \\ Y) quad "1 wird auf 1 abgebildet" $
    #line()
  + $ker(f) = pset (Y)$, da $x \\ Y = emptyset$ genau dann, wenn $x subset.eq Y$ (also $x in pset(Y)$)
    #line()
  + $im(f) = pset (X \\ Y)$, da $f(pset (X \\ Y)) = pset (X \\ Y)$, d.h. alle Elemente aus $pset (X \\ Y)$ werden mindestens einmal getroffen.
]

== e)
Seien $A, B in pset (X)$
+ $(A) = pset (A)$, da für ein Ideal gelten muss: $(A) inf x subset.eq (A) quad forall x in pset (X)$.
  $x$ kann hier insbesondere alle Teilmengen von $A$ annehmen. \
  Damit gilt $(A,B) = pset (A) union pset (B) = pset (A union B)$ und $(A, B) = (A union B)$
+ $(9,15)$. Wir wissen, dass $3 in (9,15)$, da $3 = 9 - (15 - 9) in (9,15)$ (folgt aus der Abgeschlossenheit unter Addition). 
  Alle weitere Zahlen, die wir durch Addition und Subtraktion von 9 und 15 erhalten können siind vielfache von 3. Es gilt also 
  $ (9,15) = {3k | k in ZZ} = (3) $




== Aufgabe 5

== Aufgabe 6

== Aufgabe 7
