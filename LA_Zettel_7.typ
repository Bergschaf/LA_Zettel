#import "Preamble.typ": *

= LA Zettel 7
Bearbeitet von Leon Krasniqi, Christian Krause, Silas Gaschler (Tutorium: Gregor Teupke (Mi 16:15))

== Aufgabe 1
(i)
$(ZZ_3,+_3,dot_2)$
Da $3$ eine Primzahl ist, ist nach script $(ZZ_3,+_3,dot_3)$ ein Körper.
==== Bestimme Charakteristik
$ underbrace((1+1), 2)+1 = 0 => "char"(ZZ_3,+_3,dot_3)= 3 $
==== Nullteilerfreiheit
$ZZ_3 = {0,1,2}$
$ 0*x = 0 forall x in ZZ_3 $
$ 1*2 = 2*1 = 2 $
$ 2*2 = 1 $
$ 1*1 = 1 $
$=> "Nullteilerfreiheit"$

=== (ii)

Bereits bewiesen
$ forall A,B in cal(P)(X): $
$(cal(P)(X),Delta) " ist abelsche Gruppe"$
$ A inter (B inter C)= (A inter B)inter C in cal(P)(X) $
$=> "Es handelt sich um einen Ring"$
Das Einselement ist $X$ da $A inter X = A$
Das Nullelement ist $emptyset$
==== Nullteilerfreiheit
Sei $A in cal(P)(X)$ und $emptyset != A$ dann existiert ($hash X > 1$) eine zu $A$ disjunkte Menge $B in cal(P)(X)$ mit $B!= emptyset$
$ => A inter B = emptyset $
$=>$ Falls $hash X > 1$ ist der Ring nicht Nullteilerfrei.

Falls $hash X = 1$ existiert maximal eine von $A$ disjunkte Teilmenge, und zwar  $emptyset$. Also ist der Ring für $hash X = 1$ Nullteilerfrei
==== Charakteristik



=== (iii)
Angenommen $(cal(P)(X),Delta,Delta)$ ist ein Ring, dann muss $forall A,B,C in X$ das Distributivgesetz gelten:
$ A Delta (B Delta C) = (A Delta B) Delta (A Delta C) $
Da $Delta$ assoziativ sein muss, und die inversen Elemente für die verknüpfung $Delta$ existieren müssen:
$ iff (A Delta B) Delta C = (A Delta B) Delta (A Delta C) $
$ iff (A Delta B) Delta C = (A Delta B) Delta (A Delta C) $
$ iff C = A Delta C iff A = emptyset $
Das ist ein Wiederspruch, also ist $(cal(P)(X),Delta,Delta)$ kein Ring
==== (iv)
Damit $(QQ^RR,+,compose)$ ein Ring ist, muss das Distributivgesetz gelten.
das heißt:
$ forall f_1,f_2,f_3 in QQ^RR; forall x_2,x_3 in RR: $
$ f_1 compose (f_2(x_2)+f_3(x_3)) = f_1 compose f_2(x_2)+f_1 compose f_3(x_3) $
Wähle $f_1 = f_2 = f_3 : RR in.rev x |-> 1 in QQ:$
$ f_(1)(f_(2)(x_(2))+f_(3)(x_(3)))!=f_(1)(f_(2)(x_(2)))+f_(1)(f_(3)(x_(3))) $
$ 1 != 1+1 $
Das ist ein Wiederspruch. Es handelt sich also um keinen Ring

== Aufgabe 2

=== b)
#proof[

  *$ (i)=> (i i): $*
  $ (i): forall a in R: a != 0_R => a dot b != 0_R $
  $ f: R in.rev a |-> a dot b in R $
  $ "Kern"(f) = {a|a dot b = 0_R} = {0_R} $
  $ I: R \/ {0_R}-> "Bild"(f) $
  $ a+"Kern"(f) = [a] |-> f(a) $
  Homomorphiesatz für Ringe
  $=>I$ ist ein Isomorphismus
  $ pi: R in.rev a-> [a] in R\/{0_R} $
  Da $ R \/{0_R} = {a+0_R = [a] a in R} = {a = [a]| a in R} $
  ist $pi$ injektiv.
  Es gilt außerden, das:
  $ f = I compose pi $
  Da $I,pi$ injektiv  $=> f$ injektiv

  *$ (i i) => (i i i) $*
  $ (i i): (forall a,c in R: f(a) = f(c)=> a = c) $
  $ <=> (forall a,c in R: a dot b = c dot b => a = c) $

  *$ (i i i)=> (i) $*
  $ (i i i):(forall a,b in R: a dot b = c dot b => a = c) $
  Es gilt außerdem $0_R dot b = 0_R$
  $ "Sei" a dot b = 0_R = 0_R dot b => a = 0_R $
  $=>$ b ist kein Rechtsnullteiler

  *$=> ((i)=> (i i)=> (i i i)=> (i)) => "Ringschluss"$*

]


== Aufgabe 3
=== b)
#lemma[

  Seien $(R_1,+_1,dot_1)$ und $(R_2,+_2,dot_2)$ Ringe mit den Nullelementen $0_(R_1)$ bzw. $0_(R_2)$ und $f: R_(1)-> R_(2)$ ein Homomorphismus, dann gilt die Äquivalenz foldender Aussagen:
  - (i): $f$ ist injektiv
  - (ii): $"Kern"(f) = {0_(R_1)}$
  - (iii): Die einzige Lösung der Gleichung $f(a) = 0_(R_2)$ ist $a = 0_(R_1)$
]
#proof[

  *(i)$=>$(ii)*
  $ (i): (forall a,b in R_1: f(a)= f(b) => a = b) $
  $ forall a_(n) in R_1: f(a_(n))= f(a_(n)+_1 0_(R_1)) = f(a_(n))+_2 f(0_(R_1)) $
  Da wir $+_2$ Kürzen dürfen
  $ iff 0_(R_2) = f(0_(R_1)) $
  $ => 0_(R_1) in "Kern"(f) $

  $=> forall b in R_1 "mit" f(b) = 0_(R_2) =>f(b)= f(0_(R_1)) => b = 0_(R_1)$
  $ => "Kern"(f) = {0_(R_(1))} $
  *(ii)$=>$(iii)*
  $ (i i): "Kern"(f) = {0_(R_1)}= {a in R_1| f(a) = 0_(R_2)} $
  $ => forall a in R_1 "mit" f(a)=0_(R_2) => a in "Kern"(f) => a = 0_(R_1) $
  *(iii)$=>$(i)*

  $ (i i i): f(a) = 0_R_2 => a = 0_R_1 $
  Sei $c,d in R_(1)$ und $f(c) = f(d)$
  $ => 0_R_2 = f(c)-f(d) $
  $ => f(c-d) = 0_R_2 $
  $ => c-d = 0_R_1 $
  $ => c = d $


  *$ => ((i)=>(i i)=>(i i i)=>(i))=>((i)iff(i i)iff(i i i)) $*
]
=== c)
#lemma[

  Es sei $(R,+,dot)$ ein Ring mit Eins und $"char"(R) = 0$, dann enthält $R$ einen Unterring, der isomorph zu $ZZ$ ist.

]
#proof[


  $ f: ZZ in.rev n -> cases(0_R "falls" n = 0, n 1 "falls" n >0, |n|(-1_R) "falls" n <0) in R $
  $ a in ZZ $

  $ a >0 : f(-a)= a(-1_R)= underbrace((-1_R-...-1_R), a "mal") = -underbrace((1+..+1), a "mal") = -(a 1_R) $
  In folgendem nutze wir : $-(a 1_R)hat(=)-a 1_R = underbrace((1+...+1), -a "mal")$


  $a,b in ZZ$


  $
    f(a)+f(b) = a 1_R + b 1_R = underbrace((1_R+...+1_R), a "mal")+underbrace((1_R+...+1_R), b "mal") = (a+b)1_R=f(a+b)
  $
  $
    f(a)dot f(b)= underbrace((1_R+...+1_R), a "mal")dot underbrace((1_R+...+1_R), b "mal") = underbrace((b 1+ ...+b 1), a "mal") = (a dot b )1_R =f(a dot b)
  $
  $ =>f "ist Homomorphismus" $
  Als nächstes zeigen wir, das $f$ injektiv ist:
  $ "Sei" f(a) = f(b) => a 1_R = b 1_R $
  $=>(a-b)1_R= 0_R=>a-b = "char"(R)=0=>a = b$

  Schränken wir R auf das Bild von $f$ ein, so bekommen wir den Isomorphismus:
  $ g: ZZ in.rev n -> cases(0_R "falls" n = 0, n 1 "falls" n >0, |n|(-1_R) "falls" n <0) in "Bild"(f) $

  Es bleibt zu zeigen, das das Bild von $f$ ein Unterring von $R$ ist:
  $ forall a,b in ZZ: $
  $"Es gilt: "a - b in ZZ$und $a dot b in ZZ$ und $0_R in "Bild"(f)=>"Bild"(f)!=emptyset$
  $ g(a)-g(b)=g(a)+g(-b) = g(underbrace(a-b, in ZZ)) in "Bild"(g)="Bild"(f) $
  $ g(a)dot g(b) = g(a dot b) in "Bild"(f) $
  $=>ZZ$ ist isomorph zum Bild($f$), welcher ein Unterring von $R$ ist.
]



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

== Aufgabe 5
a)
#lemma[
  Jeder Körper $(K,+,dot)$ ist Nullteilerfrei.
]
#proof[

  Angenommen es existiert ein Linksnullteiler $a!= 0_K$
  $ exists b!=0_K in K: $
  $ a b = 0_K $
  $ a b = a 0_K $
  $ iff a^(-1) dot a dot b = a^(-1) dot a dot 0_K $
  $ iff b = 0_K $
  Das ist ein Wiederspruch
  $=>$ Jeder Körper ist Nullteilerfrei

]
#lemma[
  Es sei $(K,+,dot)$ ein Körper und $a,b in K$.
  $ (a-x) dot (b-x) = 0_K => x = a or x = b $


]
#proof[

  Wir haben bereit gezeigt, das jeder Körper Nullteilerfrei ist. Daraus folgt:
  $ underbrace((a-x), in K) dot underbrace((b-x), in K) = 0_K => a-x = 0_K or b-x = 0_K $
  $ iff x = a or x = b $


]
== b)
Wir beweisen zunächst einige Hilfslemmas. Zur besseren lesbarkeit wird verwendt: $1_K hat(=) 1$
#lemma[
  Sei $(K,+, dot)$ ein Körper mit  $"char"(K)=0$, dann gilt
  $ forall a,b in NN: a 1 = b 1 => a = b $
]
#proof[

  Falls $ a >= b $
  $ a 1 = b 1 iff b 1 + (a-b)1 = b 1 => a-b = "char"(K) = 0 => a = b $
  Falls $ a <= b $
  $ b 1 = a 1 iff a 1 + (b-a)1 = a 1 => b-a = "char"(K) = 0 => a = b $

]
#lemma[
  Sei $(K,+, dot)$ ein Körper mit  $"char"(K)=0$, dann gilt:
  $ a 1 + b 1 = (a+b) 1 $
  $a 1 + b (-1) = (a-b) 1$
  $ a 1 dot b 1 = (a dot b) 1 $
  $ (a 1)^(-1)dot (b 1)^(-1) = ((a dot b)1)^(-1) $


]
#proof[

  $ a 1 + b 1 = underbrace((1+...+1), a "mal") +underbrace((1+...+1), b "mal") = (a+b)1 $
  $
    1 + b 1 = underbrace((1+...+1), a "mal") +underbrace((-1-...-1), b "mal") = underbrace((1+...+1), a-b "mal") +underbrace((0_K+...+0_K), b "mal") = (a-b)1
  $
  $ a 1 dot b 1 = underbrace((1+...+1), a "mal") dot b 1= underbrace((b 1 +...+ b 1), a "mal") = (a dot b)1 $
  $ (a 1)^(-1)dot (b 1)^(-1) dot a 1 dot b 1 = 1 iff (a 1)^(-1)dot (b 1)^(-1) dot (a dot b) 1 = 1 $
  $ => (a 1)^(-1)dot (b 1)^(-1) = ((a dot b) 1)^(-1) $

]


#lemma[

  Sei $(K,+,dot)$ ein Körper mit $"char"(K)=0$, dann enthält $K$ einen Unterkörper, der isomorph zu $QQ$ ist.

]
#proof[

  Wir verwenden aus dem script:

  Jeder Homomorphismus zwischen Körpern ist injektiv

  Wir definieren:
  $ f: QQ-> K $$
    a/b |-> cases(a 1 dot (b 1)^(-1) "falls " a >0, 0_K "falls" a = 0, |a|(-1) dot (b 1)^(-1) "falls " a <0)
  $

  Wir zeigen, das $f$ ein Homomorphismus ist
  Zur besseren Lesbarkeit schreiben wir $n 1 hat(=) n$ und $(n 1)^(-1)hat(=)n^(-1)$
  $ f(a/b)+f(c/d) = a dot b^(-1)+c dot d^(-1) $
  $
    =b^(-1)(a+c dot b dot d^(-1))=b^(-1) dot d^(-1) dot (a dot d +c dot b) =(b dot d)^(-1 ) dot (a dot d + c dot b) = f((a d +c b)/(b d)) = f(a/b+b/c)
  $
  $ f(a/b) dot f(c/d) = a dot b^(-1)dot c dot d^(-1) = (a dot b )dot (b dot d)^(-1 )= f(a/b dot c/d) $
  $ => f" ist ein Homomorphismus" $
  $=> f "ist injektiv"$
  Wir definieren
  $ g: QQ-> "Bild"(f) $$
    a/b |-> cases(a 1 dot (b 1)^(-1) "falls " a >0, 0_K "falls" a = 0, |a|(-1) dot (b 1)^(-1) "falls " a <0)
  $
  $ => "g ist ein Isomorphismus" $
  Es gilt außerdem, da $"Bild"(f) subset.eq K$, dass das $"Bild"(f)$ einen zu $QQ$ isomorphen Unterkörper in $K$ bildet


]
== c)
#lemma[

  Kein endlicher Körper kann geordnet werden

]
#proof[

  In einem geordneten Körper gilt:
  $ 0_K < 1_K $
  $ alpha <= beta => alpha + gamma<=beta+gamma $
  Angenommen es existiert ein endlicher geordneter Körper $(K,+,dot)$, dann
  $ exists m = max(K) $
  Es gilt $forall a in K$
  $ a+1_K <=m $
  Wähle $a = m$
  $ =>m+1_K <= m iff m+1_K <= m +0_K $
  $ => 1_K <= 0_K $
  Das Wiederspricht den Rechenregeln in einem Körper

]
