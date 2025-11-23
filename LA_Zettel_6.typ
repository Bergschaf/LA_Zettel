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
== Aufgabe 2
*(a)*

(i)

Das neutrale Element der Addition ist $0$
$ forall x in RR : f(x) = ln(x)= 0 iff x = e^0=1 $
$ => "Kern"(f) = {1} $
Da $f$ surjektiv ist gilt:
$ "Bild"(f) = RR $
(ii)

Das neutrale element der Addition ist $0$
$ forall x in QQ: f(x)=3x +1 = 0 iff x = -1/3 $
$ => "Kern"(f)= {-1/3} $
$ "Bild"(f)= {y in RR|y = f(x) = 3x +1 and x in QQ} = {y | (y-1)/3 in QQ} $
(iii)

Das neutrale Element von $({top,bot},"XOR")$ ist $bot$
$ forall x in ZZ_2:(x > 0)iff bot "falls " x <=0 <=> x = 0 $
$ => "Kern"(f)= {0} $
$ f(0)= bot;f(1)=top => "f ist surjektiv"=>"Bild"(f)={top,bot} $
(iv)
Das neutrale Element von $cal(P(RR,Delta))$ ist $emptyset$(Auf vorherigen Zetteln gezeigt)

ges:
$ f(sigma) = emptyset $
$ iff [0,-"sgn"(sigma)]= emptyset $
$ <=> "sgn"(sigma)=1 $
$ => "Kern"(f) = {sigma in S_3|"sgn"(sigma)=1} = A_(3) $
$"sgn"(sigma)$ ist entweder $1$ oder $-1$
$ =>"Bild"(f)= {emptyset,[0,1]} $
b)

$
  "Kern"(g compose f)= {a in G_(1)|g(f(a)) = e_(3)}={a in G_(1)|f(a) = b in G_(2) and g(b)=e_(3)}= f^(-1)("Kern"(g)) inter "Bild"(f))
$
$ "Bild"(g compose f)={g(a)|exists x in G_(1):a = f(x)} = g("Bild"(f)) $
= Aufgabe 6.3
a)
$ ZZ\/RR = {[a] = a + ZZ| a in RR} $
$ [a]tilde(+)[c] = [a + c] $
$ =>"neutrales Element" e = [0] $
Gesucht ist $b in RR$, sodass:
$ n[b] = [0]; n in NN $
$ iff b+...+b =n b= 0 ;n in NN $
$ => b = 0 $
$=>$ Das einzige Element mit endlicher Ordnung in $RR\/ZZ$ ist [0].

b)
#lemma[

  Sei $(G star)$ eine Gruppe und $E subset.eq G$ mit $chevron.l E chevron.r=G$ und $(N,star)$ untergruppe von $G$.

  Dann gilt: $N$ ist genau dann normalteiler von $(G,star)$, wenn $a star N = N star a$ für alle $a in E$ gilt.


]
#proof[

  $ forall a_(n)in E: N = a'_(n)star N star a_(n) (iff a_(n) star N = N star a_(n)) $
  Da $E$ ein Erzeugendensystem von $G$ ist, gilt auch:
  $ forall b in G: b = a_(1)star ...star a_(n) $
  $ b' = a'_(n)star...star a'_(1) $
  $
    => b' star N star b =underbrace(a'_(n)star underbrace(...star underbrace(a'_(1) star N star a_(1), N) star ..., N) star a_(n), N) = N
  $



]

c)

geg:
$ (G,star)" ist eine Gruppe" $
$ (N_(1),star),(N_(2),star) "sind Untergruppen von "G $
$ N_(1) subset.eq N_(2) $

#lemma[

  $ (G \/N_(2),tilde(star))" ist Untergruppe von " (G \/N_(1),tilde(star)) $

]
#proof[

  Da $N_(1) subset.eq N_(2)$ gilt:
  $ N_(1)=N_(2)or exists n in N_(2) : n in.not N_(1) $
  Falls $N_(1)=N_(2)$ dann ist auch $(G \/N_(2),tilde(star)) = (G \/N_(1),tilde(star))$

  Falls $exists n in N_(2) : n in.not N_(1)$ gilt:
  $ forall a in G: a star n in a star N_(2) and a star n in.not a star N_(1) $
  $ => a star N_(2) != a star N_(1) $
  $ => (G \/N_(2),tilde(star))" ist nicht Untergruppe von " (G \/N_(1),tilde(star)) $

]
d)
$
  \( G \, star.op \) upright(" Gruppe") \, #h(2em) \( N \, star.op \) upright(" Normalteiler") \, #h(2em) a star.op N = N star.op a
$

#lemma[
  $G \/ N$ ist abelsch, wenn $K \( G \) subset.eq N$.


]
Es gilt für alle $a in G$: $ a star.op N = N star.op a . $

$
  G \/ N = { thin a star.op N divides a in G thin } \, #h(2em) \[ a \] thin hat(star.op) thin \[ b \] = \[ a star.op b \] = \( a star.op b \) star.op N .
$
#proof[

  Zu zeigen:
  $
    \[ a \] thin tilde(star.op) thin \[ b \] = \[ b \] thin tilde(star.op) thin \[ a \] quad arrow.l.r.double quad K \( G \) subset.eq N .
  $

  $ \[ a \] thin tilde(star.op) thin \[ b \] = \[ b \] thin tilde(star.op) thin \[ a \] $

  $ arrow.l.r.double quad \[ a star.op b \] = \[ b star.op a \] $

  $ arrow.l.r.double quad \( a star.op b \) star.op N = \( b star.op a \) star.op N $

  $ arrow.l.r.double quad N star.op \( a star.op b \) = N star.op \( b star.op a \) . $

  $
    arrow.l.r.double { thin c star.op a star.op b divides c in N thin } = { thin d star.op b star.op a divides d in N thin }
  $

  $ arrow.l.r.double forall c in N #h(0em) exists d in N : #h(0em) c star.op a star.op b = d star.op b star.op a $

  $
    arrow.l.r.double forall c in N #h(0em) exists d in N : #h(0em) c star.op a star.op b star.op \( b star.op a \)' = d .
  $

  Da $c' in N$:
  $
    arrow.l.r.double forall c in N #h(0em) exists d in N : #h(0em) a star.op b star.op a' star.op b' = underbrace(c' star.op d, in N) .
  $

  $ arrow.l.r.double quad a star.op b star.op a' star.op b' in N quad arrow.l.r.double quad K \( G \) subset.eq N . $
]



== Aufgabe 4

Es seien $(G_1, star)$ und $(G_2, square)$ zwei Gruppen. ($G_1$ ist endlich).

#lemma([
  Ist auch $G_2$ endlich und $\# G_1$ und $\# G_2$ sind teilerfremd, dann existiert zwischen $G_1$ und $G_2$ nur der triviale Gruppenhomomorphismus.
])
#proof[
  Sei $f: G_1 -> G_2$ ein Gruppenhomomorphismus von $G_1$ nach $G_2$.
  Da $G_1$ endlich ist, gilt $\# G_1 \/ ker(f) divides \# G_1$.
  Dann gilt nach dem Homomorphiesatz:
  $ G_1 \/ ker(f) tilde.equiv im(f) => \# (G_1 \/ ker(f)) = \# im(f) $
  In die vorherige Gleichung eingesetzt ergibt das $\# im(f) \/ \# G_1$. \
  Da $f$ ein Gruppenhomomorphismus ist, ist $im(f)$ eine Untergruppe von $G_2$.Nach dem Satz von Lagrange gilt also $\# im(f) divides \# g_2$. \
  Da wir angenommen haben, dass $\# G_1$ und $\# G_2$ teilerfremd sind, muss gelten $\# im(f) = 1$. D.h. $f$ kann nur der triviale Gruppenhomomorphismus $f: x mapsto e_2$ sein.
]

#lemma[
  Ist $\# G_1$ eine Primzahl, dann ist jeder Gruppenhomomorphismus von $(G_1, star)$ nach $(G_2, square)$ trivial oder injektiv.
]
#proof[
  Sei $f: G_1 -> G_2$ ein Gruppenhomomorphismus von $G_1$ nach $G_2$.
  Da $G_1$ endlich ist, gilt $\# (G_1 \/ ker(f)) divides \# G_1$.
  Da $\# G_1$ eine Primzahl ist, ist $\# (G_1 \/ ker(f))$ entweder 1 oder $\# G_1$. \
  Wenn $\# (G_1 \/ ker(f)) = 1$, dann ist $f$ der triviale Gruppenhomomorphismus.\
  Zu zeigen: Wenn $\# (G_1 \/ ker(f)) = \# G_1$, dann ist f injektiv:\

  Im Beweis oben haben wir bereits aus dem Homomorphiesatz hergeleitet, dass $\#(G_1 \/ ker(f)) = \# im(f)$. Wir haben also $\# im(f) = \# G_1$. \
  Wir wissen, dass auf endlichen Mengen gleicher Mächtigkeit Surjektivität und Injektivität equivalent sind. Da $f|_(im(f)) : G_1 -> im(f)$ surjektiv ist, und $\# G_1 = \# im(f)$ wissen wir, dass $f|_(im(f))$ injektiv ist.
  Da wir $f_(im(f))$ nur auf das eigene Bild beschränkt haben, folgt, dass $f$ injektiv ist.
]
