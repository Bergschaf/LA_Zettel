#import "Preamble.typ": *

= LA Zettel 3
Bearbeitet von Leon Krasniqi, Christian Krause, Silas Gaschler (Tutorium: Gregor Teupke(Mi 16:15))
== Aufgabe 1
- (i): $f$ ist injektiv
- (ii): $exists g: Y->X: g compose f = id_X$
- (iii) Für beliebige $X_0$ und beliebige $f_1,f_2: X_0 -> X$ gilt: Aus $f compose f_1=f compose f_2$ folgt $f_1=f_2$
#lemma[
  $ ("i")<=>("ii")<=>("iii") $
]
#proof[

  *$ ("i")=>("ii"): $*
  Definiere $g:Y->X$ wie folgt:
  $ g:={(y,x)in Y times X | f(x)= y} $
  $ => g compose f = {(x_1,x_2) in X times X|exists f(x) in Y: (x_1,f(x))in f and (f(x),x_2)in g} $
  mit

  $ ("i"): forall x_1,x_2in X:f(x_1)=f(x_2)=>x_1=x_2 $
  $ => g compose f = {(x,x) in X times X|exists f(x) in Y: (x,f(x))in f and (f(x),x)in g}=id_X $

  *(ii)$=>$(iii):*

  Es sein $X_0$ eine beliebige Menge und $f_1,f_2:X_0->X$ beliebige Abbildungen.

  $("ii"): exists g:Y->X: g compose f = id_X$ und $f compose f_1 = f compose f_2$
  $ =>g compose (f compose f_1) = g compose (f compose f_2) $
  $ <=> underbrace((g compose f), id_X)compose f_1=underbrace((g compose f), id_X)compose f_2 $
  $ => f_1 =f_2 $

  *$ ("iii")=>("i") $*
  $ ("iii"):f compose f_1 = f compose f_2 => f_1=f_2 $
  $ <=> forall x_0 in X_0: f(f_1(x_0))=f(f_2(x_0))=>f_1(x_0) = f_2(x_0) $
  Sei $x_1=f_1(x_0)$ und $x_2=f_2(x_0)$. Und da $f_1$ und $f_2$ frei wählbar sind, können sie auch surjektiv sein. Für surjektive $f_1,f_2$ folgt:
  $ forall x_1,x_2 in X: f(x_1)=f(x_2)=>x_1 =x_2 $
  *$ =>(("i")=>("ii")=>("iii")=>("i"))=>(("i")<=>("ii")<=>("iii")) $*

]
#emph(text(red)[Die obige Aufgabe sollte noch einmal auf klarheit überprüft werden])
