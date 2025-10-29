

#import "@preview/ctheorems:1.1.3": *
#show: thmrules.with(qed-symbol: $square$)

#set page(width: 16cm, height: auto, margin: 1.5cm)
#set heading(numbering: "1.1.")

#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
#let lemma = thmbox("theorem", "Lemma", fill: rgb("#eeffff"))

#let corollary = thmplain(
  "corollary",
  "Corollary",
  base: "theorem",
  titlefmt: strong
)
#let definition = thmbox("definition", "Definition", fill:rgb("#aaeeee"))

#let example = thmplain("example", "Example").with(numbering: none)
#let proof = thmproof("proof", "Proof")

#let wichtig = thmbox("wichtig", "Wichtig", fill:rgb("#ffffaa")).with(numbering: none)
// Second derivateive
#let ddot(x) = $accent(x, dot.double)$
// Vector Arrow
#let ar(var) = $arrow(var)$ 
#let pset = $cal(P)$
#let iff = $<=>$
