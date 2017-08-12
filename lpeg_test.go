package lpeg

import (
	"fmt"
	"testing"
)

func TestPatt(*testing.T) {
	patt := R("az").Pow(1).Seq(P(-1))
	fmt.Println(Match(patt, "hello"))
	fmt.Println(Match(patt, "1 hello"))
}

func anywhere(p *Pattern) *Pattern {
	g := Grammar{}
	g.AddRule("S", p.Or(P(1).Seq(V("S"))))
	return P(g)
}

func TestAnywhere(*testing.T) {
	patt := P("ll")
	patt = anywhere(patt)
	//fmt.Println(patt)
	fmt.Println(Match(patt, "hello"))
}

func TestGrammar(*testing.T) {
	g := Grammar{}
	g.AddRule("S", P("a").Seq(V("B")).Or(P("b").Seq(V("A"))).Or(P("")))
	g.AddRule("A", P("a").Seq(V("S")).Or(P("b").Seq(V("A")).Seq(V("A"))))
	g.AddRule("B", P("b").Seq(V("S")).Or(P("a").Seq(V("B")).Seq(V("B"))))
	equalcount := P(g)
	fmt.Println(Match(equalcount, "aabbhello"))
}
