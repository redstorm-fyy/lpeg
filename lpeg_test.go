package lpeg

import (
	"fmt"
	"reflect"
	"testing"
)

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

func TestPatt(*testing.T) {
	patt := R("az").Pow(1).Seq(P(-1))
	fmt.Println(Match(patt, "hello"))
	fmt.Println(Match(patt, "1 hello"))
}

func rawset(cap1 interface{}, cap2 ...interface{}) interface{} {
	tb := cap1.(CaptureTable)
	tb.Set(cap2[0], cap2[1])
	return tb
}

func TestNameValueList(*testing.T) {
	space := S(" \t").Pow(0)
	alpha := R("az", "AZ")
	name := C(alpha.Pow(1)).Seq(space)
	sep := S(",;").Seq(space)
	pair := Cg(name.Seq(P("=").Seq(space).Seq(name))).Seq(sep.Pow(-1))
	list := Cf(Ct(P("")).Seq(pair.Pow(0)), rawset)
	fmt.Println(Match(list, "a=b, c = hi; next = pi"))
}

func split(s string, sep string) (int, interface{}) {
	sepp := P(sep)
	elem := C(P(1).Sub(sepp).Pow(0))
	p := elem.Seq(sepp.Seq(elem).Pow(0))
	return Match(p, s)
}

func split2(s string, sep string) (int, interface{}) {
	sepp := P(sep)
	elem := C(P(1).Sub(sepp).Pow(0))
	p := Ct(elem.Seq(sepp.Seq(elem).Pow(0)))
	return Match(p, s)
}
func TestSplit(*testing.T) {
	n, c := split("abce;,erds;1334;,", ";,")
	fmt.Println(n, c, len(c.([]interface{})))
	fmt.Println(split2("abce;,erds;1334;,", ";,"))
	a := c.([]interface{})[2]
	fmt.Println(reflect.TypeOf(a))
}

func anywhere2(p *Pattern) *Pattern {
	i := Cp()
	var g Grammar
	g.AddRule("S", P(i.Seq(p).Seq(i).Or(P(1).Seq(V("S")))))
	return P(g)
}

func anaywhere3(p *Pattern) *Pattern {
	i := Cp()
	return P(1).Sub(p).Pow(0).Seq(i).Seq(p).Seq(i)
}

func atwordboundary(p *Pattern) *Pattern {
	alpha := R("az", "AZ")
	var g Grammar
	g.AddRule("S", p.Or(
		alpha.Pow(0).
			Seq(
				P(1).Sub(alpha).Pow(1),
			).
			Seq(
				C(V("S")),
			),
	))
	return P(g)
}

func TestAnywhere2(*testing.T) {
	//p2 := anywhere2(P("world"))
	//fmt.Println(Match(p2, "hello world"))
	//p3 := anaywhere3(P("world"))
	//fmt.Println(Match(p3, "hello world"))
	p4 := atwordboundary(P("world"))
	fmt.Println(Match(p4, "hello world"))
}
