package lpeg

import (
	"fmt"
	"reflect"
	"strconv"
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
	p2 := anywhere2(P("world"))
	fmt.Println(Match(p2, "hello world"))
	p3 := anaywhere3(P("world"))
	fmt.Println(Match(p3, "hello world"))
	p4 := atwordboundary(P("world"))
	fmt.Println(Match(p4, "hello world"))
}

func TestParentheses(*testing.T) {
	var g Grammar
	g.AddRule("S",
		P("(").
			Seq(
				P(1).Sub(S("()")).
					Or(
						V("S"),
					).
					Pow(0),
			).
			Seq(P(")")))
	patt := P(g)
	fmt.Println(Match(patt, "(((sdf(sd)sd)(sd(sdf)sdf))as)df"))
}

func gsub(s string, p string, repl string) (int, interface{}) {
	patt := Cs(P(p).Sc(repl).Or(P(1)).Pow(0))
	return Match(patt, s)
}

func TestSubstitude(*testing.T) {
	fmt.Println(gsub("dabcd", "abc", "haha"))
}

func TestCommaSeparate(*testing.T) {
	p := P(1).Sub(P(`"`)).Or(P(`""`).Sc(`"`)).Pow(0)
	c := C(P(1).Sub(S(`,\n"`)).Pow(0))
	field := P(`"`).Seq(Cs(p).Seq(P(`"`))).Or(c)
	record := field.Seq(P(",").Seq(field).Pow(0)).Seq(P("\n").Or(P(-1)))
	fmt.Println(Match(record, "ab,\"cd\",ef,g"))
	fmt.Println(Match(record, "ab,\"cd,\"ef,g"))
	fmt.Println(Match(record, "ab,\"\"cd\"\",ef,g"))
}

func TestLongstring(*testing.T) {
	equals := P("=").Pow(0)
	open := P("[").Seq(Cgn(equals, "init")).Seq(P("[")).Seq(P("\n").Pow(-1))
	close := P("]").Seq(C(equals)).Seq(P("]"))
	closeeq := Cmt(close.Seq(Cb("init")), func(s string, i int, cap ...interface{}) (int, []interface{}) {
		a := cap[0].(string)
		b := cap[1].(string)
		if a == b {
			return i, nil
		}
		return -1, nil
	})
	_ = closeeq
	strp := open.Seq(C(P(1).Sub(closeeq).Pow(0))).Seq(close).Nc(1)
	//strp := open.Seq(C(P(1).Sub(close).Pow(0))).Seq(close).Nc(1)
	fmt.Println(Match(strp, "[==[abcd]==]"))
}

func eval(x interface{}) int {
	switch x := x.(type) {
	case string:
		i, err := strconv.Atoi(x)
		if err != nil {
			panic(err)
		}
		return i
	case CaptureTable:
		op1 := eval(x[1])
		for i := 2; i < len(x); i++ {
			op := x[i]
			op2 := eval(x[i+1])
			if op, ok := op.(string); !ok {
				panic(op)
			}
			switch op {
			case "+":
				op1 = op1 + op2
			case "-":
				op1 = op1 - op2
			case "*":
				op1 = op1 * op2
			case "/":
				op1 = op1 / op2
			}
		}
		return op1
	default:
		panic(reflect.TypeOf(x))
	}
}
func TestArithmetic(*testing.T) {
	space := S(" \n\t").Pow(0)
	number := C(P("-").Pow(-1).Seq(R("09").Pow(1))).Seq(space)
	termop := C(S("+-")).Seq(space)
	factorop := C(S("*/")).Seq(space)
	open := P("(").Seq(space)
	close := P(")").Seq(space)
	var g Grammar
	g.AddRule("Exp", Ct(V("Term").Seq(termop.Seq(V("Term")).Pow(0))))
	g.AddRule("Term", Ct(V("Factor").Seq(factorop.Seq(V("Factor")).Pow(0))))
	g.AddRule("Factor", number.Or(open.Seq(V("Exp")).Seq(close)))
	patt := space.Seq(P(g)).Seq(P(-1))
	i, cap := Match(patt, "2*(5+7)-3/2")
	fmt.Println(i, len(cap), eval(cap[0]))
}
