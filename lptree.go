package lpeg

import (
	"reflect"
	"unsafe"
)

const treeSize = int(unsafe.Sizeof(*(*tTree)(nil)))
const maxValue = 0xffff // key uint16

// types of trees
type tTag byte

const (
	tChar tTag = iota // 'n' = char
	tSet              // the set is stored in next CHARSETSIZE bytes
	tAny
	tTrue
	tFalse
	tRep      // 'sib1'*
	tSeq      // 'sib1' 'sib2'
	tChoice   // 'sib1' / 'sib2'
	tNot      // !'sib1'
	tAnd      // &'sib1'
	tCall     // ktable[key] is rule's key; 'sib2' is rule being called
	tOpenCall // ktable[key] is rule's key
	tRule
	tGrammar // 'sib1' is initial (and first) rule
	tBehind  // 'sib1' is Pattern,'n' is how mutch to go back
	tCapture
	tRunTime
)

// number of siblings for each tree
var numsiblings = []int{
	0, 0, 0, // char, set, any
	0, 0, // true, false
	1,    // rep
	2, 2, // seq, choice
	1, 1, // not, and
	0, 0, 2, 1, // call, opencall, rule, grammer
	1,    // behind
	1, 1, // capture, runtime capture
}

type tTree struct {
	tag tTag
	cap capKind
	key uint16
	psn int32 // ps or n,ps is the second child,n is the counter
}

func sib1(tree []tTree, cur int32) int32 {
	return cur + 1
}

func sib2(tree []tTree, cur int32) int32 {
	return cur + tree[cur].psn // ps
}

type ktable struct {
	tb []interface{}
}

func newtree(count int) *Pattern {
	patt := &Pattern{
		k: &ktable{tb: []interface{}{nil}},
	}
	if count == 1 {
		patt.tree = patt.cache[:]
	} else {
		patt.tree = make([]tTree, count)
	}
	return patt
}

func newleaf(tag tTag) *Pattern {
	patt := newtree(1)
	patt.tree[0].tag = tag
	return patt
}

func correctkeys(tree []tTree, cur int32, n uint16) {
	if n == 0 {
		return
	}
tailcall:
	switch tree[cur].tag {
	case tOpenCall, tCall, tRunTime, tRule:
		if tree[cur].key > 0 {
			tree[cur].key += n
		}
	case tCapture:
		if tree[cur].key > 0 && tree[cur].cap != cArg && tree[cur].cap != cNum {
			tree[cur].key += n
		}
	}
	switch numsiblings[tree[cur].tag] {
	case 1:
		cur = sib1(tree, cur)
		goto tailcall
	case 2:
		correctkeys(tree, sib1(tree, cur), n)
		cur = sib2(tree, cur)
		goto tailcall
	}
}

// ktable[0] is invalid
func concatktable(from, to *Pattern) {
	n1 := len(from.k.tb) - 1
	n2 := len(to.k.tb) - 1
	if n1+n2 > maxValue {
		panic("too many values in pattern")
	}
	to.k.tb = append(to.k.tb, from.k.tb[1:]...)
}

func joinktables(patt, a, b *Pattern, tree []tTree, t2 int32) {
	n1 := len(a.k.tb) - 1
	n2 := len(b.k.tb) - 1
	if n1 == 0 && n2 == 0 {
		return
	}
	if n2 == 0 || a.k == b.k {
		patt.k = a.k
		return
	}
	if n1 == 0 {
		patt.k = b.k
		return
	}
	concatktable(a, patt)
	concatktable(b, patt)
	correctkeys(tree, t2, uint16(n1))
}

func newroot2sib(a, b *Pattern, tag tTag) *Pattern {
	patt := newtree(1 + len(a.tree) + len(b.tree))
	patt.tree[0].tag = tag
	patt.tree[0].psn = 1 + int32(len(a.tree)) // ps
	copy(patt.tree[sib1(patt.tree, 0):], a.tree)
	copy(patt.tree[sib2(patt.tree, 0):], b.tree)
	joinktables(patt, a, b, patt.tree, sib2(patt.tree, 0))
	return patt
}

func newroot1sib(a *Pattern, tag tTag) *Pattern {
	patt := newtree(1 + len(a.tree))
	patt.tree[0].tag = tag
	copy(patt.tree[sib1(patt.tree, 0):], a.tree)
	patt.k = a.k
	return patt
}

func addtoktable(patt *Pattern, value interface{}) uint16 {
	if value == nil {
		return 0
	}
	if len(patt.k.tb)-1 >= maxValue {
		panic("too many values in pattern")
	}
	patt.k.tb = append(patt.k.tb, value)
	return uint16(len(patt.k.tb)) - 1
}

func mergektable(to, from *Pattern, tree []tTree, cur int32) {
	n := len(to.k.tb) - 1
	concatktable(from, to)
	correctkeys(tree, cur, uint16(n))
}

func newcharset() *Pattern {
	patt := newtree((charsetSize-1)/treeSize + 2)
	patt.tree[0].tag = tSet
	b := treebuffer(patt.tree, 0)
	for i := 0; i < charsetSize; i++ {
		b[i] = 0
	}
	return patt
}

// add to tree a sequence where first sibling is 'sib'
// return the second sibling
func seqaux(tree []tTree, cur int32, sib []tTree) int32 {
	tree[cur].tag = tSeq
	tree[cur].psn = int32(len(sib)) + 1 // ps
	copy(tree[sib1(tree, cur):], sib)
	return sib2(tree, cur)
}

func fillseq(tree []tTree, cur int32, tag tTag, n int, s string) {
	for i := 0; i < n-1; i++ {
		tree[cur].tag = tSeq
		tree[cur].psn = 2 // ps
		tree[sib1(tree, cur)].tag = tag
		if s != "" {
			tree[sib1(tree, cur)].psn = int32(s[i]) // n
		} else {
			tree[sib1(tree, cur)].psn = 0
		}
		cur = sib2(tree, cur)
	}
	tree[cur].tag = tag
	if s != "" {
		tree[cur].psn = int32(s[n-1])
	} else {
		tree[cur].psn = 0
	}
}

func numtree(n int) *Pattern {
	if n == 0 {
		return newleaf(tTrue)
	}
	var patt *Pattern
	var nd int32
	if n > 0 {
		patt = newtree(2*n - 1)
		nd = 0
	} else {
		n = -n
		patt = newtree(2 * n)
		patt.tree[0].tag = tNot
		nd = sib1(patt.tree, 0)
	}
	fillseq(patt.tree, nd, tAny, n, "")
	return patt
}

func getpatt(value interface{}) *Pattern {
	var patt *Pattern
	switch value := value.(type) {
	case string:
		slen := len(value)
		if slen == 0 {
			patt = newleaf(tTrue)
		} else {
			patt = newtree(2*(slen-1) + 1)
			fillseq(patt.tree, 0, tChar, slen, value)
		}
	case int:
		patt = numtree(value)
	case bool:
		if value {
			patt = newleaf(tTrue)
		} else {
			patt = newleaf(tFalse)
		}
	case Grammar:
		patt = newgrammar(value)
	case CaptureFunction, FoldFunction, RuntimeFunction:
		patt = newtree(2)
		patt.tree[0].tag = tRunTime
		patt.tree[0].key = addtoktable(patt, value)
		patt.tree[sib1(patt.tree, 0)].tag = tTrue
	case *Pattern:
		patt = value
	default:
		panic("getpatt:" + reflect.TypeOf(value).String())
	}
	return patt
}

type rule struct {
	name string
	patt *Pattern
}

func (g *Grammar) treeSize() int {
	size := 1
	for _, r := range g.r {
		size += 1 + len(r.patt.tree)
	}
	return size + 1
}

func newgrammar(g Grammar) *Pattern {
	size := g.treeSize()
	patt := newtree(size)
	patt.tree[0].tag = tGrammar
	patt.tree[0].psn = int32(len(g.r)) // n
	postable := buildgrammar(g, patt)
	finalfix(patt, patt.tree, 0, sib1(patt.tree, 0), postable)
	initialrulename(patt, g)
	verifygrammar(patt.tree)
	return patt
}

func buildgrammar(g Grammar, patt *Pattern) map[string]int32 {
	nd := sib1(patt.tree, 0)
	n := len(g.r)
	postable := make(map[string]int32, n)
	for i := 0; i < n; i++ {
		rn := g.r[i]
		rulesize := 1 + len(rn.patt.tree)
		patt.tree[nd].tag = tRule
		patt.tree[nd].key = 0               // will be fixed when rule is used
		patt.tree[nd].cap = capKind(i)      // rule number
		patt.tree[nd].psn = int32(rulesize) // ps
		copy(patt.tree[sib1(patt.tree, nd):], rn.patt.tree)
		mergektable(patt, rn.patt, patt.tree, sib1(patt.tree, nd))
		postable[rn.name] = nd
		nd = sib2(patt.tree, nd)
	}
	patt.tree[nd].tag = tTrue
	return postable
}

func finalfix(patt *Pattern, tree []tTree, g, t int32, postable map[string]int32) {
tailcall:
	switch tree[t].tag {
	case tGrammar: // subgrammars were already fixed
		return
	case tOpenCall:
		fixonecall(patt, tree, g, t, postable)
	case tSeq, tChoice:
		correctassociativity(tree, t)
	}
	switch numsiblings[tree[t].tag] {
	case 1:
		t = sib1(tree, t)
		goto tailcall
	case 2:
		finalfix(patt, tree, g, sib1(tree, t), postable)
		t = sib2(tree, t)
		goto tailcall
	}
}

func fixonecall(patt *Pattern, tree []tTree, g, t int32, postable map[string]int32) {
	ruleName := patt.k.tb[tree[t].key].(string)
	n, ok := postable[ruleName]
	if !ok {
		panic("rule undefined in given grammar")
	}
	tree[t].tag = tCall
	tree[t].psn = n - (t - g)
	if tree[sib2(tree, t)].tag != tRule {
		panic(sib2(tree, t))
	}
	tree[sib2(tree, t)].key = tree[t].key
}

func initialrulename(patt *Pattern, g Grammar) {
	if patt.tree[sib1(patt.tree, 0)].key == 0 { // initial rule is not referenced?
		ruleName := g.r[0].name
		patt.tree[sib1(patt.tree, 0)].key = addtoktable(patt, ruleName)
	}
}

func verifyerror(passed []uint16) bool {
	for i := len(passed) - 1; i >= 0; i-- {
		for j := i - 1; j >= 0; j-- {
			if passed[i] == passed[j] {
				panic("rule may be left recursive")
				return false
			}
		}
	}
	panic("too many left calls in grammar")
	return false
}

func verifyrule(tree []tTree, cur int32, passed []uint16, nb bool) bool {
tailcall:
	switch tree[cur].tag {
	case tChar, tSet, tAny, tFalse:
		return nb // cannot pass from here
	case tTrue, tBehind:
		return true
	case tNot, tAnd, tRep:
		// return verifyrule(tree,sib1(tree,cur), passed,true)
		cur = sib1(tree, cur)
		nb = true
		goto tailcall
	case tCapture, tRunTime:
		// return verifyrule(tree,sib1(tree,cur),passed,nb)
		cur = sib1(tree, cur)
		goto tailcall
	case tCall:
		// return verifyrule(tree,sib2(tree,cur),passed,nb)
		cur = sib2(tree, cur)
		goto tailcall
	case tSeq:
		if !verifyrule(tree, sib1(tree, cur), passed, false) {
			return nb
		}
		// return verifyrule(tree,sib2(tree,cur),passed,nb)
		cur = sib2(tree, cur)
		goto tailcall
	case tChoice:
		nb = verifyrule(tree, sib1(tree, cur), passed, nb)
		// return verifyrule(tree,sib2(tree,cur),passed,nb)
		cur = sib2(tree, cur)
		goto tailcall
	case tRule:
		if len(passed) >= maxRules {
			return verifyerror(passed)
		}
		passed = append(passed, tree[cur].key)
		// return verifyrule(tree,sib1(tree,cur),passed,nb)
		cur = sib1(tree, cur)
		goto tailcall
	case tGrammar:
		return nullable(tree, cur)
	default:
		panic(tree[cur])
	}
}

func verifygrammar(grammar []tTree) {
	var passed [maxRules]uint16
	var rule int32
	for rule = sib1(grammar, 0); grammar[rule].tag == tRule; rule = sib2(grammar, rule) {
		if grammar[rule].key == 0 {
			continue // unused rule
		}
		verifyrule(grammar, sib1(grammar, rule), passed[:0], false)
	}
	if grammar[rule].tag != tTrue {
		panic(grammar[rule])
	}
	for rule = sib1(grammar, 0); grammar[rule].tag == tRule; rule = sib2(grammar, rule) {
		if grammar[rule].key == 0 {
			continue //unused rule
		}
		if checkloops(grammar, sib1(grammar, rule)) {
			panic("empty loop in rule")
		}
	}
	if grammar[rule].tag != tTrue {
		panic(grammar[rule])
	}
}

func checkloops(tree []tTree, cur int32) bool {
tailcall:
	if tree[cur].tag == tRep && nullable(tree, (sib2(tree, cur))) {
		return true
	} else if tree[cur].tag == tGrammar {
		return false
	}
	switch numsiblings[tree[cur].tag] {
	case 1:
		cur = sib1(tree, cur)
		goto tailcall
	case 2:
		if checkloops(tree, sib1(tree, cur)) {
			return true
		}
		// return checkloops(tree,sib2(tree,cur))
		cur = sib2(tree, cur)
		goto tailcall
	default:
		return false
	}
}

// Transform left associative constructions into right
// associative ones, for sequence and choice; that is:
// (t11 + t12) + t2  =>  t11 + (t12 + t2)
// (t11 * t12) * t2  =>  t11 * (t12 * t2)
// (that is, Op (Op t11 t12) t2 => Op t11 (Op t12 t2))
func correctassociativity(tree []tTree, cur int32) {
	t1 := sib1(tree, cur)
	for tree[t1].tag == tree[cur].tag {
		n1size := tree[cur].psn - 1 // ps
		n11size := tree[t1].psn - 1
		n12size := n1size - n11size - 1
		copy(tree[sib1(tree, cur):], tree[sib1(tree, t1):sib1(tree, t1)+n11size])
		tree[cur].psn = n11size + 1
		tree[sib2(tree, cur)].tag = tree[cur].tag
		tree[sib2(tree, cur)].psn = n12size + 1
	}
}

func finalfixcompile(tree []tTree, cur int32) {
tailcall:
	switch tree[cur].tag {
	case tGrammar: // subgrammars were already fixed
		return
	case tSeq, tChoice:
		correctassociativity(tree, cur)
	}
	switch numsiblings[tree[cur].tag] {
	case 1:
		cur = sib1(tree, cur)
		goto tailcall
	case 2:
		finalfixcompile(tree, sib1(tree, cur))
		cur = sib2(tree, cur)
		goto tailcall
	}
}

func prepcompile(patt *Pattern) []instruction {
	finalfixcompile(patt.tree, 0)
	return compile(patt)
}

func captureaux(a *Pattern, cap capKind, value interface{}) *Pattern {
	patt := newroot1sib(a, tCapture)
	patt.tree[0].cap = cap
	patt.tree[0].key = addtoktable(patt, value)
	return patt
}

func captureauxzero(a *Pattern, cap capKind) *Pattern {
	patt := newroot1sib(a, tCapture)
	patt.tree[0].cap = cap
	patt.tree[0].key = 0
	return patt
}

func auxemptycap(tree []tTree, cur int32, cap capKind) {
	tree[cur].tag = tCapture
	tree[cur].cap = cap
	tree[sib1(tree, cur)].tag = tTrue
}

func newemptycapkey(cap capKind, value interface{}) *Pattern {
	patt := newtree(2)
	auxemptycap(patt.tree, 0, cap)
	patt.tree[0].key = addtoktable(patt, value)
	return patt
}

func newemptycap(cap capKind) *Pattern {
	patt := newtree(2)
	auxemptycap(patt.tree, 0, cap)
	return patt
}
