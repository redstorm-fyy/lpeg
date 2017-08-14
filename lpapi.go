package lpeg

type CaptureTable struct {
	seq []interface{}
	dic map[interface{}]interface{}
}
type FoldFunction func(cap1 interface{}, cap2 ...interface{}) interface{}
type CaptureFunction func(cap ...interface{}) []interface{}
type RuntimeFunction func(subject string, position int, cap ...interface{}) (newpos int, newcap []interface{})

type Pattern struct {
	code  []instruction
	tree  []tTree
	k     *ktable
	cache [1]tTree
}

type Grammar struct {
	r []rule
}

func (g *Grammar) AddRule(name string, patt *Pattern) {
	g.r = append(g.r, rule{name: name, patt: patt})
}

// -------------------- the method

// Seq :Sequence
func (a *Pattern) Seq(b *Pattern) *Pattern {
	if a.tree[0].tag == tFalse || b.tree[0].tag == tTrue {
		return a
	}
	if a.tree[0].tag == tTrue {
		return b
	}
	return newroot2sib(a, b, tSeq)
}

// Or :Choice
func (a *Pattern) Or(b *Pattern) *Pattern {
	var st1, st2 charset
	if tocharset(a.tree, 0, &st1) && tocharset(b.tree, 0, &st2) {
		patt := newcharset()
		b := treebuffer(patt.tree, 0)
		for i := 0; i < charsetSize; i++ {
			b[i] = st1.cs[i] | st2.cs[i]
		}
		return patt
	}
	if nofail(a.tree, 0) || b.tree[0].tag == tFalse {
		return a
	}
	if a.tree[0].tag == tFalse {
		return b
	}
	return newroot2sib(a, b, tChoice)
}

// Pow :a^n
func (a *Pattern) Pow(n int) *Pattern {
	var patt *Pattern
	if n >= 0 { // seq a (seq a ... (seq a (rep a)))
		patt = newtree((n + 1) * (len(a.tree) + 1))
		if nullable(a.tree, 0) {
			panic("loop body may accept empty string")
		}
		var tree int32
		for i := 0; i < n; i++ {
			tree = seqaux(patt.tree, tree, a.tree)
		}
		patt.tree[tree].tag = tRep
		copy(patt.tree[sib1(patt.tree, tree):], a.tree)
	} else { // choice (seq a ... choice a true ...) true
		n = -n
		alen := len(a.tree)
		// size = (choice + seq + a + true) * n, but the last has no seq
		patt = newtree(n*(alen+3) - 1)
		var tree int32
		for ; n > 1; n-- {
			patt.tree[tree].tag = tChoice
			patt.tree[tree].psn = int32(n*(alen+3) - 2) // ps
			patt.tree[sib2(patt.tree, tree)].tag = tTrue
			tree = sib1(patt.tree, tree)
			tree = seqaux(patt.tree, tree, a.tree)
		}
		patt.tree[tree].tag = tChoice
		patt.tree[tree].psn = int32(alen) + 1 // ps
		patt.tree[sib2(patt.tree, tree)].tag = tTrue
		copy(patt.tree[sib1(patt.tree, tree):], a.tree)
	}
	patt.k = a.k
	return patt
}

// And :&p
func (a *Pattern) And() *Pattern {
	return newroot1sib(a, tAnd)
}

// Not :!p
func (a *Pattern) Not() *Pattern {
	return newroot1sib(a, tNot)
}

// Sub :a - b == Seq (Not t2) t1
func (a *Pattern) Sub(b *Pattern) *Pattern {
	var st1, st2 charset
	if tocharset(a.tree, 0, &st1) && tocharset(b.tree, 0, &st2) {
		patt := newcharset()
		b := treebuffer(patt.tree, 0)
		for i := 0; i < charsetSize; i++ {
			b[i] = st1.cs[i] &^ st2.cs[i]
		}
		return patt
	}
	patt := newtree(2 + len(a.tree) + len(b.tree))
	patt.tree[0].tag = tSeq
	patt.tree[0].psn = 2 + int32(len(b.tree)) // ps
	patt.tree[sib1(patt.tree, 0)].tag = tNot
	copy(patt.tree[sib1(patt.tree, sib1(patt.tree, 0)):], b.tree)
	copy(patt.tree[sib2(patt.tree, 0):], a.tree)
	joinktables(patt, a, b, patt.tree, sib1(patt.tree, 0))
	return patt
}

// Sc :string capture
func (a *Pattern) Sc(s string) *Pattern {
	return captureaux(a, cString, s)
}

// Nc :number capture
func (a *Pattern) Nc(n int) *Pattern {
	if n >= 0xffff {
		panic("invalid number")
	}
	patt := newroot1sib(a, tCapture)
	patt.tree[0].cap = cNum
	patt.tree[0].key = uint16(n)
	return patt
}

// Qc :query capture
func (a *Pattern) Qc(tb CaptureTable) *Pattern {
	return captureaux(a, cQuery, tb)
}

// Fc :function capture
func (a *Pattern) Fc(fn CaptureFunction) *Pattern {
	return captureaux(a, cFunction, fn)
}

// -------------------- the api

// P :Pattern
func P(value interface{}) *Pattern {
	return getpatt(value)
}

// S :Set
func S(value string) *Pattern {
	patt := newcharset()
	b := treebuffer(patt.tree, 0)
	for _, c := range value {
		setchar(b, byte(c))
	}
	return patt
}

// R :Range
func R(value ...string) *Pattern {
	patt := newcharset()
	b := treebuffer(patt.tree, 0)
	for _, r := range value {
		if len(r) != 2 {
			panic("range must have two characters")
		}
		for c := r[0]; c <= r[1]; c++ {
			setchar(b, byte(c))
		}
	}
	return patt
}

func V(value string) *Pattern {
	patt := newleaf(tOpenCall)
	patt.tree[0].key = addtoktable(patt, value)
	return patt
}

func B(patt *Pattern) *Pattern {
	n := fixedlen(patt.tree, 0)
	if n < 0 {
		panic("pattern may not have fixed length")
	}
	if hascaptures(patt.tree, 0) {
		panic("pattern have captures")
	}
	if n > maxBehind {
		panic("pattern too long to look behind")
	}
	newp := newroot1sib(patt, tBehind)
	newp.tree[0].psn = n
	return newp
}

func C(patt *Pattern) *Pattern {
	return captureauxzero(patt, cSimple)
}

func Cs(patt *Pattern) *Pattern {
	return captureauxzero(patt, cSubst)
}

func Ct(patt *Pattern) *Pattern {
	return captureauxzero(patt, cTable)
}

func Cf(patt *Pattern, fn FoldFunction) *Pattern {
	return captureaux(patt, cFold, fn)
}

// Cg : group capture
func Cg(patt *Pattern) *Pattern {
	return captureauxzero(patt, cGroup)
}

// Cgn : named group capture
func Cgn(patt *Pattern, name interface{}) *Pattern {
	return captureaux(patt, cGroup, name)
}

func Cc(value ...interface{}) *Pattern {
	n := len(value)
	if n == 0 {
		return newleaf(tTrue)
	}
	if n == 1 {
		return newemptycapkey(cConst, value[0])
	}
	patt := newtree(1 + 3*(n-1) + 2)
	patt.tree[0].tag = tCapture
	patt.tree[0].cap = cGroup
	patt.tree[0].key = 0
	cur := sib1(patt.tree, 0)
	for i := 0; i < n-1; i++ {
		patt.tree[cur].tag = tSeq
		patt.tree[cur].psn = 3 // ps
		s1 := sib1(patt.tree, cur)
		auxemptycap(patt.tree, s1, cConst)
		patt.tree[s1].key = addtoktable(patt, value[i])
		cur = sib2(patt.tree, cur)
	}
	auxemptycap(patt.tree, cur, cConst)
	patt.tree[cur].key = addtoktable(patt, value[n-1])
	return patt
}

func Cmt(patt *Pattern, fn RuntimeFunction) *Pattern {
	newp := newroot1sib(patt, tRunTime)
	newp.tree[0].key = addtoktable(patt, fn)
	return newp
}

func Cb(name interface{}) *Pattern {
	return newemptycapkey(cBackref, name)
}

func Carg(n int) *Pattern { // arg start from 1
	if n <= 0 || n > 0xffff {
		panic("invalid argument index")
	}
	patt := newemptycap(cArg)
	patt.tree[0].key = uint16(n)
	return patt
}

func Cp() *Pattern {
	return newemptycap(cPosition)
}

func Match(patt *Pattern, subject string, args ...interface{}) (int, []interface{}) {
	if patt.code == nil {
		patt.code = prepcompile(patt)
	}
	var cs capState
	cs.args = args
	cs.s = subject
	cs.k = patt.k
	cs.cap = 0
	r, cap := match(subject, 0, patt.code, &cs)
	if r == -1 {
		return -1, nil
	}
	cs.ocap = cap
	cs.cap = 0
	return r + 1, getcaptures(&cs) // start from 1
}
