package lpeg

type TableCapture struct {
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
	patt.tree[0].key = uint16(addtoktable(patt, value))
	return patt
}

func Match(patt *Pattern, subject string) (int, []interface{}) {
	if patt.code == nil {
		patt.code = prepcompile(patt)
	}
	var cs capState
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
