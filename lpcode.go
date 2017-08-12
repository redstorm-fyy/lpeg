package lpeg

import (
	"reflect"
	"unsafe"
)

const bitsperchar = 8
const noinst int32 = -1
const maxBehind int32 = 0xff
const maxOff = 0xf
const maxAux = 0xff
const maxRules = 0xff

var fullset = &charset{[charsetSize]byte{
	0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
	0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
	0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
	0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
}}

type charset struct {
	cs [charsetSize]byte
}

func setchar(cs []byte, b byte) {
	(cs)[(b)>>3] |= (1 << ((b) & 7))
}

type compileState struct {
	p     *Pattern
	ncode int32 // next position in p.code to be filled
}

func realloccode(p *Pattern, nsize int) {
	if cap(p.code) >= nsize {
		p.code = p.code[:nsize]
		return
	}
	ncode := make([]instruction, nsize)
	copy(ncode, p.code)
	p.code = ncode
}

func getinstr(cs *compileState, i int32) *codeInst {
	return toinst(&cs.p.code[i])
}

func nextinstruction(compst *compileState) int32 {
	size := len(compst.p.code)
	if compst.ncode >= int32(size) {
		realloccode(compst.p, size*2)
	}
	ncode := compst.ncode
	compst.ncode++
	return ncode
}

func addinstruction(compst *compileState, op opCode, aux int32) int32 {
	i := nextinstruction(compst)
	getinstr(compst, i).code = op
	getinstr(compst, i).aux = byte(aux)
	return i
}

func treebuffer(tree []tTree, cur int32) []byte {
	b := reflect.SliceHeader{
		Data: uintptr(unsafe.Pointer(&tree[cur+1])),
		Len:  charsetSize,
		Cap:  charsetSize,
	}
	return *(*[]byte)(unsafe.Pointer(&b))
}

// Check whether a charset is empty (returns IFail), singleton (IChar),
// full (IAny), or none of those (ISet). When singleton, '*c' returns
// which character it is. (When generic set, the set was the input,
// so there is no need to return it.)
func charsettype(cs []byte) (op opCode, c int32) {
	count := int32(0)
	candidate := int32(-1)
	for i := int32(0); i < charsetSize; i++ { // for each byte
		b := cs[i]
		if b == 0 { // is byte empty?
			if count > 1 { // was set neither empty nor singleton?
				op = iSet // neither full nor empty nor singleton
				return
			}
			// else set is still empty or singleton
		} else if b == 0xFF { // is byte full?
			if count < (i * bitsperchar) { // was set not full?
				op = iSet // neither full nor empty nor singleton
				return
			} else {
				count += bitsperchar // set is still full
			}
		} else if (b & (b - 1)) == 0 { // has byte only one bit?
			if count > 0 { // was set not empty?
				op = iSet // neither full nor empty nor singleton
				return
			} else { // set has only one char till now; track it
				count++
				candidate = i
			}
		} else {
			op = iSet // byte is neither empty, full, nor singleton
			return
		}
	}
	switch count {
	case 0:
		op = iFail // empty set
		return
	case 1:
		//singleton; find character bit inside byte
		b := cs[candidate]
		c = candidate * bitsperchar
		if (b & 0xF0) != 0 {
			c += 4
			b >>= 4
		}
		if (b & 0x0C) != 0 {
			c += 2
			b >>= 2
		}
		if (b & 0x02) != 0 {
			c += 1
		}
		op = iChar
		return
	default:
		if count != charsetSize*bitsperchar { // full set
			panic(count)
		}
		op = iAny
		return
	}
}

type peState int

const (
	peNullable peState = iota
	peNofail
)

func checkaux(tree []tTree, cur int32, pred peState) bool {
tailcall:
	switch tree[cur].tag {
	case tChar, tSet, tAny, tFalse, tOpenCall:
		return false // not nullable
	case tRep, tTrue:
		return true // nofail
	case tNot, tBehind:
		if pred == peNofail {
			return false
		} else {
			return true
		}
	case tAnd:
		if pred == peNullable {
			return true
		} // else return checkaux(tree,sib1(tree,cur),pred)
		cur = sib1(tree, cur)
		goto tailcall
	case tRunTime:
		if pred == peNofail {
			return false
		}
		cur = sib1(tree, cur)
		goto tailcall
	case tSeq:
		if !checkaux(tree, sib1(tree, cur), pred) {
			return false
		}
		cur = sib2(tree, cur)
		goto tailcall
	case tChoice:
		if checkaux(tree, sib2(tree, cur), pred) {
			return true
		}
		cur = sib1(tree, cur)
		goto tailcall
	case tCapture, tGrammar, tRule:
		cur = sib1(tree, cur)
		goto tailcall
	case tCall:
		cur = sib2(tree, cur)
		goto tailcall
	default:
		panic(tree[cur].tag)
	}
}

func nofail(tree []tTree, cur int32) bool {
	return checkaux(tree, cur, peNofail)
}

func nullable(tree []tTree, cur int32) bool {
	return checkaux(tree, cur, peNullable)
}

func headfail(tree []tTree, cur int32) bool {
tailcall:
	switch tree[cur].tag {
	case tChar, tSet, tAny, tFalse:
		return true
	case tTrue, tRep, tRunTime, tNot, tBehind:
		return false
	case tCapture, tGrammar, tRule, tAnd:
		cur = sib1(tree, cur)
		goto tailcall
	case tCall:
		cur = sib2(tree, cur)
		goto tailcall
	case tSeq:
		if !nofail(tree, sib2(tree, cur)) {
			return false
		}
		cur = sib1(tree, cur)
		goto tailcall
	case tChoice:
		if !headfail(tree, sib1(tree, cur)) {
			return false
		}
		cur = sib2(tree, cur)
		goto tailcall
	default:
		panic(tree[cur].tag)
	}
}

func callrecursive(tree []tTree, cur int32, fn func([]tTree, int32) int32, def int32) int32 {
	key := tree[cur].key
	if key == 0 {
		return def
	}
	tree[cur].key = 0
	result := fn(tree, sib2(tree, cur))
	tree[cur].key = key
	return result
}

func callrecursivebool(tree []tTree, cur int32, fn func([]tTree, int32) bool, def bool) bool {
	key := tree[cur].key
	if key == 0 {
		return def
	}
	tree[cur].key = 0
	result := fn(tree, sib2(tree, cur))
	tree[cur].key = key
	return result
}

func fixedlen(tree []tTree, cur int32) int32 {
	len := int32(0)
tailcall:
	switch tree[cur].tag {
	case tChar, tSet, tAny:
		return len + 1
	case tFalse, tTrue, tNot, tAnd, tBehind:
		return len
	case tRep, tRunTime, tOpenCall:
		return -1
	case tCapture, tRule, tGrammar:
		cur = sib1(tree, cur)
		goto tailcall
	case tCall:
		n1 := callrecursive(tree, cur, fixedlen, -1)
		if n1 < 0 {
			return -1
		} else {
			return len + n1
		}
	case tSeq:
		n1 := fixedlen(tree, sib1(tree, cur))
		if n1 < 0 {
			return -1
		}
		// else return len+fixedlen(tree,sib2(tree,cur))
		len += n1
		cur = sib2(tree, cur)
		goto tailcall
	case tChoice:
		n1 := fixedlen(tree, sib1(tree, cur))
		n2 := fixedlen(tree, sib2(tree, cur))
		if n1 != n2 || n1 < 0 {
			return -1
		} else {
			return len + n1
		}
	default:
		panic(tree[cur].tag)
	}
}

func hascaptures(tree []tTree, cur int32) bool {
tailcall:
	switch tree[cur].tag {
	case tCapture, tRunTime:
		return true
	case tCall:
		return callrecursivebool(tree, cur, hascaptures, false)
	case tRule:
		cur = sib1(tree, cur)
		goto tailcall
	case tOpenCall:
		panic(tree[cur])
	default:
		switch numsiblings[tree[cur].tag] {
		case 1:
			cur = sib1(tree, cur)
			goto tailcall
		case 2:
			if hascaptures(tree, sib1(tree, cur)) {
				return true
			}
			cur = sib2(tree, cur)
			goto tailcall
		default:
			return false
		}
	}
}

func needfollow(tree []tTree, cur int32) bool {
tailcall:
	switch tree[cur].tag {
	case tChar, tSet, tAny, tFalse, tTrue, tAnd, tNot, tRunTime, tGrammar, tCall, tBehind:
		return false
	case tChoice, tRep:
		return true
	case tCapture:
		cur = sib1(tree, cur)
		goto tailcall
	case tSeq:
		cur = sib2(tree, cur)
		goto tailcall
	default:
		panic(tree[cur])
	}
}

func cscomplement(cs *charset) {
	for i := 0; i < charsetSize; i++ {
		cs.cs[i] = ^cs.cs[i]
	}
}

func csdisjoint(cs1 *charset, cs2 *charset) bool {
	for i := 0; i < charsetSize; i++ {
		if cs1.cs[i]&cs2.cs[i] != 0 {
			return false
		}
	}
	return true
}

func codechar(compst *compileState, c int32, tt int32) {
	if tt >= 0 && getinstr(compst, tt).code == iTestChar && getinstr(compst, tt).aux == byte(c) {
		addinstruction(compst, iAny, 0)
	} else {
		addinstruction(compst, iChar, c)
	}
}

func csequal(cs1 []byte, cs2 []byte) bool {
	return true
}

func addcharset(compst *compileState, cs []byte) {
	p := compst.ncode
	for i := int32(0); i < charsetInstsize-1; i++ {
		nextinstruction(compst) // space for buffer
	}
	cs2 := tobuff(&compst.p.code[p])
	copy(cs2, cs)
}

func codecharset(compst *compileState, cs []byte, tt int32) {
	op, c := charsettype(cs)
	switch op {
	case iChar:
		codechar(compst, c, tt)
	case iSet:
		if tt >= 0 && getinstr(compst, tt).code == iTestSet && csequal(cs, tobuff(&compst.p.code[tt+2])) {
			addinstruction(compst, iAny, 0)
		} else {
			addinstruction(compst, iSet, 0)
			addcharset(compst, cs)
		}
	default:
		addinstruction(compst, op, c)
	}
}

func tocharset(tree []tTree, cur int32, cs *charset) bool {
	switch tree[cur].tag {
	case tSet:
		copy(cs.cs[:], treebuffer(tree, cur))
		return true
	case tChar:
		for i := 0; i < charsetSize; i++ {
			cs.cs[i] = 0
		}
		setchar(cs.cs[:], byte(tree[cur].psn)) // n
		return true
	case tAny:
		for i := 0; i < charsetSize; i++ {
			cs.cs[i] = 0xff
		}
		return true
	}
	return false
}

func sizei(i *instruction) int32 {
	switch toinst(i).code {
	case iSet, iSpan:
		return charsetInstsize
	case iTestSet:
		return charsetInstsize + 1
	case iTestChar, iTestAny, iChoice, iJmp, iCall, iOpenCall, iCommit, iParticalCommit, iBackCommit:
		return 2
	default:
		return 1
	}
}

func addoffsetinst(compst *compileState, op opCode) int32 {
	i := addinstruction(compst, op, 0)
	addinstruction(compst, 0, 0)
	if op == iTestSet || sizei(&compst.p.code[i]) == 2 {
	} else {
		panic(op)
	}
	return i
}

func codetestset(compst *compileState, cs *charset, e int) int32 {
	if e != 0 {
		return noinst
	}
	op, c := charsettype(cs.cs[:])
	switch op {
	case iFail:
		return addoffsetinst(compst, iJmp)
	case iAny:
		return addoffsetinst(compst, iTestAny)
	case iChar:
		i := addoffsetinst(compst, iTestChar)
		getinstr(compst, i).aux = byte(c)
		return i
	case iSet:
		i := addoffsetinst(compst, iTestSet)
		addcharset(compst, cs.cs[:])
		return i
	default:
		panic(op)
	}
}

func getfirst(tree []tTree, cur int32, follow, firstset *charset) int {
tailcall:
	switch tree[cur].tag {
	case tChar, tSet, tAny:
		tocharset(tree, cur, firstset)
		return 0
	case tTrue:
		for i := 0; i < charsetSize; i++ {
			firstset.cs[i] = follow.cs[i]
		}
		return 1 // accepts the empty string
	case tFalse:
		for i := 0; i < charsetSize; i++ {
			firstset.cs[i] = 0
		}
		return 0
	case tChoice:
		var csaux charset
		e1 := getfirst(tree, sib1(tree, cur), follow, firstset)
		e2 := getfirst(tree, sib2(tree, cur), follow, &csaux)
		for i := 0; i < charsetSize; i++ {
			firstset.cs[i] |= csaux.cs[i]
		}
		return e1 | e2
	case tSeq:
		if !nullable(tree, sib1(tree, cur)) {
			cur = sib1(tree, cur)
			follow = fullset
			goto tailcall // return getfirst(tree,sib1(tree,cur),fullset,firstset)
		}
		var csaux charset
		e2 := getfirst(tree, sib2(tree, cur), follow, &csaux)
		e1 := getfirst(tree, sib1(tree, cur), &csaux, firstset)
		if e1 == 0 {
			return 0
		} else if (e1|e2)&2 != 0 {
			return 2
		}
		return e2
	case tRep:
		getfirst(tree, sib1(tree, cur), follow, firstset)
		for i := 0; i < charsetSize; i++ {
			firstset.cs[i] |= follow.cs[i]
		}
		return 1
	case tCapture, tGrammar, tRule:
		cur = sib1(tree, cur)
		goto tailcall
	case tRunTime:
		e := getfirst(tree, sib1(tree, cur), fullset, firstset)
		if e != 0 {
			return 2
		}
		return 0
	case tCall:
		cur = sib2(tree, cur)
		goto tailcall
	case tAnd:
		e := getfirst(tree, sib1(tree, cur), follow, firstset)
		for i := 0; i < charsetSize; i++ {
			firstset.cs[i] &= follow.cs[i]
		}
		return e
	case tNot:
		if tocharset(tree, sib1(tree, cur), firstset) {
			cscomplement(firstset)
			return 1
		}
		fallthrough
	case tBehind:
		e := getfirst(tree, sib1(tree, cur), follow, firstset)
		for i := 0; i < charsetSize; i++ {
			firstset.cs[i] = follow.cs[i]
		}
		return e | 1
	default:
		panic(tree[cur].tag)
	}
}

func target(code []instruction, i int32) int32 {
	return i + tooffset(&code[i+1]).offset
}

func choicedisjoint(tree []tTree, p2 int32, fl, cs1, cs2 *charset) bool {
	getfirst(tree, p2, fl, cs2)
	return csdisjoint(cs1, cs2)
}

func setoffset(compst *compileState, instruction int32, offset int32) {
	tooffset(&compst.p.code[instruction+1]).offset = offset
}

func jumptothere(compst *compileState, instruction int32, target int32) {
	if instruction >= 0 {
		setoffset(compst, instruction, target-instruction)
	}
}

func jumptohere(compst *compileState, instruction int32) {
	jumptothere(compst, instruction, compst.ncode)
}

func codechoice(compst *compileState, tree []tTree, p1, p2 int32, opt bool, fl *charset) {
	emptyp2 := tree[p2].tag == tTrue
	var cs1, cs2 charset
	e1 := getfirst(tree, p1, fullset, &cs1)
	if headfail(tree, p1) || (e1 == 0 && (choicedisjoint(tree, p2, fl, &cs1, &cs2))) {
		// <p1 / p2> == test (fail(p1)) -> L1 ; p1 ; jmp L2; L1: p2; L2:
		test := codetestset(compst, &cs1, 0)
		jmp := noinst
		codegen(compst, tree, p1, false, test, fl)
		if !emptyp2 {
			jmp = addoffsetinst(compst, iJmp)
		}
		jumptohere(compst, test)
		codegen(compst, tree, p2, opt, noinst, fl)
		jumptohere(compst, jmp)
	} else if opt && emptyp2 {
		// p1? == IPartialCommit; p1
		jumptohere(compst, addoffsetinst(compst, iParticalCommit))
		codegen(compst, tree, p1, true, noinst, fullset)
	} else {
		// <p1 / p2> == test(first(p1)) -> L1; choice L1; <p1>; commit L2; L1: <p2>; L2:
		test := codetestset(compst, &cs1, e1)
		pchoice := addoffsetinst(compst, iChoice)
		codegen(compst, tree, p1, emptyp2, test, fullset)
		pcommit := addoffsetinst(compst, iCommit)
		jumptohere(compst, pchoice)
		jumptohere(compst, test)
		codegen(compst, tree, p2, opt, noinst, fl)
		jumptohere(compst, pcommit)
	}
}

func coderep(compst *compileState, tree []tTree, cur int32, opt bool, fl *charset) {
	var st charset
	if tocharset(tree, cur, &st) {
		addinstruction(compst, iSpan, 0)
		addcharset(compst, st.cs[:])
		return
	}
	e1 := getfirst(tree, cur, fullset, &st)
	if headfail(tree, cur) || e1 == 0 && csdisjoint(&st, fl) {
		// L1: test (fail(p1)) -> L2; <p>; jmp L1; L2:
		test := codetestset(compst, &st, 0)
		codegen(compst, tree, cur, false, test, fullset)
		jmp := addoffsetinst(compst, iJmp)
		jumptohere(compst, test)
		jumptothere(compst, jmp, test)
		return
	}
	// test(fail(p1)) -> L2; choice L2; L1: <p>; partialcommit L1; L2:
	// or (if 'opt'): partialcommit L1; L1: <p>; partialcommit L1;
	test := codetestset(compst, &st, e1)
	pchoice := noinst
	if opt {
		jumptohere(compst, addoffsetinst(compst, iParticalCommit))
	} else {
		pchoice = addoffsetinst(compst, iChoice)
	}
	l2 := compst.ncode
	codegen(compst, tree, cur, false, noinst, fullset)
	commit := addoffsetinst(compst, iParticalCommit)
	jumptothere(compst, commit, l2)
	jumptohere(compst, pchoice)
	jumptohere(compst, test)
}

func codebehind(compst *compileState, tree []tTree, cur int32) {
	if tree[cur].psn > 0 { // n
		addinstruction(compst, iBehind, tree[cur].psn)
	}
	codegen(compst, tree, sib1(tree, cur), false, noinst, fullset)
}

func codenot(compst *compileState, tree []tTree, cur int32) {
	var st charset
	e := getfirst(tree, cur, fullset, &st)
	test := codetestset(compst, &st, e)
	if headfail(tree, cur) {
		// test (fail(p1)) -> L1; fail; L1:
		addinstruction(compst, iFail, 0)
	} else {
		// test(fail(p))-> L1; choice L1; <p>; failtwice; L1:
		pchoice := addoffsetinst(compst, iChoice)
		codegen(compst, tree, cur, false, noinst, fullset)
		addinstruction(compst, iFailTwice, 0)
		jumptohere(compst, pchoice)
	}
	jumptohere(compst, test)
}

func codeand(compst *compileState, tree []tTree, cur int32, tt int32) {
	n := fixedlen(tree, cur)
	if n >= 0 && n <= maxBehind && !hascaptures(tree, cur) {
		codegen(compst, tree, cur, false, tt, fullset)
		if n > 0 {
			addinstruction(compst, iBehind, n)
		}
		return
	}
	pchoice := addoffsetinst(compst, iChoice)
	codegen(compst, tree, cur, false, tt, fullset)
	pcommit := addoffsetinst(compst, iBackCommit)
	jumptohere(compst, pchoice)
	addinstruction(compst, iFail, 0)
	jumptohere(compst, pcommit)
}

func joinkindoff(kind int, off int) int32 {
	return int32(kind | off<<4)
}

func addinstcap(compst *compileState, op opCode, cap capKind, key uint16, aux int32) int32 {
	i := addinstruction(compst, op, joinkindoff(int(cap), int(aux)))
	getinstr(compst, i).key = key
	return i
}

func codecapture(compst *compileState, tree []tTree, cur int32, tt int32, fl *charset) {
	len := fixedlen(tree, sib1(tree, cur))
	if len >= 0 && len <= maxOff && !hascaptures(tree, sib1(tree, cur)) {
		codegen(compst, tree, sib1(tree, cur), false, tt, fl)
		addinstcap(compst, iFullCapture, tree[cur].cap, tree[cur].key, len)
	} else {
		addinstcap(compst, iOpenCapture, tree[cur].cap, tree[cur].key, 0)
		codegen(compst, tree, sib1(tree, cur), false, tt, fl)
		addinstcap(compst, iCloseCapture, cClose, 0, 0)
	}
}

func coderuntime(compst *compileState, tree []tTree, cur int32, tt int32) {
	addinstcap(compst, iOpenCapture, cGroup, tree[cur].key, 0)
	codegen(compst, tree, sib1(tree, cur), false, tt, fullset)
	addinstcap(compst, iCloseRunTime, cClose, 0, 0)
}

func correctcalls(compst *compileState, positions []int32, from, to int32) {
	code := compst.p.code
	for i := from; i < to; i += sizei(&code[i]) {
		inst := toinst(&code[i])
		if inst.code == iOpenCall {
			n := inst.key // rule number
			rule := positions[n]
			if rule == from || toinst(&code[rule-1]).code == iRet {
			} else {
				panic(code[rule-1])
			}
			if toinst(&code[finaltarget(code, i+2)]).code == iRet {
				inst.code = iJmp
			} else {
				inst.code = iCall
			}
			jumptothere(compst, i, rule)
		}
	}
}

// call L1; jmp L2; L1: rule 1; ret; rule 2; ret; ...; L2:
func codegrammar(compst *compileState, tree []tTree, cur int32) {
	var positions [maxRules]int32
	firstcall := addoffsetinst(compst, iCall)
	jumptoend := addoffsetinst(compst, iJmp)
	start := compst.ncode
	jumptohere(compst, firstcall)
	var rulenumber int
	for rule := sib1(tree, cur); tree[rule].tag == tRule; rule = sib2(tree, rule) {
		positions[rulenumber] = compst.ncode
		rulenumber++
		codegen(compst, tree, sib1(tree, rule), false, noinst, fullset)
		addinstruction(compst, iRet, 0)
	}
	jumptohere(compst, jumptoend)
	correctcalls(compst, positions[:], start, compst.ncode)
}

func codecall(compst *compileState, tree []tTree, cur int32) {
	c := addoffsetinst(compst, iOpenCall)                       // to be corrected later
	getinstr(compst, c).key = uint16(tree[sib2(tree, cur)].cap) // rule number
}

func codeseq1(compst *compileState, tree []tTree, p1, p2, tt int32, fl *charset) int32 {
	if needfollow(tree, p1) {
		var fl1 charset
		getfirst(tree, p2, fl, &fl1)
		codegen(compst, tree, p1, false, tt, &fl1)
	} else {
		codegen(compst, tree, p1, false, tt, fullset)
	}
	if fixedlen(tree, p1) != 0 {
		return noinst
	}
	return tt
}

func codegen(compst *compileState, tree []tTree, cur int32, opt bool, tt int32, fl *charset) {
tailcall:
	switch tree[cur].tag {
	case tChar:
		codechar(compst, tree[cur].psn, tt) // n
	case tAny:
		addinstruction(compst, iAny, 0)
	case tSet:
		b := treebuffer(tree, cur)
		codecharset(compst, b, tt)
	case tTrue:
	case tFalse:
		addinstruction(compst, iFail, 0)
	case tChoice:
		codechoice(compst, tree, sib1(tree, cur), sib2(tree, cur), opt, fl)
	case tRep:
		coderep(compst, tree, sib1(tree, cur), opt, fl)
	case tBehind:
		codebehind(compst, tree, cur)
	case tNot:
		codenot(compst, tree, sib1(tree, cur))
	case tAnd:
		codeand(compst, tree, sib1(tree, cur), tt)
	case tCapture:
		codecapture(compst, tree, cur, tt, fl)
	case tRunTime:
		coderuntime(compst, tree, cur, tt)
	case tGrammar:
		codegrammar(compst, tree, cur)
	case tCall:
		codecall(compst, tree, cur)
	case tSeq:
		tt = codeseq1(compst, tree, sib1(tree, cur), sib2(tree, cur), tt, fl)
		cur = sib2(tree, cur)
		goto tailcall // codegen(compst,tree,p2,opt,tt,fl)
	}
}

func finaltarget(code []instruction, i int32) int32 {
	for toinst(&code[i]).code == iJmp {
		i = target(code, i)
	}
	return i
}

func finallabel(code []instruction, i int32) int32 {
	return finaltarget(code, target(code, i))
}

func peephole(compst *compileState) {
	code := compst.p.code
	for i := int32(0); i < compst.ncode; i += sizei(&code[i]) {
	redo:
		switch toinst(&code[i]).code {
		case iChoice, iCall, iCommit, iParticalCommit, iBackCommit, iTestChar, iTestSet, iTestAny:
			jumptothere(compst, i, finallabel(code, i))
		case iJmp:
			ft := finaltarget(code, i)
			switch toinst(&code[ft]).code {
			case iRet, iFail, iFailTwice, iEnd:
				code[i] = code[ft]
				toinst(&code[i+1]).code = iAny
			case iCommit, iParticalCommit, iBackCommit:
				fft := finallabel(code, ft)
				code[i] = code[ft]
				jumptothere(compst, i, fft)
				goto redo
			default:
				jumptothere(compst, i, ft)
			}
		}
	}
	if toinst(&code[compst.ncode-1]).code != iEnd {
		panic(toinst(&code[compst.ncode-1]))
	}
}

func compile(p *Pattern) []instruction {
	var compst compileState
	compst.p = p
	compst.ncode = 0
	realloccode(p, 2)
	codegen(&compst, p.tree, 0, false, noinst, fullset)
	addinstruction(&compst, iEnd, 0)
	realloccode(p, int(compst.ncode))
	peephole(&compst)
	return p.code
}
