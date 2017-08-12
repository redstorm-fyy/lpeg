package lpeg

import (
	"bytes"
)

type capKind byte

const (
	cClose capKind = iota // not used in trees
	cPosition
	cConst
	cBackref
	cArg
	cSimple
	cTable
	cFunction
	cQuery
	cString
	cNum
	cSubst
	cFold
	cRuntime
	cGroup
)

type capture struct {
	s    int    // subject position
	idx  uint16 // extra info (group name,arg index,etc.)
	kind capKind
	siz  byte // size of full capture + 1 (0 = not a full capture)
}

type capState struct {
	cap  int       // current capture
	ocap []capture // (original) capture list
	s    string    // original string
	args []interface{}
	k    *ktable
	push []interface{}
}

func isfullcap(cap *capture) bool {
	return cap.siz != 0
}

func isclosecap(cap *capture) bool {
	return cap.kind == cClose
}

func closeaddr(cap *capture) int {
	return cap.s + int(cap.siz) - 1
}

func getvalue(cs *capState, cap int) interface{} {
	return cs.k.tb[cs.ocap[cap].idx]
}

func nextcap(cs *capState) {
	if !isfullcap(&cs.ocap[cs.cap]) {
		n := 0 // number of opens waiting a close
		for {
			cs.cap++
			if isclosecap(&cs.ocap[cs.cap]) {
				nn := n
				n--
				if nn == 0 {
					break
				}
			} else if !isfullcap(&cs.ocap[cs.cap]) {
				n++
			}
		}
	}
	cs.cap++ // skip last close(or entire single capture)
}

func pushnestedvalues(cs *capState, addextra bool) int {
	co := &cs.ocap[cs.cap]
	cs.cap++
	if isfullcap(co) {
		cs.push = append(cs.push, cs.s[co.s:co.s+int(co.siz)-1])
		return 1
	}
	n := 0
	for !isclosecap(&cs.ocap[cs.cap]) {
		n += pushcapture(cs)
	}
	if addextra || n == 0 {
		cs.push = append(cs.push, cs.s[co.s:co.s+cs.ocap[cs.cap].s-co.s])
		n++
	}
	cs.cap++ // skip close entry
	return n
}

func pushonenestedvalue(cs *capState) {
	n := pushnestedvalues(cs, false)
	if n > 1 {
		cs.push = cs.push[:len(cs.push)-n+1]
	}
}

type strAux struct {
	isstring bool
	cp       int
	s        int
	e        int
}

func getstrcaps(cs *capState, cps []strAux, n int) int {
	k := n
	n++
	cap := &cs.ocap[cs.cap]
	cps[k].isstring = true
	cps[k].s = cap.s
	cs.cap++
	if !isfullcap(cap) {
		for !isclosecap(&cs.ocap[cs.cap]) {
			if n >= len(cps) { // too many captures?
				nextcap(cs) // skip extra captures(will not need them)
			} else if cs.ocap[cs.cap].kind == cSimple {
				n = getstrcaps(cs, cps, n)
			} else {
				cps[n].isstring = false
				cps[n].cp = cs.cap
				nextcap(cs)
				n++
			}
		}
		cs.cap++ // skip close
	}
	cps[k].e = closeaddr(&cs.ocap[cs.cap-1])
	return n
}

func addonestring(b *bytes.Buffer, cs *capState) int {
	switch cs.ocap[cs.cap].kind {
	case cString:
		stringcap(b, cs)
		return 1
	case cSubst:
		substcap(b, cs)
		return 1
	default:
		n := pushcapture(cs)
		if n > 0 {
			one := cs.push[len(cs.push)-n]
			b.WriteString(one.(string))
			cs.push = cs.push[:len(cs.push)-n]
		}
		return n
	}
}

func stringcap(b *bytes.Buffer, cs *capState) {
	var cps [10]strAux
	fmt := getvalue(cs, cs.cap).(string)
	n := getstrcaps(cs, cps[:], 0) - 1 // collect nested captures
	for i := 0; i < len(fmt); i++ {
		if fmt[i] != '%' {
			b.WriteByte(fmt[i])
			continue
		}
		i++
		if fmt[i] < '0' || fmt[i] > '9' {
			b.WriteByte(fmt[i])
			continue
		}
		l := fmt[i] - '0'
		if int(l) > n {
			panic("invalid capture index")
		} else if cps[l].isstring {
			b.WriteString(cs.s[cps[l].s:cps[l].e])
		} else {
			curr := cs.cap
			cs.cap = cps[l].cp
			if addonestring(b, cs) == 0 {
				panic("no values in capture index")
			}
			cs.cap = curr
		}
	}
}

func substcap(b *bytes.Buffer, cs *capState) {
	curr := cs.ocap[cs.cap].s
	if isfullcap(&cs.ocap[cs.cap]) {
		b.WriteString(cs.s[curr : curr+int(cs.ocap[cs.cap].siz)-1])
	} else {
		cs.cap++ // skip open entry
		for !isclosecap(&cs.ocap[cs.cap]) {
			next := cs.ocap[cs.cap].s
			b.WriteString(cs.s[curr : curr+next-curr])
			if addonestring(b, cs) != 0 {
				curr = closeaddr(&cs.ocap[cs.cap-1])
			} else {
				curr = next
			}
		}
		b.WriteString(cs.s[curr:cs.ocap[cs.cap].s])
	}
	cs.cap++
}

func pushcapture(cs *capState) int {
	switch cap := &cs.ocap[cs.cap]; cap.kind {
	case cPosition:
		cs.push = append(cs.push, int(cap.s+1)) // start from 1
		cs.cap++
		return 1
	case cConst:
		cs.push = append(cs.push, getvalue(cs, cs.cap))
		cs.cap++
		return 1
	case cArg: // start from 1
		const fixedArgnum = 3
		arg := cap.idx
		cs.cap++
		if int(arg) > len(cs.args) || arg <= 0 {
			panic("reference to absent extra argument")
		}
		cs.push = append(cs.push, cs.args[arg-1])
		return 1
	case cSimple:
		k := pushnestedvalues(cs, true)
		n := len(cs.push)
		if k > 1 { // make whole match be first result
			last := cs.push[n-1]
			copy(cs.push[n-k+1:], cs.push[n-k:])
			cs.push[n-k] = last
		}
		return k
	case cRuntime:
		cs.push = append(cs.push, int(cap.idx))
		cs.cap++
		return 1
	case cString:
		var b bytes.Buffer
		stringcap(&b, cs)
		cs.push = append(cs.push, b.String())
		return 1
	case cSubst:
		var b bytes.Buffer
		substcap(&b, cs)
		cs.push = append(cs.push, b.String())
		return 1
	case cGroup:
		if cs.ocap[cs.cap].idx == 0 {
			// anonymous group
			return pushnestedvalues(cs, false)
		}
		// named group
		nextcap(cs) // skill capture
		return 0
	case cBackref:
		return backrefcap(cs)
	case cTable:
		return tablecap(cs)
	case cFunction:
		return functioncap(cs)
	case cNum:
		return numcap(cs)
	case cQuery:
		return querycap(cs)
	case cFold:
		return foldcap(cs)
	default:
		panic(cap.kind)
	}
}

func findopen(cs *capState, cap int) int {
	n := 0
	for {
		cap--
		if isclosecap(&cs.ocap[cap]) {
			n++
		} else if !isfullcap(&cs.ocap[cap]) {
			nn := n
			n--
			if nn == 0 {
				return cap
			}
		}
	}
}

func findback(cs *capState, cap int) int {
	for cap > 0 {
		cap--
		if isclosecap(&cs.ocap[cap]) {
			cap = findopen(cs, cap) // skip nested captures
		} else if !isfullcap(&cs.ocap[cap]) {
			continue
		}
		if cs.ocap[cap].kind == cGroup {
			v1 := getvalue(cs, cap)
			v2 := getvalue(cs, cs.cap)
			if v1 == v2 {
				return cap
			}
		}
	}
	panic("back reference not found")
}

func backrefcap(cs *capState) int {
	curr := cs.cap
	cs.cap = findback(cs, curr)
	n := pushnestedvalues(cs, false)
	cs.cap = curr + 1
	return n
}

func tablecap(cs *capState) int {
	tb := TableCapture{}
	cap := &cs.ocap[cs.cap]
	cs.cap++
	if isfullcap(cap) {
		cs.push = append(cs.push, tb)
		return 1
	}
	for !isclosecap(&cs.ocap[cs.cap]) {
		if cs.ocap[cs.cap].kind == cGroup && cs.ocap[cs.cap].idx != 0 { // named group?
			key := getvalue(cs, cs.cap)
			pushonenestedvalue(cs)
			value := cs.push[len(cs.push)-1]
			cs.push = cs.push[:len(cs.push)-1]
			if tb.dic == nil {
				tb.dic = make(map[interface{}]interface{}, 8)
			}
			tb.dic[key] = value
		} else {
			if tb.seq == nil {
				tb.seq = make([]interface{}, 1, 8) // start from 1
			}
			k := pushcapture(cs)
			tb.seq = append(tb.seq, cs.push[len(cs.push)-k:]...)
			cs.push = cs.push[:len(cs.push)-k]
		}
	}
	cs.push = append(cs.push, tb)
	cs.cap++
	return 1
}

func querycap(cs *capState) int {
	cap := cs.cap
	pushonenestedvalue(cs)
	key := cs.push[len(cs.push)-1]
	tb := getvalue(cs, cap).(TableCapture)
	switch key := key.(type) {
	case int:
		if key > 0 && key < len(tb.seq) {
			cs.push[len(cs.push)-1] = tb.seq[key]
			return 1
		}
		if tb.dic != nil {
			if value, ok := tb.dic[key]; ok {
				cs.push[len(cs.push)-1] = value
				return 1
			}
		}
	default:
		if tb.dic != nil {
			if value, ok := tb.dic[key]; ok {
				cs.push[len(cs.push)-1] = value
				return 1
			}
		}
	}
	cs.push = cs.push[:len(cs.push)-1]
	return 0
}

func foldcap(cs *capState) int {
	cap := cs.cap
	cs.cap++
	if isfullcap(&cs.ocap[cap]) || isclosecap(&cs.ocap[cs.cap]) {
		panic("no initial value for fold capture")
	}
	n := pushcapture(cs)
	if n == 0 {
		panic("no initial value for fold capture")
	}
	if n > 1 {
		cs.push = cs.push[:len(cs.push)-n+1]
	}
	fn := getvalue(cs, cap).(FoldFunction)
	for !isclosecap(&cs.ocap[cs.cap]) {
		cap1 := cs.push[len(cs.push)-1]
		n := pushcapture(cs)
		cap2 := cs.push[len(cs.push)-n:]
		cs.push = cs.push[:len(cs.push)-n]
		cs.push[len(cs.push)-1] = fn(cap1, cap2...)
	}
	cs.cap++ // skip close entry
	return 1
}

func functioncap(cs *capState) int {
	fn := getvalue(cs, cs.cap).(CaptureFunction)
	n := pushnestedvalues(cs, false)
	arg := cs.push[len(cs.push)-n:]
	cs.push = cs.push[:len(cs.push)-n]
	ret := fn(arg...)
	cs.push = append(cs.push, ret...)
	return len(ret)
}

func numcap(cs *capState) int {
	idx := cs.ocap[cs.cap].idx
	if idx == 0 { // no values?
		nextcap(cs) // skip entire capture
		return 0
	}
	n := pushnestedvalues(cs, false)
	if n < int(idx) {
		panic("no capture")
	}
	cs.push[len(cs.push)-n] = cs.push[len(cs.push)-1-n+int(idx)] // idx start from 1
	cs.push = cs.push[:len(cs.push)-n+1]
	return 1
}

func finddyncap(cap []capture, from, to int) (uint16, bool) {
	for i := from; i < to; i++ {
		if cap[i].kind == cRuntime {
			return cap[i].idx, true
		}
	}
	return 0, false
}

func runtimecap(cs *capState, close int, s int) (success bool, position int, adddyn int, removecap int, removedyn int) {
	otop := len(cs.push)
	open := findopen(cs, close)
	if cs.ocap[open].kind != cGroup {
		panic(open)
	}
	id, ok := finddyncap(cs.ocap, open, close)
	cs.ocap[close].kind = cClose
	cs.ocap[close].s = s
	cs.cap = open
	fn := getvalue(cs, cs.cap).(RuntimeFunction)
	n := pushnestedvalues(cs, false)
	cap := cs.push[len(cs.push)-n:]
	cs.push = cs.push[:len(cs.push)-n]
	position, newcap := fn(cs.s, s+1, cap...) // position start from 1
	removecap = close - open
	removedyn = 0
	if ok {
		cs.push = append(cs.push[:id], cs.push[otop:]...)
		removedyn = otop - int(id)
	}
	cs.push = append(cs.push, newcap...)
	adddyn = len(newcap)
	success = position >= s+1 && position < len(cs.s)+1
	return
}

func getcaptures(cs *capState) []interface{} {
	var n int
	for !isclosecap(&cs.ocap[cs.cap]) {
		n += pushcapture(cs)
	}
	if n == 0 {
		return nil
	}
	return cs.push[:n]
}
