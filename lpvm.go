package lpeg

import (
	"reflect"
	"unsafe"
)

const charsetSize = 0xff/8 + 1
const charsetInstsize = (charsetSize+int32(unsafe.Sizeof(*(*instruction)(nil)))-1)/int32(unsafe.Sizeof(*(*instruction)(nil))) + 1

type opCode byte

const (
	iAny opCode = iota
	iChar
	iSet
	iTestAny
	iTestChar
	iTestSet
	iSpan
	iBehind
	iRet
	iEnd
	iChoice
	iJmp
	iCall
	iOpenCall
	iCommit
	iParticalCommit
	iBackCommit
	iFailTwice
	iFail
	iFullCapture
	iOpenCapture
	iCloseCapture
	iCloseRunTime
)

const nullPosition = -1

type codeInst struct {
	code opCode
	aux  byte
	key  uint16
}
type codeOffset struct {
	offset int32
}
type codeBuff struct {
	buff [1]byte
}
type instruction [4]byte

func toinst(i *instruction) *codeInst {
	return (*codeInst)(unsafe.Pointer(i))
}
func tooffset(i *instruction) *codeOffset {
	return (*codeOffset)(unsafe.Pointer(i))
}
func tobuff(i *instruction) []byte {
	buff := (*codeBuff)(unsafe.Pointer(i))
	b := reflect.SliceHeader{
		Data: uintptr(unsafe.Pointer(&buff.buff[0])),
		Len:  charsetSize,
		Cap:  charsetSize,
	}
	return *(*[]byte)(unsafe.Pointer(&b))
}

type stackFrame struct {
	s     int   // saved position (or -1 for calls)
	p     int32 // next instruction
	caplv int
}

func getoffset(op []instruction, p int32) int32 {
	return tooffset(&op[p+1]).offset
}

func testchar(st []byte, c byte) bool {
	return (st)[(c>>3)]&(1<<(c&7)) != 0
}

func doublestack(stack []stackFrame) []stackFrame {
	if len(stack) >= 0xffff {
		panic("backtrack stack overflow")
	}
	newstack := make([]stackFrame, 2*len(stack))
	copy(newstack, stack)
	return newstack
}

func doublecap(cap []capture, captop int, n int) []capture {
	if len(cap) >= 0xffffffff/(2*int(unsafe.Sizeof(*(*capture)(nil)))) {
		panic("too many captures")
	}
	newc := make([]capture, 2*captop)
	copy(newc, cap[:captop-n])
	return newc
}

func removedyncap(cs *capState, cap []capture, level int, last int) int {
	id, ok := finddyncap(cap, level, last)
	if !ok {
		return 0
	}
	top := len(cs.push)
	cs.push = cs.push[:id-1]
	return top - int(id) + 1
}

func adddyncaptures(s int, base []capture, n int, fd int) {
	base[0].kind = cGroup
	base[0].siz = 0
	base[0].idx = 0 // anonymous group
	i := 1
	for ; i <= n; i++ {
		base[i].kind = cRuntime
		base[i].siz = 1 // mark it as closed
		base[i].idx = uint16(fd + i - 1)
		base[i].s = s
	}
	base[i].kind = cClose
	base[i].siz = 1
	base[i].s = s
}

func getkind(i *instruction) capKind {
	return capKind(toinst(i).aux & 0xf)
}

func getoff(i *instruction) byte {
	return toinst(i).aux >> 4 & 0xf
}

func match(subject string, s int, op []instruction, cs *capState) (int, []capture) {
	var initStack [256]stackFrame
	var initCapture [32]capture
	var stack = initStack[:]
	var cap = initCapture[:]
	var top = 0
	var captop = 0
	var ndyncap = 0
	const giveupInstruction = -1
	stack[top].p = giveupInstruction
	stack[top].s = 0
	stack[top].caplv = 0
	top++
	p := int32(0)
	e := len(subject)
	for {
		if len(cs.push) > captop {
			panic(cs.push)
		}
		if p == giveupInstruction {
			return -1, nil
		}
		switch toinst(&op[p]).code {
		case iEnd:
			cap[captop].kind = cClose
			cap[captop].s = nullPosition
			return s, cap[:captop+1]
		case iRet:
			top--
			p = stack[top].p
			continue
		case iAny:
			if s < e {
				p++
				s++
			} else {
				goto fail
			}
			continue
		case iTestAny:
			if s < e {
				p += 2
			} else {
				p += getoffset(op, p)
			}
			continue
		case iChar:
			if s < e && subject[s] == toinst(&op[p]).aux {
				p++
				s++
			} else {
				goto fail
			}
			continue
		case iTestChar:
			if s < e && subject[s] == toinst(&op[p]).aux {
				p += 2
			} else {
				p += getoffset(op, p)
			}
			continue
		case iSet:
			if s < e && testchar(tobuff(&op[p+1]), subject[s]) {
				p += charsetInstsize
				s++
			} else {
				goto fail
			}
			continue
		case iTestSet:
			if s < e && testchar(tobuff(&op[p+2]), subject[s]) {
				p += 1 + charsetInstsize
			} else {
				p += getoffset(op, p)
			}
			continue
		case iBehind:
			n := int(toinst(&op[p]).aux)
			if n > s {
				goto fail
			}
			s -= n
			p++
			continue
		case iSpan:
			for ; s < e; s++ {
				if !testchar(tobuff(&op[p+1]), subject[s]) {
					break
				}
			}
			p += charsetInstsize
			continue
		case iJmp:
			p += getoffset(op, p)
			continue
		case iChoice:
			if top == len(stack) {
				stack = doublestack(stack)
			}
			stack[top].p = p + getoffset(op, p)
			stack[top].s = s
			stack[top].caplv = captop
			top++
			p += 2
			continue
		case iCall:
			if top == len(stack) {
				stack = doublestack(stack)
			}
			stack[top].s = nullPosition
			stack[top].p = p + 2 // save return address
			top++
			p += getoffset(op, p)
			continue
		case iCommit:
			top--
			p += getoffset(op, p)
			continue
		case iParticalCommit:
			stack[top-1].s = s
			stack[top-1].caplv = captop
			p += getoffset(op, p)
			continue
		case iBackCommit:
			top--
			s = stack[top].s
			captop = stack[top].caplv
			p += getoffset(op, p)
			continue
		case iFailTwice:
			top--
			fallthrough
		case iFail:
			goto fail
		case iCloseRunTime:
			cs.ocap = cap
			suc, pos, adddyn, remcap, remdyn := runtimecap(cs, captop, s)
			captop -= remcap
			ndyncap -= remdyn
			if !suc {
				goto fail
			}
			s = pos - 1 // position start from 1
			if adddyn > 0 {
				ndyncap += adddyn
				captop += adddyn + 2
				if captop >= len(cap) {
					cap = doublecap(cap, captop, adddyn+2)
				}
				adddyncaptures(s, cap[captop-adddyn-2:], adddyn, len(cs.push)-adddyn)
			}
		case iCloseCapture:
			s1 := s
			if cap[captop-1].siz == 0 && s1-cap[captop-1].s < 0xff {
				cap[captop-1].siz = byte(s1 - cap[captop-1].s + 1)
				p++
				continue
			}
			cap[captop].siz = 1
			cap[captop].s = s
			goto pushcapture
		case iOpenCapture:
			cap[captop].siz = 0
			cap[captop].s = s
			goto pushcapture
		case iFullCapture:
			cap[captop].siz = getoff(&op[p]) + 1
			cap[captop].s = s - int(getoff(&op[p]))
			goto pushcapture
		}
	fail:
		top--
		s = stack[top].s
		for s == nullPosition {
			top--
			s = stack[top].s
		}
		if ndyncap > 0 { // is there matchtime captures?
			ndyncap -= removedyncap(cs, cap, stack[top].caplv, captop)
		}
		captop = stack[top].caplv
		p = stack[top].p
		continue
	pushcapture:
		cap[captop].idx = toinst(&op[p]).key
		cap[captop].kind = getkind(&op[p])
		captop++
		if captop >= len(cap) {
			cap = doublecap(cap, captop, 0)
		}
		p++
		continue
	}
}
