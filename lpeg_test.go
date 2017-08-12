package lpeg

import (
	"fmt"
	"testing"
)

func TestPatt(*testing.T) {
	patt := P("5")
	a, b := Match(patt, "57")
	fmt.Println(a, b)
}
