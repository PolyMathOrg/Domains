Extension { #name : #SmallInteger }

{ #category : #'*mathematics' }
SmallInteger >> bitCount [
	"Answer the number of bits that are set, i.e. the number of 1s in the binary representation."
	| v count |
	v := self.
	count := 0.
	[v = 0] whileFalse: [v := v bitAnd: v - 1. count := count + 1].
	^ count
	
	"HACKMEM:
	| count |
	self flag: #fix.
	count := self - ((self >> 1) bitAnd: 8r33333333333) - ((self >> 1) bitAnd: 8r11111111111).
	^ (count + (count >> 3) bitAnd: 8r30707070707) \\ 63
"

]

{ #category : #'*mathematics' }
SmallInteger >> bitParity [
	"Answer 1 if there are an odd number of bits set, 0 otherwise."
	| v parity |
	v := self.
	parity := 0.
	[v = 0] whileFalse: [parity := parity bitXor: (v bitAnd: 1). v := v bitShift: -1].
	^ parity

"	n := self.
	n := n bitXor: (n bitShift: -16).
	n := n bitXor: (n bitShift: -8).
	n := n bitXor: (n bitShift: -4).
	n := n bitAnd: 16rF.
	^ (16r6996 bitShift: n negated) bitAnd: 1
"
]
