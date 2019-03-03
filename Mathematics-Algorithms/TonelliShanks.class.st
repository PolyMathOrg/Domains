"
This is the Tonelli-Shanks algorithm for computing square roots in a prime field Z/pZ.

Reference: Henri Cohen, 'A Course in Computational Algebraic Number Theory', Algorithm 1.5.1.
"
Class {
	#name : #TonelliShanks,
	#superclass : #Object,
	#instVars : [
		'p',
		'q',
		'e',
		'z'
	],
	#category : #'Mathematics-Algorithms'
}

{ #category : #'as yet unclassified' }
TonelliShanks >> modulus: anInteger [
	| n |
	anInteger == 2
		ifTrue: [ self error: 'the modulus should be not 2' ].
	p := anInteger.
	e := (p - 1) lowBit - 1.
	q := p - 1 bitShift: e negated.
	"find generator of the multiplicative group of units (Z/pZ)*"
	[ n := (p - 1) atRandom.
	(n kronecker: p) == -1 ] whileFalse.
	z := n raisedTo: q modulo: p
]

{ #category : #'as yet unclassified' }
TonelliShanks >> squareRootOf: anInteger [
	| a y r x b m b2 t |
	anInteger == 0 ifTrue: [^ anInteger].
	a := anInteger.
	y := z. r := e. x := a raisedTo: q-1 // 2 modulo: p. b := a*x squared \\ p. x := a*x \\ p.
	[b == 1 ifTrue: [^ x].
	b2 := b. m := 1. [(b2 := b2 squared \\ p) == 1] whileFalse: [m := m + 1].
	(b raisedTo: (2 raiseTo: m) modulo: p) == 1 ifFalse: [self halt].
	(m > 1 and: [(b raisedTo: (2 raiseTo: (m-1)) modulo: p) == 1]) ifTrue: [self halt].
	m = r ifTrue: [^ nil]. "the input is not a quadratic residue modulo p"
	t := y. r - m - 1 timesRepeat: [t := t squared \\ p]. "t := y ^ (2 ^ (r - m - 1)) mod p"
	y := t squared \\ p. r := m. x := x * t \\ p. b := b * y \\ p] repeat
]
