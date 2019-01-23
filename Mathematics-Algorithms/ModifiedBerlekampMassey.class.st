"
This is a modified [1] Berlekamp-Massey algorithm. This modified version admits lazy evaluation.

Input: a_1..a_{2n} the first 2n coefficients of a linear recursive sequence over a field K of order at most n (the minimal polynomial has degree bound n);
Output: the minimal polynomial of the sequence.

[1] 'The Berlekamp-Massey Algorithm revisited', Nadie Ben Atti, Gema M Diaz-Toca, Henri Lombardi.

"
Class {
	#name : #ModifiedBerlekampMassey,
	#superclass : #Object,
	#instVars : [
		'input',
		'field',
		'minimalPolynomial'
	],
	#category : #'Mathematics-Algorithms'
}

{ #category : #accessing }
ModifiedBerlekampMassey >> field: aField [
	field := aField
]

{ #category : #accessing }
ModifiedBerlekampMassey >> input: anArray [
	input := anArray.
	minimalPolynomial := nil
]

{ #category : #accessing }
ModifiedBerlekampMassey >> minimalPolynomial [
	minimalPolynomial isNil ifTrue: [self run].
	^ minimalPolynomial
]

{ #category : #private }
ModifiedBerlekampMassey >> run [
	"Modified Berlekamp-Massey from 'The Berlekamp-Massey Algorithm revisited', Nadie Ben Atti, Gema M Diaz-Toca, Henri Lombardi."
	| Fx x R0 R1 V V0 V1 n m |
	n := input size // 2.
	m := 2*n - 1.
	Fx := field polynomials.
	x := Fx x.
	R0 := x raisedTo: (2*n). R1 := (0 to: m) sum: [:i| (x raisedTo: i)*(input at: m-i+1)].
	V0 := Fx zero. V1 := Fx one.
	[n <= R1 degree]
		whileTrue:
			[ | division |
			division := R0 divisionBy: R1.
			V := V0 - (division quotient * V1).
			V0 := V1. V1 := V. R0 := R1. R1 := division remainder].
	minimalPolynomial := V1 / V1 leadingCoefficient
]
