"
This algorithm separates complex roots of polynomials with real or complex coefficients. This is Newton's modified algorithm [1], and the convergence is quadratic. The polynomial is assumed to be squarefree.

Input: a square-free polynomial of degree n with real or complex coefficients, and a desired minimum absolute error (tolerance);
Output: a collection of the n complex roots of the polynomial.

[1] ""A Course in Computational Algebraic Number Theory"", Cohen, Algorithm 3.6.6.
"
Class {
	#name : #NumericalComplexRootIsolator,
	#superclass : #Object,
	#instVars : [
		'polynomial',
		'tolerance'
	],
	#category : #'Mathematics-Polynomials-Algorithms'
}

{ #category : #'instance creation' }
NumericalComplexRootIsolator class >> polynomial: aPolynomial [
	^ self squareFreePolynomial: aPolynomial // (aPolynomial gcd: aPolynomial derivative)
]

{ #category : #'instance creation' }
NumericalComplexRootIsolator class >> squareFreePolynomial: aPolynomial [
	^ super polynomial: aPolynomial
]

{ #category : #private }
NumericalComplexRootIsolator >> initialValue [
	^ 1.3 + 0.314159 i
]

{ #category : #initialization }
NumericalComplexRootIsolator >> initialize [
	super initialize.
	tolerance := 0.1
]

{ #category : #accessing }
NumericalComplexRootIsolator >> rootNear: aComplex [
"	[self roots do: [:each| (each approximation - aComplex) abs < epsilon ifTrue: [^ each]].
	self roots do: [:each| each refine]] repeat"
	^ self roots argmin: [:each| (each approximation - aComplex) abs]
]

{ #category : #private }
NumericalComplexRootIsolator >> roots [
	| roots X P Q P2 Q2 n x v m c dx x1 v1 m1 realCoefficients |
	X := polynomial parent x.
	P := polynomial.
	Q := P.
	P2 := P derivative.
	Q2 := P2.
	n := P degree.
	roots := OrderedCollection new: n.
	realCoefficients := P coefficients allSatisfy: [:each| (each isKindOf: Number) or: [each imaginary isZero]].
	["Initialize root finding:"
	x := self initialValue.
	v := Q value: x.
	m := v norm2.
	"Initialize recursion:"
	c := 0. dx := v / (Q2 value: x).
	[dx abs < tolerance]
		whileFalse:
			[x1 := x - dx.
			v1 := Q value: x1.
			m1 := v1 norm2.
			m1 < m
				ifTrue: [x := x1. v := v1. m := m1. c := 0. dx := v / (Q2 value: x)]
				ifFalse: [c := c + 1. dx := dx / 4. c > 20 ifTrue: [self error: 'failed']]].
	"Polish root:"
	2 timesRepeat: [x := x - ((P value: x) / (P2 value: x))].
	"Divide:"
	((realCoefficients not or: [n = 1]) or: [x imaginary abs < tolerance "###"])
		ifTrue: "found one root"
			[x imaginary abs < tolerance ifTrue: [x := x real]. "###"
			roots add: (ComplexDisk center: x radius: tolerance).
			Q := Q // (X - x).
			Q2 := Q derivative. "###"
			n := n - 1]
		ifFalse: "found a root and (if the root is not real) also found its conjugate"
			[roots
				add: (ComplexDisk center: x radius: tolerance);
				add: (ComplexDisk center: x conjugated radius: tolerance).
			Q := Q // ((X raiseTo: 2) - (X * (x real * 2)) + x abs squared).
			Q2 := Q derivative. "###"
			n := n - 2].
	n > 0] whileTrue.
	^ roots
]

{ #category : #accessing }
NumericalComplexRootIsolator >> tolerance [
	^ tolerance
]

{ #category : #accessing }
NumericalComplexRootIsolator >> tolerance: aNumber [
	tolerance := aNumber
]
