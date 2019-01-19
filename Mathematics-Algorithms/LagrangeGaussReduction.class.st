"
This is the Lagrange-Gauss reduction algorithm. My instances perform reduction of lattice basis of rank 2, and the algorithm it is essentially Euclid's algorithm.

Input: a vector space V and two independent vectors {v1,v2} that generate a lattice;
Output: a short vector in the lattice.

"
Class {
	#name : #LagrangeGaussReduction,
	#superclass : #Object,
	#instVars : [
		'vectorSpace',
		'v1',
		'v2',
		'shortVector'
	],
	#category : #'Mathematics-Algorithms'
}

{ #category : #'as yet unclassified' }
LagrangeGaussReduction >> computeShortVector [
	| innerProduct a b A B t T n r |
	innerProduct := vectorSpace innerProduct. "Euclidean inner product"

	"Initialization:"
	a := v1. b := v2.
	A := innerProduct value: {a. a}.
	B := innerProduct value: {b. b}.
	A < B ifTrue: [b := v1. a := v2. t := A. A := B. B := t].
	
	["Euclidean step:"
	n := innerProduct value: {a. b}.
	r := (n/B) rounded. "nearest integer"
	T := A - (2*r*n) + (r*r*B).
	T >= B]
		whileFalse:
			[t := a - (r*b).
			a := b.
			b := t.
			A := B.
			B := T].
	
	shortVector := b
]

{ #category : #'as yet unclassified' }
LagrangeGaussReduction >> shortVector [
	shortVector isNil ifTrue: [self computeShortVector].
	^ shortVector
]
