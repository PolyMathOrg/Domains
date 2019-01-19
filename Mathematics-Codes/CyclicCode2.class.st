Class {
	#name : #CyclicCode2,
	#superclass : #LinearCode,
	#instVars : [
		'generator'
	],
	#category : #'Mathematics-Codes'
}

{ #category : #'examples-todo' }
CyclicCode2 class >> H7 [
	"Answer the Hamming code of length 7."
	^ 'self new: 7 generator: (ZZ/2) polynomials ! [:x| x^3 + x + 1]'
]

{ #category : #'instance creation' }
CyclicCode2 class >> new: n generator: aPolynomial [
	| F |
	F := aPolynomial scalars.
	^ (self new subspace: (F extension: aPolynomial) asVectorSpace) generator: aPolynomial
]

{ #category : #converting }
CyclicCode2 >> asIdeal [
	^ generator asIdeal
]

{ #category : #accessing }
CyclicCode2 >> checkPolynomial [
	| x one |
	x := generator parent x.
	one := generator parent one.
	^ 'x ^ self length - one / generator'
]

{ #category : #accessing }
CyclicCode2 >> dimension [
	^ self length - generator degree
]

{ #category : #enumerating }
CyclicCode2 >> do: aBlock [
	self asIdeal do: aBlock
]

{ #category : #operations }
CyclicCode2 >> dual [
	^ self class new: self length generator: self generator reversed
]

{ #category : #accessing }
CyclicCode2 >> generator [
	^ generator
]

{ #category : #'accessing-private' }
CyclicCode2 >> generator: aPolynomial [
	generator := aPolynomial.
"
	| n V g x |
	generator := aPolynomialResidue.
	n := generator modulus degree.
	V := generator ispecies asVectorSpaceMaxDegree: n.
	basis := LinearBasis on: V.
	g := generator.
	x := generator representative species x mod: generator modulus.
	[basis includes: g] whileFalse: [basis add: g. g := g * x].
	self subspace: basis span"
]

{ #category : #testing }
CyclicCode2 >> includes: aCodeword [
	| x |
	x := generator parent x.
	^ 'self checkPolynomial * aCodeword \\ (x ^ self length - x one) :: isZero'
]

{ #category : #testing }
CyclicCode2 >> isIrreducible [
	^ generator isIrreducible
]
