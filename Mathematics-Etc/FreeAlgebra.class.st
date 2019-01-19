"
(Associative) algebras of noncommutative polynomials in a finite set of indeterminates. Their elements are FreePolynomials.

This is the noncommutative analogue of a polynomial ring.
"
Class {
	#name : #FreeAlgebra,
	#superclass : #Ring,
	#instVars : [
		'scalars',
		'words'
	],
	#category : #'Mathematics-Etc-Algebras'
}

{ #category : #'instance creation' }
FreeAlgebra class >> new: anInteger over: aRing [
	^ self on: (1 to: anInteger) over: aRing
]

{ #category : #'instance creation' }
FreeAlgebra class >> on: aCollection over: aRing [
	^ self words: (FreeMonoid on: aCollection) over: aRing
]

{ #category : #'instance creation' }
FreeAlgebra class >> over: aRing [
	^ self new: 1 over: aRing
]

{ #category : #'instance creation' }
FreeAlgebra class >> words: aMonoid over: aRing [
	^ self new words: aMonoid; scalars: aRing
]

{ #category : #comparing }
FreeAlgebra >> = anObject [
	self == anObject ifTrue: [^ true].
	^ (anObject isKindOf: FreeAlgebra) and: [anObject scalars = scalars and: [anObject words = words]]
]

{ #category : #random }
FreeAlgebra >> atRandom: aRandom bits: bitSize [
	^ self atRandom: aRandom bits: bitSize maxDegree: ((bitSize raisedTo: (1/self rank)) min: bitSize - 1) truncated
]

{ #category : #random }
FreeAlgebra >> atRandom: aRandom bits: bitSize maxDegree: d [
	| answer n term |
	answer := self zero.
	n := 2 raisedTo: (self rank).
	n timesRepeat:
		[term := ((1 to: d) product: [:i| self x: (self rank atRandom: aRandom) to: (2 atRandom: aRandom) - 1]) * (self scalars atRandom: aRandom bits: bitSize/(self rank*d)).
		answer := answer + term].
	^ answer
]

{ #category : #elements }
FreeAlgebra >> coefficient: aNumber word: aWord [
	aNumber isZero ifTrue: [^ self zero].
	^ self coefficients: ((Dictionary new: 1) at: aWord put: aNumber; yourself)
]

{ #category : #elements }
FreeAlgebra >> coefficients: aDictionary [
	^ (FreePolynomial coefficients: aDictionary) parent: self
]

{ #category : #elements }
FreeAlgebra >> constant: aNumber [
	^ self coefficient: aNumber word: words identity
]

{ #category : #comparing }
FreeAlgebra >> hash [
	^ scalars hash + words hash hashMultiply
]

{ #category : #testing }
FreeAlgebra >> includes: anObject [
	^ (anObject isKindOf: FreePolynomial) and: [anObject parent = self]
]

{ #category : #accessing }
FreeAlgebra >> indeterminates [
	^ words symbols
]

{ #category : #testing }
FreeAlgebra >> isAssociative [
	^ true
]

{ #category : #testing }
FreeAlgebra >> isCommutative [
	^ words isCommutative and: [scalars isCommutative]
]

{ #category : #testing }
FreeAlgebra >> isFinite [
	^ words isFinite and: [scalars isFinite]
]

{ #category : #elements }
FreeAlgebra >> one [
	^ self constant: scalars one
]

{ #category : #printing }
FreeAlgebra >> printOn: aStream [
	aStream print: scalars.
	aStream nextPut: $<.
	self indeterminates
		do: [:i| aStream print: (self x: i)]
		separatedBy: [aStream nextPut: $,].
	aStream nextPut: $>
]

{ #category : #accessing }
FreeAlgebra >> rank [
	self flag: #fix. "conflicts with FreeModule|rank"
	^ self indeterminates size
]

{ #category : #accessing }
FreeAlgebra >> scalars [
	^ scalars
]

{ #category : #'accessing-private' }
FreeAlgebra >> scalars: aCommutativeRing [
	scalars := aCommutativeRing
]

{ #category : #accessing }
FreeAlgebra >> words [
	^ words
]

{ #category : #'accessing-private' }
FreeAlgebra >> words: aMonoid [
	words := aMonoid
]

{ #category : #elements }
FreeAlgebra >> x [
	^ self x: self indeterminates first
]

{ #category : #elements }
FreeAlgebra >> x: anIndeterminate [
	^ self coefficient: scalars one word: (words x: anIndeterminate)
]

{ #category : #elements }
FreeAlgebra >> x: anIndeterminate to: anInteger [
	^ self coefficient: scalars one word: (words x: anIndeterminate to: anInteger)
]

{ #category : #elements }
FreeAlgebra >> y [
	^ self x: self indeterminates second
]

{ #category : #elements }
FreeAlgebra >> z [
	^ self x: self indeterminates third
]

{ #category : #elements }
FreeAlgebra >> zero [
	^ self coefficients: (Dictionary new: 0)
]
