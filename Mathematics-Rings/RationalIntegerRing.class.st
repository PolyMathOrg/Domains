"
The singletion global instance ZZ is the ring of rational integers.
"
Class {
	#name : #RationalIntegerRing,
	#superclass : #Ring,
	#category : #'Mathematics-Rings'
}

{ #category : #'class initialization' }
RationalIntegerRing class >> initialize [
	Smalltalk at: #ZZ put: self new
]

{ #category : #elements }
RationalIntegerRing >> ! anObject [
	anObject isInteger ifTrue: [^ anObject].
	^ super ! anObject
]

{ #category : #operations }
RationalIntegerRing >> % anInteger [
	anInteger isPrime ifTrue: [^ PrimeField new: anInteger].
	^ ModularIntegerRing new: anInteger
]

{ #category : #operations }
RationalIntegerRing >> / anInteger [
	| factors |
	anInteger isInteger ifFalse: [^ super / anInteger].
	factors := anInteger factors.
	factors asSet size = 1 ifTrue:
		[^ PrimeRing new: factors anyOne to: factors size].
	^ ModularIntegerRing new: anInteger
]

{ #category : #comparing }
RationalIntegerRing >> <= aDomain [
	^ aDomain isRing and: [(aDomain includes: 1) and: [aDomain includes: 0]]
]

{ #category : #comparing }
RationalIntegerRing >> = anObject [
	^ anObject class == self class
]

{ #category : #operations }
RationalIntegerRing >> adic: aPrime [
	^ AdicIntegerRing p: aPrime
]

{ #category : #random }
RationalIntegerRing >> atRandom: aRandom bits: bitSize [
	| n |
	bitSize isInfinite ifTrue: [^ self error: 'infinite bitsize'].
	bitSize < 0 ifTrue: [^ self error: 'negative bitsize'].
	self flag: #fix. "maybe this should be more like a flat gaussian distribution around 0?"
	bitSize < 1 ifTrue: [^ 0].
	n := 2 raisedTo:(bitSize truncated - 1).
	^ (0-n to: n) atRandom: aRandom
]

{ #category : #accessing }
RationalIntegerRing >> characteristic [
	^ 0
]

{ #category : #accessing }
RationalIntegerRing >> dimension [
	"Answer the Krull dimension of the receiver."
	^ 1
]

{ #category : #enumerating }
RationalIntegerRing >> do: aBlock [
	| i |
	aBlock value: 0.
	i := 1.
	[ aBlock value: i; value: i negated. i := i + 1 ] repeat
]

{ #category : #operations }
RationalIntegerRing >> fractions [
	^ QQ
]

{ #category : #comparing }
RationalIntegerRing >> hash [
	^ self class hash
]

{ #category : #private }
RationalIntegerRing >> idealClass [
	^ RationalIntegerIdeal
]

{ #category : #testing }
RationalIntegerRing >> includes: anObject [
	^ anObject isInteger
]

{ #category : #testing }
RationalIntegerRing >> isDedekindDomain [
	"A Dedekind domain is an integral domain in which every non-zero proper ideal factors into a product of prime ideals."
	^ true
]

{ #category : #testing }
RationalIntegerRing >> isEuclidean [
	^ true
]

{ #category : #testing }
RationalIntegerRing >> isFinite [
	^ false
]

{ #category : #testing }
RationalIntegerRing >> isInitial [
	^ true
]

{ #category : #testing }
RationalIntegerRing >> isIntegralDomain [
	^ true
]

{ #category : #testing }
RationalIntegerRing >> isIrreducible: anInteger [
	^ anInteger isPrime
]

{ #category : #testing }
RationalIntegerRing >> isNoetherian [
	^ true
]

{ #category : #testing }
RationalIntegerRing >> isReal [
	^ true
]

{ #category : #testing }
RationalIntegerRing >> isReduced [
	"Answer true if the receiver has no non-zero nilpotent elements, or equivalently if it has no non-zero elements with square zero, i.e. x^2 = 0 implies x = 0."
	^ true
]

{ #category : #testing }
RationalIntegerRing >> isUnit: anInteger [
	"Answer true if the argument is invertible."
	^ anInteger = 1 or: [anInteger = -1]
]

{ #category : #testing }
RationalIntegerRing >> isZeroDivisor: anElement [
	"Answer true if there exists a nonzero element that multiplied by the argument is zero."
	^ anElement = 0
]

{ #category : #elements }
RationalIntegerRing >> one [
	^ 1
]

{ #category : #enumerating }
RationalIntegerRing >> primeIdealsDo: aBlock [
	| p |
	p := 0.
	[aBlock value: self * p.
	p := p nextPrime] repeat
]

{ #category : #printing }
RationalIntegerRing >> printOn: aStream [
	aStream nextPutAll: 'ℤ'
]

{ #category : #operations }
RationalIntegerRing >> radical [
	"Answer the Jacobson radical J(R) of the receiver R. This is the ideal consisting of all elements that annihilate all simple R-modules. It is the intersection of all maximal ideals."
	^ self zeroIdeal
]

{ #category : #accessing }
RationalIntegerRing >> size [
	^ Aleph new
]

{ #category : #morphisms }
RationalIntegerRing >> to: aCodomain [
	"Answer the canonical morphism from the receiver to aCodomain."
	aCodomain isRing
		ifTrue: [^ self to: aCodomain evaluating: [:x| aCodomain one * x]].
	^ super to: aCodomain
]

{ #category : #operations }
RationalIntegerRing >> units [
	"Answer the multiplicative group of units of the receiver (i.e., elements that have multiplicative inverse)."
	^ super units elements: {1. -1}
]

{ #category : #enumerating }
RationalIntegerRing >> unitsDo: aBlock [
	aBlock value: 1; value: -1
]

{ #category : #accessing }
RationalIntegerRing >> valuation [
	"Answer the Euclidean function of the receiver."
	^ Function from: self to: self evaluating: [:x| x abs]
]

{ #category : #elements }
RationalIntegerRing >> zero [
	^ 0
]

{ #category : #operations }
RationalIntegerRing >> zeroDivisors [
	^ #(0)
]
