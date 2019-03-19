"
Residue class rings of Z, i.e. rings Z/mZ of residue classes of integers modulo m. Elements are instances of ModularInteger.
"
Class {
	#name : #ModularIntegerRing,
	#superclass : #QuotientRing,
	#instVars : [
		'modulus'
	],
	#category : #'Mathematics-Rings-Finite'
}

{ #category : #'instance creation' }
ModularIntegerRing class >> new: anInteger [
	^ self new modulus: anInteger
]

{ #category : #comparing }
ModularIntegerRing >> = anObject [
	self == anObject
		ifTrue: [ ^ true ].
	(anObject isKindOf: ModularIntegerRing)
		ifFalse: [ ^ false ].
	^ self modulus = anObject modulus 
]

{ #category : #random }
ModularIntegerRing >> atRandom: aRandom [
	^ self project: (self modulus atRandom: aRandom) - 1 
]

{ #category : #random }
ModularIntegerRing >> atRandom: aRandom bits: bitSize [
	^ self atRandom: aRandom 
]

{ #category : #accessing }
ModularIntegerRing >> base [
	^ ZZ 
]

{ #category : #accessing }
ModularIntegerRing >> characteristic [
	^ self modulus 
]

{ #category : #enumerating }
ModularIntegerRing >> do: aBlock [
	0 to: self modulus - 1 do: [ :i | aBlock value: (self project: i) ] 
]

{ #category : #private }
ModularIntegerRing >> elementClass [
	^ ModularInteger
]

{ #category : #comparing }
ModularIntegerRing >> hash [
	^ self modulus hash
]

{ #category : #testing }
ModularIntegerRing >> includes: anObject [
	^ anObject class = self elementClass
		and: [ anObject modulus = self modulus ]
]

{ #category : #testing }
ModularIntegerRing >> isField [
	^ self propertyAt: #isField ifAbsentPut: [ self modulus isPrime ]
]

{ #category : #testing }
ModularIntegerRing >> isFinite [
	^ true 
]

{ #category : #testing }
ModularIntegerRing >> isIntegralDomain [
	^ self isField
]

{ #category : #testing }
ModularIntegerRing >> isReduced [
	"Answer true if the receiver has no non-zero nilpotent elements, or equivalently if it has no non-zero elements with square zero, i.e. x^2 = 0 implies x = 0."

	^ modulus = 0 or: [ modulus isSquareFree ]
]

{ #category : #testing }
ModularIntegerRing >> isUnit: anElement [
	"Answer true if the argument is invertible."

	^ (anElement representative gcd: self modulus) = 1
]

{ #category : #testing }
ModularIntegerRing >> isZeroDivisor: anElement [
	"Answer true if there exists a nonzero element that multiplied by the argument is zero.
	An element in a finite ring is either a unit or a zero-divisor."

	^ (self isUnit: anElement) not
]

{ #category : #morphisms }
ModularIntegerRing >> lifting [
	"Answer the map from the receiver to the rational integers lifting the canonical projection."

	| h |
	h := modulus // 2.
	^ self
		to: self base
		evaluating: [ :f | 
			| r |
			(r := f representative) > h
				ifTrue: [ r - modulus ]
				ifFalse: [ r ] ]
]

{ #category : #accessing }
ModularIntegerRing >> modulus [
	^ modulus
]

{ #category : #'accessing-private' }
ModularIntegerRing >> modulus: anInteger [
	modulus := anInteger
]

{ #category : #private }
ModularIntegerRing >> modulusFactors [
	^ self
		propertyAt: #modulusFactors
		ifAbsentPut: [ self modulus factors ]
]

{ #category : #enumerating }
ModularIntegerRing >> primeIdealsDo: aBlock [
	| p |
	"	aBlock value: self * self zero."
	p := 2.
	[ p > modulus ]
		whileFalse: [ p | modulus
				ifTrue: [ aBlock value: self * (self project: p) ].
							p := p nextPrime ]
]

{ #category : #printing }
ModularIntegerRing >> printOn: aStream [
	aStream
		print: self base;
		nextPut: $/;
		print: self modulus;
		print: self base 
]

{ #category : #morphisms }
ModularIntegerRing >> project: anInteger [
	^ self representative: anInteger \\ modulus 
]

{ #category : #accessing }
ModularIntegerRing >> relations [
	^ self propertyAt: #relations ifAbsentPut: [ ZZ * modulus ]
]

{ #category : #'accessing-private' }
ModularIntegerRing >> relations: anIdeal [
	super relations: anIdeal.
	self modulus: anIdeal generator
]

{ #category : #accessing }
ModularIntegerRing >> size [
	^ self modulus
]

{ #category : #tuples }
ModularIntegerRing >> tuple: anArray [
	^ self modulus = 2 ifTrue: [BitTuple coefficients: anArray] ifFalse: [ModularTuple coefficients: anArray over: self]
]

{ #category : #tuples }
ModularIntegerRing >> tuple: anInteger evaluating: aBlock [
	| modulus |
	modulus := self modulus.
	modulus = 2 ifTrue: [^ BitTuple new: anInteger evaluating: aBlock].
	^ ModularTuple new: anInteger over: self evaluating: aBlock
]

{ #category : #tuples }
ModularIntegerRing >> tupleClass [
	^ self modulus = 2
		ifTrue: [ ^ BitTuple ]
		ifFalse: [ ModularTuple ] 
]

{ #category : #operations }
ModularIntegerRing >> units [
	"Answer the multiplicative group of units of the receiver (i.e., elements that have multiplicative inverse)."

	^ ModularIntegersUnitGroup on: self 
]
