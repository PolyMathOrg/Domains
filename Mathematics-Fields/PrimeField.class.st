"
Residue class fields Z/pZ of integers modulo a prime p.

These are the simplest examples of Galois fields, GF(p^1). Other Galois fields are constructed by finite algebraic extensions (see GaloisField).
"
Class {
	#name : #PrimeField,
	#superclass : #PrimeRing,
	#category : #'Mathematics-Fields-Finite'
}

{ #category : #private }
PrimeField >> computePrimitiveRoot [
	| a order primeFactors |
	modulus = 2 ifTrue: [^ self one].
	order := modulus - 1.
	primeFactors := order factors asSet.
	a := 2.
	[primeFactors anySatisfy: [:pi| (a raisedTo: order / pi modulo: modulus) = 1]]
		whileTrue:
			[a := a + 1.
			a >= modulus ifTrue: [self error: 'no primitive element, the modulus is not prime']].
	^ self representative: a
]

{ #category : #operations }
PrimeField >> extension: aPolynomial [
	"Answer the Galois overfield of the receiver defined by the given irreducible polynomial."
	aPolynomial scalars = self ifFalse: [DomainError signal: 'polynomial coefficients not from this field'].
	aPolynomial parent isUnivariate ifFalse: [DomainError signal: 'not univariate poylnomial'].
	^ GaloisField polynomial: aPolynomial
]

{ #category : #morphisms }
PrimeField >> inverseOf: anElement [
	^ self representative: ((self inverseOfRepresentative: anElement representative) ifNil: [^ nil])
]

{ #category : #private }
PrimeField >> inverseOfRepresentative: anInteger [
	| result |
	anInteger == 0 ifTrue: [^ nil].
	anInteger == 1 ifTrue: [^ 1].
	result := anInteger xgcd: modulus.
	^ (result at: 2) \\ modulus
]

{ #category : #testing }
PrimeField >> isField [
	^ true
]

{ #category : #testing }
PrimeField >> isGaloisField [
	^ true
]

{ #category : #testing }
PrimeField >> isUnit: anElement [
	"Answer true if the argument is invertible."
	^ anElement isZero not
]

{ #category : #testing }
PrimeField >> isZeroDivisor: anElement [
	"Answer true if there exists a nonzero element that multiplied by the argument is zero."
	^ anElement isZero
]

{ #category : #'accessing-private' }
PrimeField >> p: aPrime to: anInteger [
	anInteger = 1 ifFalse: [^ self error: 'exponent must be 1'].
	super p: aPrime to: anInteger
]

{ #category : #enumerating }
PrimeField >> primeIdealsDo: aBlock [
	aBlock value: self zeroIdeal
]

{ #category : #accessing }
PrimeField >> primeSubfield [
	^ self
]

{ #category : #accessing }
PrimeField >> primitiveRoot [
	"When the receiver is a field Z/<p>, answer a primitive root modulo p."
	^ self propertyAt: #primitiveRoot ifAbsentPut: [self computePrimitiveRoot]
]

{ #category : #printing }
PrimeField >> printOn: aStream [
	aStream nextPutAll: 'FF'; nextPutAll: self modulus printString sub
]

{ #category : #morphisms }
PrimeField >> squareRootOf: anElement [
	^ self representative: ((self squareRootOfRepresentative: anElement representative) ifNil: [^ nil])
]

{ #category : #private }
PrimeField >> squareRootOfRepresentative: anInteger [
	| algorithm |
	algorithm := self propertyAt: #squareRootAlgorithm ifAbsentPut: [TonelliShanks new modulus: self modulus].
	^ algorithm squareRootOf: anInteger
]

{ #category : #operations }
PrimeField >> zeroDivisors [
	^ {self zero}
]

{ #category : #comparing }
PrimeField >> ~ aRing [
	"Any two finite fields of the same cardinality are isomorphic."
	^ aRing isField and: [self size = aRing size]
]
