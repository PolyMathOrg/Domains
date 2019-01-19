"
Homomorphisms of polynomial rings.
"
Class {
	#name : #PolynomialRingMap,
	#superclass : #RingMap,
	#category : #'Mathematics-Polynomials'
}

{ #category : #'as yet unclassified' }
PolynomialRingMap >> imageContains: aPolynomial [
	"As in Magma, algorithm in p. 82 of [AL94]."
	self notYetImplemented
]

{ #category : #'as yet unclassified' }
PolynomialRingMap >> implicitization [
	"As implemented in RationalMap. Maybe shouldn't implement it here.
	Magma uses the algorithm in p. 97 of [CLO96]."
	self notYetImplemented
]

{ #category : #testing }
PolynomialRingMap >> isSurjective [
	^ self codomain generators allSatisfy: [:each| self imageContains: each]
]

{ #category : #operations }
PolynomialRingMap >> kernel [
	"See RationalMap>>image."
	| A B m n P t embedding generators I |
	self propertyAt: #kernel ifPresent: [:anIdeal| ^ anIdeal].
	A := self domain.
	B := self codomain.
	n := A rank.
	m := B rank.
	P := self codomain scalars polynomialsIn: n + m + 1.
	"the embedding mapping the i-th indeterminate to the (i+n)-th indeterminate in the bigger ring:"
	embedding := A to: P evaluating: [:f| P ! f substitute: [:i| i+n]].
	t := P x: P rank.
	generators := OrderedCollection new.
	1 to: n do: [:i|
		generators add: (P x: i) - (embedding value: (self value: (A x: i)))].
	generators add: P one - t.
	I := P * generators eliminateAll: (n+1 to: P rank).
	^ self propertyAt: #kernel put: A * (I generators collect: [:each| A ! each])
]

{ #category : #printing }
PolynomialRingMap >> printOn: aStream [
"	self isIdentity ifTrue: [aStream nextPutAll: 'id'. ^ self].
	self negated isIdentity ifTrue: [aStream nextPutAll: '-id'. ^ self].
	self isZero ifTrue: [aStream nextPut: $0. ^ self].
"	aStream nextPut: $(.
	(1 to: self domain rank)
		do: [:i| aStream print: (self value: (self domain x: i))]
		separatedBy: [aStream nextPutAll: ', '].
	aStream nextPut: $)
]

{ #category : #operations }
PolynomialRingMap >> spec [
	"This is the Spec functor. Answer the affine scheme homomorphism induced by the receiver, i.e. given a ring homomorphism f:R->S, Spec(f) is a scheme homomorphism Spec(S)->Spec(R)."
	^ self codomain spec to: self domain spec representatives: ((1 to: self domain rank) collect: [:i| self value: (self domain x: i)])
]
