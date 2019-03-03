"
Ideals of integers. They are cyclic, i.e. they are all multiples of a given integer (the #generator).
"
Class {
	#name : #RationalIntegerIdeal,
	#superclass : #Ideal,
	#category : #'Mathematics-Rings'
}

{ #category : #random }
RationalIntegerIdeal >> atRandom: aRandom bits: bitSize [
	^ ((0-bitSize//2 to: bitSize//2) atRandom: aRandom) * self generator
]

{ #category : #operations }
RationalIntegerIdeal >> dot: anIdeal [ "ï "
	"Answer the intersection of the receiver and the argument."
	^ self scalars * (self generator lcm: anIdeal generator)
]

{ #category : #'operations-elements' }
RationalIntegerIdeal >> inverseOf: anInteger [
	| result |
	result := anInteger xgcd: self generator.
	^ (result at: 1) = 1 ifTrue: [result at: 2]
]

{ #category : #testing }
RationalIntegerIdeal >> isMaximal [
	^ self isZero not and: [self isPrime]
]

{ #category : #testing }
RationalIntegerIdeal >> isPrimary [
	^ self propertyAt: #isPrimary ifAbsentPut:[self isZero or: [self generator factors asSet size = 1]]
]

{ #category : #testing }
RationalIntegerIdeal >> isPrime [
	^ self propertyAt: #isPrime ifAbsentPut:[self isZero or: [self generator isPrime]]
]

{ #category : #testing }
RationalIntegerIdeal >> isSemiprime [
	^ self propertyAt: #isSemiprime ifAbsentPut:[self isZero or: [self generator isSquareFree]]
]

{ #category : #printing }
RationalIntegerIdeal >> printOn: aStream [
	self isZero ifTrue: [aStream nextPutAll: '{0}'. ^ self].
	aStream print: self generator; nextPut: $ℤ
]

{ #category : #operations }
RationalIntegerIdeal >> quotientRing [
	"Answer the quotient ring of the base ring by the receiver."
	^ ModularIntegerRing mod: self
]

{ #category : #operations }
RationalIntegerIdeal >> radical [
	^ self scalars * self generator radical
]

{ #category : #random }
RationalIntegerIdeal >> remainderAtRandom: aRandom [
	^ (self generator abs atRandom: aRandom) - 1
]
