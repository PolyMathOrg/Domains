"
Rings of fractions (quotients) with numerator and (nonzero) denominator in a ring. When the ring is an integral domain they form a field. See Ring>>fractions.

For example, the field of fractions of the rational integers is the rational numbers:
	ZZ fractions

The ring of fractions is a particular case of the more general construction of the localization of a ring or module.

References:
	https://en.wikipedia.org/wiki/Field_of_fractions
"
Class {
	#name : #FractionRing,
	#superclass : #LocalizationRing,
	#category : #'Mathematics-Rings'
}

{ #category : #'instance creation' }
FractionRing class >> at: anIdeal [
	^ self shouldNotImplement
]

{ #category : #examples }
FractionRing class >> example1 [
	"The field of fractions of the rational integers is the rational numbers:"
	^ ZZ fractions

]

{ #category : #'instance creation' }
FractionRing class >> on: anIntegralDomain [
	^ super at: anIntegralDomain zeroIdeal
]

{ #category : #comparing }
FractionRing >> = anObject [
	self == anObject ifTrue: [^ true].
	^ (anObject isKindOf: FractionRing) and: [anObject integers = self integers]
]

{ #category : #operations }
FractionRing >> fractions [
	^ self
]

{ #category : #testing }
FractionRing >> includes: anObject [
	| R |
	R := self integers.
	^ (R includes: anObject) or: [anObject isFractional and: [R includes: anObject numerator]]
]

{ #category : #testing }
FractionRing >> isField [
	^ self integers isIntegralDomain
]

{ #category : #testing }
FractionRing >> isFractionRing [
	^ true
]

{ #category : #converting }
FractionRing >> over: aRing [
	"Change the base ring."
	^ self class on: (self integers over: aRing)
]

{ #category : #printing }
FractionRing >> printOn: aStream [
	aStream nextPutAll: 'Frac('; print: self integers; nextPut: $)
]
