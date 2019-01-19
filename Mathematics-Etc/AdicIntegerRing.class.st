"
Rings of p-adic integers Zp. See AdicInteger.
"
Class {
	#name : #AdicIntegerRing,
	#superclass : #Ring,
	#instVars : [
		'p'
	],
	#category : #'Mathematics-Etc-Fields-PAdics'
}

{ #category : #'instance creation' }
AdicIntegerRing class >> p: aPrime [
	^ self new p: aPrime
]

{ #category : #accessing }
AdicIntegerRing >> characteristic [
	^ 0
]

{ #category : #elements }
AdicIntegerRing >> digits: aSequence [
	^ AdicInteger in: self digits: aSequence
]

{ #category : #morphisms }
AdicIntegerRing >> embed: aNumber [
	| q digits max |
	aNumber isFraction ifTrue: [^ (self embed: aNumber numerator) / (self embed: aNumber denominator)].
	aNumber isInteger ifFalse: [^ DomainError signal: 'not a rational number'].
	q := 1.
	max := aNumber abs.
	digits := OrderedCollection new.
	[q := q * p.
	digits add: aNumber \\ q.
	q > max ifTrue: [^ self digits: digits asArray]] repeat
]

{ #category : #accessing }
AdicIntegerRing >> fractions [
	^ AdicField p: p
]

{ #category : #testing }
AdicIntegerRing >> isIntegralDomain [
	^ true
]

{ #category : #accessing }
AdicIntegerRing >> one [
	^ self embed: 1
]

{ #category : #accessing }
AdicIntegerRing >> p [
	^ p
]

{ #category : #initialization }
AdicIntegerRing >> p: aPrime [
	p := aPrime
]

{ #category : #printing }
AdicIntegerRing >> printOn: aStream [
	aStream print: ZZ; nextPutAll: p printString sub
]

{ #category : #accessing }
AdicIntegerRing >> zero [
	^ self embed: 0
]
