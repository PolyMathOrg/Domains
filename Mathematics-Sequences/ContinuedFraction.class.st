"
Finite or infinite continued fractions.

The finite case correspondes to rational numbers, for example:
  36/17 as: ContinuedFraction

But continued fractions can be infinite:
  ContinuedFraction e

Given a Float, and assuming the number is actually rational, its continued fraction expansion can be used to guess the rational number by truncating it when the convergents start to get too big (in bitsize terms), or when the coefficients of the continued fraction get too big:
  2.117647 as: ContinuedFraction :: convergents

"
Class {
	#name : #ContinuedFraction,
	#superclass : #Number,
	#instVars : [
		'coefficients'
	],
	#category : #'Mathematics-Sequences'
}

{ #category : #'instance creation' }
ContinuedFraction class >> coefficients: anArray [
	^ self new coefficients: anArray
]

{ #category : #examples }
ContinuedFraction class >> e [
	^ self coefficients: (Sequence evaluating: [:n| n=1 ifTrue: [2] ifFalse: [n \\ 3 = 0 ifTrue: [2*n/3] ifFalse: [1]]])
]

{ #category : #'instance creation' }
ContinuedFraction class >> fromFloat: aFloat [
	^ self fromFraction: aFloat asFraction
]

{ #category : #'instance creation' }
ContinuedFraction class >> fromFraction: aFraction [
	^ self new fromFraction: aFraction
]

{ #category : #'instance creation' }
ContinuedFraction class >> newFrom: aNumber [
	aNumber isFloat ifTrue: [^ self fromFloat: aNumber].
	aNumber isFraction ifTrue: [^ self fromFraction: aNumber].
	^ super newFrom: aNumber
]

{ #category : #examples }
ContinuedFraction class >> phi [
	"Answer the golden ratio."
	^ self coefficients: (Sequence constant: 1)
]

{ #category : #converting }
ContinuedFraction >> asFraction [
	self isInfinite ifTrue: [self error: 'infinite continued fraction'].
	^ self convergentAt: coefficients size
]

{ #category : #accessing }
ContinuedFraction >> coefficients [
	^ coefficients
]

{ #category : #initialization }
ContinuedFraction >> coefficients: aSequence [
	coefficients := ((aSequence isKindOf: Tuple) or: [aSequence isKindOf: Sequence])
		ifTrue: [aSequence]
		ifFalse: [ZZ tuple: aSequence]
]

{ #category : #convergents }
ContinuedFraction >> convergentAt: anInteger [
	| n x |
	coefficients size > 0 ifFalse: [^ Infinity positive].
	n := coefficients size min: anInteger.
	x := coefficients at: n.
	(1 to: n-1) reverseDo: [:i| x := x reciprocal + (coefficients at: i)].
	^ x
]

{ #category : #convergents }
ContinuedFraction >> convergents [
	^ Sequence to: QQ evaluating: [:i| self convergentAt: i]
]

{ #category : #convergents }
ContinuedFraction >> convergentsDo: aBlock [
	| p1 p2 q1 q2 |
	p2 := 0.
	p1 := 1.
	q2 := 1.
	q1 := 0.
	coefficients withIndexDo: [:ai :i| | pi qi | pi := ai*p1 + p2. qi := ai*q1 + q2. aBlock value: pi/qi. p2 := p1. p1 := pi. q2 := q1. q1 := qi]
]

{ #category : #convergents }
ContinuedFraction >> convergentsUpTo: n [
	| answer |
	answer := OrderedCollection new: n.
	self convergentsDo: [:each| answer size < n ifFalse: [^ answer]. answer add: each]
]

{ #category : #initialization }
ContinuedFraction >> fromFraction: aFraction [
	| x a |
	aFraction isInfinity ifTrue: [coefficients := ZZ tuple: 0 evaluating: []. ^ self].
	coefficients := OrderedCollection new.
	x := aFraction.
	a := x floor.
	coefficients add: a.
	[x := x - a.
	x ~= 0]
		whileTrue:
			[x := x reciprocal.
			a := x floor.
			coefficients add: a].
	coefficients := ZZ tuple: coefficients asArray
]

{ #category : #testing }
ContinuedFraction >> isFinite [
	^ coefficients size isInfinite not
]

{ #category : #testing }
ContinuedFraction >> isInfinite [
	^ self isFinite not
]

{ #category : #arithmetic }
ContinuedFraction >> negated [
	^ self class coefficients: coefficients negated
]

{ #category : #printing }
ContinuedFraction >> printOn: aStream base: base [
	| separator |
	aStream nextPut: $[.
	separator := $;.
	(1 to: (coefficients size min: 10)) do: [:i| (coefficients at: i) printOn: aStream base: base] separatedBy: [aStream nextPut: separator. separator := $,].
	coefficients size isInfinite ifTrue: [aStream nextPutAll: '...'].
	aStream nextPut: $]
]

{ #category : #arithmetic }
ContinuedFraction >> reciprocal [
	^ (coefficients at: 1) = 0
		ifTrue: [self class coefficients: (coefficients copyFrom: 2 to: coefficients size)]
		ifFalse: [self class coefficients: 0, coefficients]
]
