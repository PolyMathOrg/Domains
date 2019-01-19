"
My instances represent dyadic fractions, i.e. fractions of the form a / 2^n where a is integer and n is >= 0.

Example:
	(DyadicFraction numerator: 5 shift: 3) + (DyadicFraction numerator: 3 shift: 2)

"
Class {
	#name : #DyadicFraction,
	#superclass : #Number,
	#instVars : [
		'numerator',
		'shift'
	],
	#category : #'Mathematics-Etc'
}

{ #category : #'instance creation' }
DyadicFraction class >> fromFraction: aFraction [
	^ self numerator: aFraction numerator shift: aFraction denominator highBit - 1
]

{ #category : #'instance creation' }
DyadicFraction class >> fromInteger: anInteger [
	anInteger isInteger ifFalse: [DomainError signal].
	^ self numerator: anInteger shift: 0
]

{ #category : #'instance creation' }
DyadicFraction class >> numerator: anInteger shift: n [
	^ self new setNumerator: anInteger shift: n
]

{ #category : #arithmetic }
DyadicFraction >> * aDyadicFraction [
	aDyadicFraction isInteger ifTrue: [^ self class numerator: numerator * aDyadicFraction shift: shift].
	^ self class
		numerator: numerator * aDyadicFraction numerator
		shift: shift + aDyadicFraction shift
]

{ #category : #arithmetic }
DyadicFraction >> + aDyadicFraction [
	^ self shift <= aDyadicFraction shift
		ifTrue:
			[self class
				numerator: (numerator bitShift: aDyadicFraction shift - shift) + aDyadicFraction numerator
				shift: aDyadicFraction shift]
		ifFalse:
			[self class
				numerator: (aDyadicFraction numerator bitShift: shift - aDyadicFraction shift) + numerator
				shift: shift]
]

{ #category : #arithmetic }
DyadicFraction >> - aNumber [
	^ self + aNumber negated
]

{ #category : #arithmetic }
DyadicFraction >> / anInteger [
	| n |
	n := anInteger abs.
	n isPowerOfTwo ifFalse: [DomainError signal: 'only can divide by a power of 2'].
	^ self class
		numerator: (anInteger positive ifTrue: [numerator] ifFalse: [numerator negated])
		shift: shift + n highBit - 1
]

{ #category : #comparing }
DyadicFraction >> < aDyadicFraction [
	"Answer whether the receiver is less than the argument."
	self sign ~= aDyadicFraction sign ifTrue: [^ self sign < aDyadicFraction sign].
	shift = aDyadicFraction shift ifTrue: [^ numerator < aDyadicFraction numerator].
"	numerator = aDyadicFraction numerator ifTrue: [^ numerator positive and: [shift > aDyadicFraction shift]]."
	^ (numerator bitShift: aDyadicFraction shift) < (aDyadicFraction numerator bitShift: shift)
]

{ #category : #comparing }
DyadicFraction >> = aDyadicFraction [
	^ numerator = aDyadicFraction numerator and: [shift = aDyadicFraction shift]
]

{ #category : #converting }
DyadicFraction >> asFloat [
	^ self asFraction asFloat
]

{ #category : #converting }
DyadicFraction >> asFraction [
	^ Fraction numerator: self numerator denominator: self denominator
]

{ #category : #private }
DyadicFraction >> denominator [
	^ 1 bitShift: shift
]

{ #category : #comparing }
DyadicFraction >> hash [
	^ numerator hashMultiply + shift
]

{ #category : #testing }
DyadicFraction >> isZero [
	^ numerator isZero
]

{ #category : #arithmetic }
DyadicFraction >> negated [
	^ self class numerator: numerator negated shift: shift
]

{ #category : #private }
DyadicFraction >> normalize [
	[numerator even and: [shift > 0]]
		whileTrue:
			[numerator := numerator bitShift: -1.
			shift := shift - 1]
]

{ #category : #private }
DyadicFraction >> numerator [
	^ numerator
]

{ #category : #constants }
DyadicFraction >> one [
	^ self class numerator: 1 shift: 0
]

{ #category : #printing }
DyadicFraction >> printOn: aStream base: base [
	aStream nextPut: $(.
	numerator printOn: aStream base: base.
	aStream nextPutAll: '/2^'; print: shift; nextPut: $)
]

{ #category : #'mathematical functions' }
DyadicFraction >> raisedToInteger: anInteger [
	anInteger < 0 ifTrue: [^ self reciprocal raisedToInteger: anInteger negated].
	anInteger = 0 ifTrue: [^ self one].
	^ self class numerator: (numerator raisedToInteger: anInteger) shift: shift + anInteger
]

{ #category : #private }
DyadicFraction >> setNumerator: a shift: n [
	numerator := a asInteger.
	shift := n asInteger.
	self normalize
]

{ #category : #private }
DyadicFraction >> shift [
	^ shift
]

{ #category : #testing }
DyadicFraction >> sign [
	^ numerator sign
]

{ #category : #constants }
DyadicFraction >> zero [
	^ self class numerator: 0 shift: 0
]
