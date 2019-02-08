"
Elements of the form a / b, with a and b in a commutative ring R, and satisfying the equivalence relation: (a / b) = (a' / b') iff a*b' = a'*b.

They are elements of ring localizations or fraction fields. See LocalizationRing and FractionRing.
"
Class {
	#name : #FormalFraction,
	#superclass : #Object,
	#instVars : [
		'numerator',
		'denominator'
	],
	#category : #'Mathematics-Rings'
}

{ #category : #'instance creation' }
FormalFraction class >> numerator: anObject denominator: anotherObject [
	| numerator denominator gcd |
	(numerator := anObject) isZero
		ifTrue: [ ^ numerator ]. 
	denominator := anotherObject.
	gcd := numerator gcd: denominator.
	numerator := numerator /// gcd.
	denominator := denominator /// gcd.
	denominator = denominator one
		ifTrue: [ ^ numerator ].
	^ self reducedNumerator: numerator denominator: denominator
]

{ #category : #'instance creation' }
FormalFraction class >> reducedNumerator: anObject denominator: anotherObject [
	^ self new setNumerator: anObject denominator: anotherObject 
]

{ #category : #arithmetic }
FormalFraction >> * anObject [
	anObject class == self class
		ifTrue: [^ self class numerator: numerator * anObject numerator denominator: denominator * anObject denominator].
	^ self class numerator: numerator * anObject denominator: denominator
]

{ #category : #arithmetic }
FormalFraction >> + anObject [
	anObject class == self class
		ifTrue: [^ self class
			numerator: numerator * anObject denominator + (denominator * anObject numerator)
			denominator: denominator * anObject denominator].
	^ self class numerator: numerator + (denominator * anObject) denominator: denominator
]

{ #category : #arithmetic }
FormalFraction >> - anObject [
	^ self + anObject negated
]

{ #category : #arithmetic }
FormalFraction >> / anObject [
	^ self * anObject reciprocal
]

{ #category : #comparing }
FormalFraction >> = anObject [
	^ anObject class == self class and: [numerator * anObject denominator = (denominator * anObject numerator)] "this is wrong unless the units don't contain any zerodivisor, for example localizations of integral domains"
]

{ #category : #accessing }
FormalFraction >> bitSize [
	^ numerator bitSize + denominator bitSize
]

{ #category : #accessing }
FormalFraction >> denominator [
	^ denominator
]

{ #category : #comparing }
FormalFraction >> hash [
	^ 0
]

{ #category : #testing }
FormalFraction >> isFractional [
	"Answer true if this is an element of a localization, i.e. if it is some kind of fraction and understands #numerator and #denominator."

	^ true
]

{ #category : #testing }
FormalFraction >> isZero [
	^ numerator isZero
]

{ #category : #accessing }
FormalFraction >> lift [
	^ self numerator lift / self denominator lift
]

{ #category : #arithmetic }
FormalFraction >> negated [ 
	^ self class
		numerator: numerator negated
		denominator: denominator
]

{ #category : #accessing }
FormalFraction >> numerator [
	^ numerator
]

{ #category : #constants }
FormalFraction >> one [
	^ self class numerator: numerator one denominator: denominator one 
]

{ #category : #printing }
FormalFraction >> printOn: aStream [
	| string |
	denominator = denominator one
		ifTrue: [ aStream print: numerator.
			^ self ].
	aStream
		print: numerator;
		nextPutAll: ' / '. 
	string := denominator printString.
	((string includes: $+) or: [ string includes: $- ])
		ifTrue: [ aStream
				nextPut: $(;
				print: denominator;
				nextPut: $) ]
		ifFalse: [ aStream print: denominator ]
]

{ #category : #arithmetic }
FormalFraction >> raisedTo: anInteger [
	"^ "
	
	anInteger = 1
		ifTrue: [ ^ self ].
	anInteger < 0
		ifTrue: [ ^ self reciprocal raisedTo: anInteger negated ].
	^ self class
		numerator: (numerator raisedTo: anInteger)
		denominator: (denominator raisedTo: anInteger)
]

{ #category : #arithmetic }
FormalFraction >> reciprocal [
	^ self class numerator: denominator denominator: numerator
]

{ #category : #accessing }
FormalFraction >> representative [
	^ self numerator representative / self denominator representative
]

{ #category : #private }
FormalFraction >> setNumerator: anObject denominator: anotherObject [
	numerator := anObject.
	denominator := anotherObject
]

{ #category : #arithmetic }
FormalFraction >> squared [
	^ self class
		numerator: numerator squared
		denominator: denominator squared
]

{ #category : #constants }
FormalFraction >> zero [
	^ self class numerator: numerator zero denominator: denominator one
]
