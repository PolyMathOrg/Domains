Class {
	#name : #AdicInteger,
	#superclass : #Number,
	#instVars : [
		'parent',
		'digits'
	],
	#category : #'Mathematics-Etc-Fields-PAdics'
}

{ #category : #'instance creation' }
AdicInteger class >> in: aPAdicIntegersRing digits: aSequence [
	^ self new parent: aPAdicIntegersRing; digits: aSequence
]

{ #category : #arithmetic }
AdicInteger >> * aPAdicInteger [
	| newDigits p q |
	p := self p.
	q := 1.
	aPAdicInteger isInteger
		ifTrue:
			[aPAdicInteger == 0 ifTrue: [^ self zero].
			newDigits := digits collect: [:each| q := q * p. each * aPAdicInteger \\ q]]
		ifFalse:
			[newDigits := digits with: aPAdicInteger digits collect: [:a :b| q := q * p. a * b \\ q]].
	^ self class in: parent digits: newDigits
]

{ #category : #arithmetic }
AdicInteger >> + aPAdicInteger [
	| newDigits p q |
	p := self p.
	q := 1.
	newDigits := digits with: aPAdicInteger digits collect: [:a :b| q := q * p. a + b \\ q].
	^ self class in: parent digits: newDigits
]

{ #category : #arithmetic }
AdicInteger >> - aPAdicInteger [
	| newDigits p q |
	p := self p.
	q := 1.
	newDigits := digits with: aPAdicInteger digits collect: [:a :b| q := q * p. a - b \\ q].
	^ self class in: parent digits: newDigits
]

{ #category : #comparing }
AdicInteger >> = aPAdicInteger [
	^ aPAdicInteger class == self class and: [digits = aPAdicInteger digits]
]

{ #category : #accessing }
AdicInteger >> at: anInteger [
	"Answer the digit corresponding to p^(anInteger-1)."
	anInteger > digits size ifTrue: [^ digits last].
	^ digits at: anInteger
]

{ #category : #'accessing-private' }
AdicInteger >> digits [
	^ digits
]

{ #category : #initialization }
AdicInteger >> digits: aSequence [
	digits := aSequence
"	| n |
	digits := ZZ tuple: anArray.
	n := (digits size to: 2 by: -1) detect: [:i| (digits at: i) representative ~= (digits at: i-1) representative] ifNone: [^ self].
	n < digits size ifTrue: [digits := digits copyFrom: 1 to: n]"
]

{ #category : #comparing }
AdicInteger >> hash [
	^ digits hash
]

{ #category : #testing }
AdicInteger >> isUniformizing [
	"Answer true if the receiver is a uniformizing element."
	^ self valuation = 1
]

{ #category : #testing }
AdicInteger >> isZero [
	^ digits isZero
]

{ #category : #arithmetic }
AdicInteger >> negated [
	| newDigits p q |
	p := self p.
	q := 1.
	newDigits := digits collect: [:a| q := q * p. a == 0 ifTrue: [a] ifFalse: [q - a]].
	^ self class in: parent digits: newDigits
]

{ #category : #accessing }
AdicInteger >> norm [
	^ self isZero ifTrue: [0] ifFalse: [(self p) raisedTo: (self valuation negated)]
]

{ #category : #constants }
AdicInteger >> one [
	^ parent one
]

{ #category : #accessing }
AdicInteger >> p [
	^ parent p
]

{ #category : #private }
AdicInteger >> parent [
	^ parent
]

{ #category : #initialization }
AdicInteger >> parent: aPAdicIntegersRing [
	parent := aPAdicIntegersRing
]

{ #category : #printing }
AdicInteger >> printOn: aStream [
	aStream nextPut: $(.
	digits do: [:each| aStream print: each] separatedBy: [aStream nextPutAll: ','].
	aStream nextPutAll: '..)'
]

{ #category : #arithmetic }
AdicInteger >> reciprocal [
	| newDigits p q |
	(digits at: 1) isZero ifTrue: [^ (ZeroDivide dividend: self one) signal].
	p := self p.
	q := 1.
	newDigits := digits collect: [:a| q := q * p. a == 1 ifTrue: [a] ifFalse: [a reciprocalModulo2: q]].
	^ self class in: parent digits: newDigits
]

{ #category : #accessing }
AdicInteger >> size [
	^ digits size
]

{ #category : #accessing }
AdicInteger >> valuation [
	self isZero ifTrue: [^ Infinity positive].
	^ (digits findFirst: [:one| one ~~ 0]) - 1
]

{ #category : #constants }
AdicInteger >> zero [
	^ parent zero
]
