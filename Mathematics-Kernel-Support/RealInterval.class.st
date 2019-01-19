"
Real intervals in the real line. Each of my instances can have finite or infinite and open or closed bounds.

For some examples try this:
	RealInterval open: 1 closed: 2.
	RealInterval open: 0 open: Infinity positive.
	RealInterval closed: -1 closed: 1.
	RealInterval open: Infinity negative open: Infinity positive.

"
Class {
	#name : #RealInterval,
	#superclass : #Domain,
	#instVars : [
		'left',
		'right',
		'rightOpen',
		'leftOpen'
	],
	#category : #'Mathematics-Kernel-Support'
}

{ #category : #'instance creation' }
RealInterval class >> closed: left closed: right [
	"Answer a new [left, right] interval."

	^ self new setLeftBound: left rightBound: right leftOpen: false rightOpen: false
]

{ #category : #'instance creation' }
RealInterval class >> closed: left open: right [
	"Answer a new [left, right) interval."

	^ self new setLeftBound: left rightBound: right leftOpen: false rightOpen: true
]

{ #category : #'instance creation' }
RealInterval class >> open: left closed: right [
	"Answer a new (left, right] interval."

	^ self new setLeftBound: left rightBound: right leftOpen: true rightOpen: false
]

{ #category : #'instance creation' }
RealInterval class >> open: left open: right [
	"Answer a new (left, right) interval."

	^ self new setLeftBound: left rightBound: right leftOpen: true rightOpen: true
]

{ #category : #arithmetic }
RealInterval >> * anInterval [
	"Answer the product of the receiver by the argument."

	| l1l2 l1r2 r1l2 r1r2 |
	l1l2 := self left * anInterval left.
	l1r2 := self left * anInterval right.
	r1l2 := self right * anInterval left.
	r1r2 := self right * anInterval right.
	^ self copy
		left: ((l1l2 min: l1r2) min: (r1l2 min: r1r2));
		right: ((l1l2 max: l1r2) max: (r1l2 max: r1r2))
]

{ #category : #arithmetic }
RealInterval >> + anInterval [
	"Answer the sum of the receiver and the argument."

	^ self copy
		left: self left + anInterval left;
		right: self right + anInterval right
]

{ #category : #operations }
RealInterval >> , anInterval [
	"Answer the cartesian product of the receiver by the argument."
	| answer |
	answer := RealBox new add: self; yourself.
	anInterval do: [:each| answer add: each].
	^ answer
]

{ #category : #arithmetic }
RealInterval >> - anInterval [
	"Answer the difference of the receiver and the argument."

	^ self + anInterval negated
]

{ #category : #arithmetic }
RealInterval >> / anInterval [
	"Answer the quotient of the receiver by the argument."

	^ self * anInterval reciprocal
]

{ #category : #comparing }
RealInterval >> = anInterval [
	^ left = anInterval left and: [right = anInterval right and: [self isLeftOpen = anInterval isLeftOpen and: [self isRightOpen = anInterval isRightOpen]]]
]

{ #category : #converting }
RealInterval >> close [
	"Answer a closed inverval with the same bounds that the receiver."

	self isClosed ifFalse: [^ self copy leftOpen: false; rightOpen: false]
]

{ #category : #converting }
RealInterval >> closeLeft [
	"Answer a closed left interval with the same bounds that the receiver."

	self isLeftClosed ifFalse: [^ self copy leftOpen: false]
]

{ #category : #converting }
RealInterval >> closeRight [
	"Answer a closed right interval with the same bounds that the receiver."

	self isRightClosed ifFalse: [^ self copy rightOpen: false]
]

{ #category : #operations }
RealInterval >> closure [
	^ self class closed: left closed: right
]

{ #category : #testing }
RealInterval >> closureIncludes: anObject [
	anObject isTuple ifTrue: [^ anObject size = 1 and: [self includes: anObject first]].
	^ anObject between: left and: right
]

{ #category : #accessing }
RealInterval >> dimension [
	"Answer the dimension of the receiver."

	self isEmpty ifTrue: [^ Infinity negative].
	self left = self right ifTrue: [^ 0].
	^ 1
]

{ #category : #accessing }
RealInterval >> halves [
	| m |
	m := self midpoint.
	^ {self copy right: m; rightOpen: false . self copy left: m; leftOpen: true}
]

{ #category : #comparing }
RealInterval >> hash [
	^ self left hash hashMultiply + self right hash + self isRightOpen hash + self isLeftOpen hash hashMultiply
]

{ #category : #constants }
RealInterval >> identity [
	"Answer the identity element for the receiver."

	^ self copy left: 1; right: 1
]

{ #category : #testing }
RealInterval >> includes: anObject [
	anObject isTuple ifTrue: [^ anObject size = 1 and: [self includes: (anObject at: 1)]].
	(self left > anObject or: [self right < anObject])
		ifTrue: [^ false].
	(self left < anObject and: [self right > anObject])
		ifTrue: [^ true].
	((self isLeftClosed and: [anObject = self left])
	or: [self isRightClosed and: [anObject = self right]])
		ifTrue: [^ true].
	^ false
]

{ #category : #accessing }
RealInterval >> inf [
	"Answer the infimun of the receiver."

	^ self left
]

{ #category : #operations }
RealInterval >> interior [
	^ self class open: left open: right
]

{ #category : #testing }
RealInterval >> intersects: anInterval [
	"Answer true if the receiver overlaps the argument."
	self right < anInterval left ifTrue: [^ false].
	self left > anInterval right ifTrue: [^ false].
	self right = anInterval left ifTrue: [^ self isRightClosed and: [anInterval isLeftClosed]].
	self left = anInterval right ifTrue: [^ self isLeftClosed and: [anInterval isRightClosed]].
	^ true
]

{ #category : #testing }
RealInterval >> isBounded [
	"Answer true if the receiver is bounded."

	^ self isLeftBounded and: [self isRightBounded]
]

{ #category : #testing }
RealInterval >> isClosed [
	"Answer true if the receiver is closed."

	^ self isLeftClosed and: [self isRightClosed]
]

{ #category : #testing }
RealInterval >> isEmpty [
	"Answer true if the receiver is empty."

	^ self isLeftBounded
		ifTrue: [self right < self left]
		ifFalse: [self left > self right]
]

{ #category : #testing }
RealInterval >> isFinite [
	^ left = right and: [leftOpen not | rightOpen not]
]

{ #category : #testing }
RealInterval >> isHalfOpen [
	"Answer true if the receiver is hald-open."

	^ self isClosed not and: [self isOpen not]
]

{ #category : #testing }
RealInterval >> isLeftBounded [
	"Answer true if the receiver is left bounded."

	^ self left isInfinity not
]

{ #category : #testing }
RealInterval >> isLeftClosed [
	"Answer true if the receiver is left closed."

	^ self isLeftOpen not
]

{ #category : #testing }
RealInterval >> isLeftOpen [
	"Answer true if the receiver is left open."

	^ leftOpen
]

{ #category : #testing }
RealInterval >> isOpen [
	"Answer true if the receiver is open."

	^ self isLeftOpen and: [self isRightOpen]
]

{ #category : #testing }
RealInterval >> isRightBounded [
	"Answer true if the receiver is right bounded."

	^ self right isInfinity not
]

{ #category : #testing }
RealInterval >> isRightClosed [
	"Answer true if the receiver is right closed."

	^ self isRightOpen not
]

{ #category : #testing }
RealInterval >> isRightOpen [
	"Answer true if the receiver is open right."

	^ rightOpen
]

{ #category : #accessing }
RealInterval >> left [
	"Answer the left bound of the receiver."

	^ left
]

{ #category : #'accessing-private' }
RealInterval >> left: aNumber [
	left := aNumber
]

{ #category : #'accessing-private' }
RealInterval >> leftOpen: aBoolean [
	leftOpen := aBoolean
]

{ #category : #accessing }
RealInterval >> length [
	^ self measure
]

{ #category : #accessing }
RealInterval >> max [
	"Answer the maximum of the receiver."

	self isRightOpen ifTrue: [^ self error: 'there''s not maximum'].
	^ self right
]

{ #category : #accessing }
RealInterval >> measure [
	^ self right - self left
]

{ #category : #accessing }
RealInterval >> midpoint [
	^ left + right / 2
]

{ #category : #accessing }
RealInterval >> min [
	"Answer the minimum of the receiver."

	self isLeftOpen ifTrue: [^ self error: 'there''s not minimun'].
	^ self left
]

{ #category : #arithmetic }
RealInterval >> negated [
	"Answer the additive inverse of the receiver."

	^ self copy
		right: self left negated;
		left: self right negated;
		leftOpen: self isRightOpen;
		rightOpen: self isLeftOpen
]

{ #category : #constants }
RealInterval >> null [
	"Answer the null element for the receiver."

	^ self copy left: 0; right: 0
]

{ #category : #converting }
RealInterval >> open [
	"Answer an open inverval with the same bounds that the receiver."

	self isOpen ifFalse: [^ self copy leftOpen: true; rightOpen: true]
]

{ #category : #converting }
RealInterval >> openLeft [
	"Answer an open left interval with the same bounds that the receiver."

	self isLeftOpen ifFalse: [^ self copy leftOpen: true]
]

{ #category : #converting }
RealInterval >> openRight [
	"Answer an open right interval with the same bounds that the receiver."

	self isRightOpen ifFalse: [^ self copy rightOpen: true]
]

{ #category : #printing }
RealInterval >> printOn: aStream [
	"Print a representation of the receiver in the stream aStream."

	aStream
		nextPut: (self isLeftOpen ifTrue: [ $( ] ifFalse: [ $[ ]);
		print: self left;
		nextPutAll: ', ';
		print: self right;
		nextPut: (self isRightOpen ifTrue: [ $) ] ifFalse: [ $] ])
]

{ #category : #arithmetic }
RealInterval >> reciprocal [
	"Answer the multiplicative inverse of the receiver."
	(self closureIncludes: 0) ifTrue: [^ ZeroDivide signal].
	^ self copy
		left: self right reciprocal;
		right: self left reciprocal
]

{ #category : #accessing }
RealInterval >> right [
	"Answer the right bound of the receiver."

	^ right
]

{ #category : #'accessing-private' }
RealInterval >> right: aNumber [
	right := aNumber
]

{ #category : #'accessing-private' }
RealInterval >> rightOpen: aBoolean [
	rightOpen := aBoolean
]

{ #category : #accessing }
RealInterval >> sample [
	"Answer a sample point in the receiver."

	self isEmpty ifTrue: [^ self error: 'empty interval'].
	self isLeftClosed ifTrue: [^ self left].
	self isRightClosed ifTrue: [^ self right].
	(self isLeftBounded and: [self isRightBounded])
		ifTrue: [^ self left + self right / 2].
	self isLeftBounded ifTrue: [^ self left + 1].
	self isRightBounded ifTrue: [^ self right - 1].
	^ 0
]

{ #category : #initialization }
RealInterval >> setLeftBound: leftBound rightBound: rightBound leftOpen: leftOpenBool rightOpen: rightOpenBool [
	left := leftBound.
	right := rightBound.
	"If the interval is left-closed or right-closed and two points are
	the same, then the interval is a single point... so it's closed."
	((leftOpenBool & rightOpenBool) not and: [left = right])
		ifTrue: [leftOpen := false.
				rightOpen := false]
		ifFalse: [leftOpen := leftOpenBool.
				rightOpen := rightOpenBool]
]

{ #category : #testing }
RealInterval >> sign [
	"Answer 1 if the receiver is greater than 0, -1 if less than 0, else 0."

	self left > 0 ifTrue: [^ 1].
	self right < 0 ifTrue: [^ -1].
	^ 0
]

{ #category : #arithmetic }
RealInterval >> squared [
	^ self * self
]

{ #category : #accessing }
RealInterval >> sup [
	"Answer the supremum of the receiver."

	^ self right
]
