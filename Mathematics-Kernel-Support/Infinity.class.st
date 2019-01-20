"
The real +infinity or -infinity.

For some examples try these:
	Infinity positive * Infinity negative.
	Infinity positive * 2.
	Infinity positive - 7811234871239847.
	Infinity negative / -199.
	Infinity positive reciprocal.
	Infinity positive > Infinity negative.
	Infinity negative < -19238479182374598172349871234.
	Infinity negative > 0.
	Infinity negative min: Infinity positive.

The following are examples of undeterminations (they produce an error):
	Infinity positive + Infinity negative.
	Infinity positive * 0.
	Infinity positive / Infinity positive.
	Infinity positive raisedToInteger: 0.

"
Class {
	#name : #Infinity,
	#superclass : #Magnitude,
	#instVars : [
		'sign'
	],
	#category : #'Mathematics-Kernel-Support'
}

{ #category : #'instance creation' }
Infinity class >> negative [
	"Answer a new instance of the receiver representing -infinity."

	^ self sign: -1
]

{ #category : #'instance creation' }
Infinity class >> positive [
	"Answer a new instance of the receiver representing +infinity."

	^ self sign: 1
]

{ #category : #'instance creation' }
Infinity class >> projective [
	"Answer a new instance of the receiver representing the projective (unsigned) infinity."

	^ self sign: 0
]

{ #category : #'instance creation' }
Infinity class >> sign: anInteger [
	"Answer a new instance of the receiver with sign anInteger."

	^ self new sign: anInteger
]

{ #category : #arithmetic }
Infinity >> * anObject [
	"Answer the product of the receiver by the argument."

	anObject = 0 ifTrue: [^ self errorUndetermined].
	^ self class sign: self sign * anObject sign
]

{ #category : #arithmetic }
Infinity >> + anObject [
	"Answer the sum of the receiver and the argument."

	(anObject isInfinity and: [self sign ~= anObject sign])
		ifTrue: [^ self errorUndetermined].
	^ self
]

{ #category : #arithmetic }
Infinity >> - anObject [
	"Answer the difference between the receiver and the argument."

	^ self + anObject negated
]

{ #category : #arithmetic }
Infinity >> / anObject [
	"Answer the division of the receiver by the argument."

	^ self * anObject reciprocal
]

{ #category : #comparing }
Infinity >> < anObject [
	anObject isInfinity ifTrue: [^ self sign < anObject sign].
	^ self negative
]

{ #category : #comparing }
Infinity >> <= aMagnitude [
	^ self < aMagnitude
]

{ #category : #comparing }
Infinity >> = anObject [
	^ self class == anObject class and: [self sign = anObject sign]
]

{ #category : #comparing }
Infinity >> > anObject [
	anObject isInfinity ifTrue: [^ self sign > anObject sign].
	^ self positive
]

{ #category : #comparing }
Infinity >> >= aMagnitude [
	^ self > aMagnitude
]

{ #category : #converting }
Infinity >> adaptToNumber: rcvr andSend: selector [
	selector == #+ ifTrue:[^self + rcvr].
	selector == #* ifTrue:[^self * rcvr].
	selector == #- ifTrue:[^self negated + rcvr].
	selector == #/ ifTrue:[^ rcvr isInfinite ifTrue: [self errorUndetermined] ifFalse: [0]].
	selector == #> ifTrue:[^self < rcvr].
	selector == #>= ifTrue:[^self <= rcvr].
	selector == #< ifTrue:[^self > rcvr].
	selector == #<= ifTrue:[^self >= rcvr].
	^super adaptToNumber: rcvr andSend: selector
]

{ #category : #private }
Infinity >> errorUndetermined [
	^ self error: 'undetermined'
]

{ #category : #comparing }
Infinity >> hash [
	^ self sign hash + self class hash
]

{ #category : #testing }
Infinity >> isInfinite [
	^ true
]

{ #category : #testing }
Infinity >> isInfinity [
	^ true
]

{ #category : #testing }
Infinity >> isZero [
	^ false
]

{ #category : #arithmetic }
Infinity >> negated [
	"Answer a copy of the receiver with the sign changed."

	^ self class sign: self sign negated
]

{ #category : #testing }
Infinity >> negative [
	"Answer true if the receiver is negative."

	^ self sign negative
]

{ #category : #testing }
Infinity >> positive [
	"Answer true if the receiver is positive."

	^ self sign positive
]

{ #category : #printing }
Infinity >> printOn: aStream [
	self negative ifTrue: [aStream nextPut: $-].
	"aStream nextPut: Character infinity"
	aStream nextPutAll: 'infinity'
]

{ #category : #arithmetic }
Infinity >> raisedTo: aNumber [
	aNumber isInteger ifTrue: [^ self raisedToInteger: aNumber].
	^ DomainError signal
]

{ #category : #arithmetic }
Infinity >> raisedToInteger: anInteger [
	anInteger = 0 ifTrue: [^ self errorUndetermined].
	anInteger negative ifTrue: [^ 0].
	^ anInteger odd ifTrue: [self] ifFalse: [self negated]
]

{ #category : #arithmetic }
Infinity >> reciprocal [
	"Answer zero. (1 / self)"

	^ 0
]

{ #category : #accessing }
Infinity >> sign [
	"Answer the sign of the receiver."

	^ sign
]

{ #category : #'accessing-private' }
Infinity >> sign: anInteger [
	sign := anInteger
]

{ #category : #arithmetic }
Infinity >> squared [
	"Answer the square of the receiver."

	^ self class positive
]

{ #category : #testing }
Infinity >> strictlyPositive [
	"Answer true if the receiver is strictly positive."

	^ self positive
]
