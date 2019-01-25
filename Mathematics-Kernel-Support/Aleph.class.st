"
Aleph numbers, i.e. cardinalities of infinite sets. Aleph-naught is the cardinality of the natural numbers. Assuming the continuum hypothesis, aleph-one is taken to be the cardinality of the real numbers.
"
Class {
	#name : #Aleph,
	#superclass : #Magnitude,
	#instVars : [
		'order'
	],
	#category : #'Mathematics-Kernel-Support'
}

{ #category : #'instance creation' }
Aleph class >> new [
	^ self new: 0
]

{ #category : #'instance creation' }
Aleph class >> new: anInteger [
	^ self basicNew order: anInteger
]

{ #category : #arithmetic }
Aleph >> * anObject [
	anObject = 0 ifTrue: [^ self errorUndetermined].
	^ self max: anObject
]

{ #category : #comparing }
Aleph >> < anObject [
	anObject class = self class ifTrue: [^ order < anObject order].
	^ false
]

{ #category : #comparing }
Aleph >> = anObject [
	^ self class == anObject class and: [order = anObject order]
]

{ #category : #converting }
Aleph >> adaptToNumber: rcvr andSend: selector [
	selector == #+ ifTrue:[^self + rcvr].
	selector == #* ifTrue:[^self * rcvr].
	selector == #/ ifTrue:[^ rcvr isNumber ifTrue: [0] ifFalse: [self errorUndetermined]].
	selector == #> ifTrue:[^false].
	selector == #>= ifTrue:[^false].
	selector == #< ifTrue:[^true].
	selector == #<= ifTrue:[^true].
	^super adaptToNumber: rcvr andSend: selector
]

{ #category : #comparing }
Aleph >> hash [
	^ self class hash + order hash
]

{ #category : #testing }
Aleph >> isCountable [
	^ order = 0
]

{ #category : #testing }
Aleph >> isInfinite [
	^ true
]

{ #category : #accessing }
Aleph >> order [
	^ order
]

{ #category : #initialization }
Aleph >> order: anInteger [
	order := anInteger
]

{ #category : #printing }
Aleph >> printOn: aStream [
	aStream
		nextPutAll: 'Aleph-';
		nextPutAll: order asString
]

{ #category : #arithmetic }
Aleph >> raisedTo: aNumber [
	(aNumber isInteger and: [aNumber > 0]) ifTrue: [^ self].
	DomainError signal: 'only integer positive exponents allowed'
]
