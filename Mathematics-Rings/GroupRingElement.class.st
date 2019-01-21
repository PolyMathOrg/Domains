"
Formal linear combinations of elements of a group G with coefficients in a ring R. Alternatively, they can be thought as the finite-support functions from G to R. They form a ring R[G] called the group ring of G over R. See GroupRing.
"
Class {
	#name : #GroupRingElement,
	#superclass : #FormalSum,
	#category : #'Mathematics-Rings'
}

{ #category : #'instance creation' }
GroupRingElement class >> coefficients: aFormalSum [
	^ self basicNew coefficients: aFormalSum
]

{ #category : #arithmetic }
GroupRingElement >> * anObject [
	((self scalars includes: anObject) or: [anObject isInteger])
		ifTrue: [^ super * anObject].
	(self parent includes: anObject)
		ifTrue: [^ self convolution: anObject].
	(self parent group includes: anObject)
		ifTrue: [^ self multipliedByGroupElement: anObject].
	^ DomainError signal
]

{ #category : #converting }
GroupRingElement >> asFunction [
	^ Function from: parent group to: parent scalars evaluating: [:each| self at: each]
]

{ #category : #operations }
GroupRingElement >> augmentation [
	| answer |
	answer := self scalars zero.
	self coefficientsDo: [:each| answer := answer + each].
	^ answer
]

{ #category : #arithmetic }
GroupRingElement >> multipliedByGroupElement: aGroupElement [
	| newCoefficients |
	newCoefficients := Dictionary new: self size.
	self associationsDo: [:each| newCoefficients at: each key * aGroupElement put: each value].
	^ self parent coefficients: newCoefficients
]

{ #category : #accessing }
GroupRingElement >> one [
	^ self parent one
]

{ #category : #arithmetic }
GroupRingElement >> raisedTo: anInteger [
	"Answer the receiver raised to the power anInteger."

	(anInteger isInteger and: [ anInteger >= 0 ])
		ifFalse: [ ^ DomainError signal: 'undefinted' ].
	anInteger = 0
		ifTrue: [ ^ self one ].
	anInteger = 1
		ifTrue: [ ^ self ].
	^ (self squared raisedTo: anInteger // 2)
		* (self raisedTo: anInteger \\ 2)
]

{ #category : #arithmetic }
GroupRingElement >> squared [
	^ self * self
]

{ #category : #operations }
GroupRingElement >> value: aGroupElement [
	"The elements of the group ring R[G] are essentially the finite-support functions from G to R."
	^ self at: aGroupElement
]
