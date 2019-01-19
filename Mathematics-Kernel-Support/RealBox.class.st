"
Boxes in R^n built by the cartesian product of one-dimensional intervals (instances of RealInterval).

Example:
	RealBox new
		add: (RealInterval closed: -1 closed: 1);
		add: (RealInterval open: 3 open: 4);
		add: (RealInterval closed: 0 open: Infinity positive);
		yourself.

"
Class {
	#name : #RealBox,
	#superclass : #Domain,
	#instVars : [
		'components'
	],
	#category : #'Mathematics-Kernel-Support'
}

{ #category : #comparing }
RealBox >> = anObject [
	"Answer true if the receiver equals the argument."

	self size = anObject size ifFalse: [^ false].
	1 to: self size do: [ :each | (self at: each) = (anObject at: each) ifFalse: [^ false]].
	^ true
]

{ #category : #accessing }
RealBox >> add: aRealInterval [
	^ components add: aRealInterval
]

{ #category : #accessing }
RealBox >> addAll: aCollection [
	"Add the elements in the argument to the receiver. Answer the argument."

	aCollection do: [ :each | self add: each].
	^ aCollection
]

{ #category : #accessing }
RealBox >> at: anInteger [
	"Answer the anInteger-th component of the receiver."
	^ components at: anInteger
]

{ #category : #'accessing-private' }
RealBox >> components [
	^ components
]

{ #category : #'accessing-private' }
RealBox >> components: aCollection [
	components := aCollection
]

{ #category : #accessing }
RealBox >> dimension [
	^ components inject: 0 into: [:sum :each| sum + each]
]

{ #category : #enumerating }
RealBox >> do: aBlock [
	"Enumerate the components of the receiver."
	components do: aBlock
]

{ #category : #accessing }
RealBox >> first [
	^ self at: 1
]

{ #category : #comparing }
RealBox >> hash [
	"Answer the hash value of the receiver."

	^ self size = 0
		ifTrue: [0]
		ifFalse: [self first hash hashMultiply + self last hash hashMultiply + self size hash]
]

{ #category : #testing }
RealBox >> includes: aTuple [
	1 to: self size do: [:each|
		((self at: each) includes: (aTuple at: each)) ifFalse: [^ false]].
	^ true
]

{ #category : #initialization }
RealBox >> initialize [
	components := OrderedCollection new: 3
]

{ #category : #testing }
RealBox >> isBounded [
	self do: [:each| each isBounded ifFalse: [^ false]].
	^ true
]

{ #category : #testing }
RealBox >> isClosed [
	self do: [:each| each isClosed ifFalse: [^ false]].
	^ true
]

{ #category : #testing }
RealBox >> isOpen [
	self do: [ :each | each isOpen ifFalse: [^ false]].
	^ true
]

{ #category : #accessing }
RealBox >> last [
	^ self at: self size
]

{ #category : #accessing }
RealBox >> measure [
	^ components inject: 1 into: [:measure :each| measure * each measure]
]

{ #category : #accessing }
RealBox >> midpoint [
	^ RR tuple: (components collect: [:each| each midpoint])
]

{ #category : #printing }
RealBox >> printOn: aStream [
	components do: [:each| aStream print: each] separatedBy: [aStream nextPut: Character times]
]

{ #category : #accessing }
RealBox >> sample [
	"Answer a sample point in the receiver."
	^ RR tuple: self size evaluating: [:each| (self at: each) sample]
]

{ #category : #accessing }
RealBox >> size [
	^ components size
]
