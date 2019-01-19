"
Elements of direct products of rings. See ProductRing.
"
Class {
	#name : #ProductRingElement,
	#superclass : #Object,
	#instVars : [
		'components'
	],
	#category : #'Mathematics-Rings'
}

{ #category : #'instance creation' }
ProductRingElement class >> components: anArray [
	^ self new components: anArray
]

{ #category : #arithmetic }
ProductRingElement >> * anObject [
	anObject isInteger ifTrue: [^ self class components: components * anObject].
	^ self class components: components * anObject components
]

{ #category : #arithmetic }
ProductRingElement >> + aProductRingElement [
	^ self class components: components + aProductRingElement components
]

{ #category : #arithmetic }
ProductRingElement >> - aProductRingElement [
	^ self + aProductRingElement negated
]

{ #category : #arithmetic }
ProductRingElement >> / aProductRingElement [
	^ self * aProductRingElement reciprocal
]

{ #category : #comparing }
ProductRingElement >> = anObject [
	^ self class = anObject class and: [components = anObject components]
]

{ #category : #accessing }
ProductRingElement >> at: anInteger [
	^ components at: anInteger
]

{ #category : #private }
ProductRingElement >> components [
	^ components
]

{ #category : #private }
ProductRingElement >> components: anArray [
	components := anArray
]

{ #category : #comparing }
ProductRingElement >> hash [
	^ components hash
]

{ #category : #testing }
ProductRingElement >> isZero [
	^ components allSatisfy: [:each| each isZero]
]

{ #category : #arithmetic }
ProductRingElement >> negated [
	^ self class components: (components collect: [:each| each negated])
]

{ #category : #printing }
ProductRingElement >> printOn: aStream [
	aStream print: components
]

{ #category : #arithmetic }
ProductRingElement >> reciprocal [
	^ self class components: (components collect: [:each| each reciprocal ifNil: [^ nil]])
]

{ #category : #accessing }
ProductRingElement >> size [
	^ components size
]
