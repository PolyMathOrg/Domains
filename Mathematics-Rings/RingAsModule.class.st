"
Rank 1 free modules (or vector spaces) of scalars, i.e. a ring R viewed as a R-module (or a field K viewed as a K-vector space).

Ideals of R are seen as submodules of this ambient module.
"
Class {
	#name : #RingAsModule,
	#superclass : #FreeModule,
	#instVars : [
		'scalars'
	],
	#category : #'Mathematics-Rings'
}

{ #category : #'instance creation' }
RingAsModule class >> over: aField [
	^ self new scalars: aField
]

{ #category : #converting }
RingAsModule >> asRing [
	^ self scalars
]

{ #category : #basis }
RingAsModule >> coordinatesOf: anObject [
	"Answer the coordinates of the argument in the canonical basis."
	^ self scalars tuple: {anObject}
]

{ #category : #basis }
RingAsModule >> e: anInteger [
	"Answer the anInteger-th canonical vector."
	^ self scalars one
]

{ #category : #testing }
RingAsModule >> includes: anObject [
	^ scalars includes: anObject
]

{ #category : #converting }
RingAsModule >> over: aRing [
	"Answer the change of base ring of the receiver."
	^ self class over: aRing
]

{ #category : #printing }
RingAsModule >> printOn: aStream [
	aStream print: scalars
]

{ #category : #basis }
RingAsModule >> rank [
	^ 1
]

{ #category : #accessing }
RingAsModule >> scalars [
	^ scalars
]

{ #category : #'accessing-private' }
RingAsModule >> scalars: aRing [
	scalars := aRing
]

{ #category : #elements }
RingAsModule >> zero [
	^ scalars zero
]
