"
Left cosets of a subgroup H of a group G: {gH : g in G}.
"
Class {
	#name : #LeftCoset,
	#superclass : #Coset,
	#category : #'Mathematics-Groups'
}

{ #category : #'instance creation' }
LeftCoset class >> on: aSubgroup representative: anObject [
	^ self new subgroup: aSubgroup; representative: anObject
]

{ #category : #comparing }
LeftCoset >> = aCoset [
	| inverseMap op |
	op := subgroup operation.
	inverseMap := subgroup inverseMap.
	^ subgroup includes: (op value: {representative. inverseMap value: aCoset representative})
]

{ #category : #enumerating }
LeftCoset >> do: aBlock [
	"Enumerate the elements of the receiver."
	| op |
	op := subgroup operation.
	subgroup do: [:each| aBlock value: (op value: {representative. each})]
]

{ #category : #testing }
LeftCoset >> includes: anElement [
	| op inverseMap |
	op := subgroup operation.
	inverseMap := subgroup inverseMap.
	^ subgroup includes: (op value: {inverseMap value: representative. anElement})
]

{ #category : #printing }
LeftCoset >> printOn: aStream [
	super printOn: aStream
"	| op |
	op := subgroup operation name ifNil: ['*'].
	aStream print: representative; space; nextPutAll: op; space; print: subgroup"
]
