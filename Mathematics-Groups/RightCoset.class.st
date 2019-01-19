"
Right cosets of a subgroup H of a group G: {Hg : g in G}.
"
Class {
	#name : #RightCoset,
	#superclass : #Coset,
	#category : #'Mathematics-Groups'
}

{ #category : #comparing }
RightCoset >> = aCoset [
	| inverseMap op |
	op := subgroup operation.
	inverseMap := subgroup inverseMap.
	^ subgroup includes: (op value: {representative. inverseMap value: aCoset representative})
]

{ #category : #enumerating }
RightCoset >> do: aBlock [
	"Enumerate the elements of the receiver."
	| op |
	op := subgroup operation.
	subgroup do: [:each| aBlock value: (op value: {each. representative})]
]

{ #category : #testing }
RightCoset >> includes: anElement [
	| op inverseMap |
	op := subgroup operation.
	inverseMap := subgroup inverseMap.
	^ subgroup includes: (op value: {anElement. inverseMap value: representative})
]

{ #category : #printing }
RightCoset >> printOn: aStream [
	super printOn: aStream
"	| op |
	op := subgroup operation name ifNil: ['*'].
	aStream print: subgroup; space; nextPutAll: op; space; print: representative"
]
