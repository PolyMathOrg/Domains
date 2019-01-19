"
Cosets of a normal subgroup N of a group G: {Ng : g in G} = {gN : g in G}. When the subgroup is not normal, this is not well defined and one of the subclasses should be used. See LeftCoset and RightCoset.
"
Class {
	#name : #Coset,
	#superclass : #Object,
	#instVars : [
		'subgroup',
		'representative'
	],
	#category : #'Mathematics-Groups'
}

{ #category : #'instance creation' }
Coset class >> on: aSubgroup representative: anObject [
	^ self new subgroup: aSubgroup; representative: anObject
]

{ #category : #arithmetic }
Coset >> * aCoset [
	^ self class on: subgroup representative: representative * aCoset representative
]

{ #category : #arithmetic }
Coset >> + aCoset [
	^ self class on: subgroup representative: representative + aCoset representative
]

{ #category : #comparing }
Coset >> = aCoset [
	| inverseMap op |
	op := subgroup operation.
	inverseMap := subgroup inverseMap.
	^ subgroup includes: (op value: {representative. inverseMap value: aCoset representative})
]

{ #category : #testing }
Coset >> contains: anElement [
	| op inverseMap |
	op := subgroup operation.
	inverseMap := subgroup inverseMap.
	^ subgroup contains: (op value: {anElement. inverseMap value: representative})
]

{ #category : #enumerating }
Coset >> do: aBlock [
	"Enumerate the elements of the receiver."
	| op |
	op := subgroup operation.
	subgroup do: [:each| aBlock value: (op value: {each. representative})]
]

{ #category : #comparing }
Coset >> hash [
	^ subgroup hash
]

{ #category : #testing }
Coset >> includes: anElement [
	^ (subgroup ambient includes: anElement) and: [self contains: anElement]
]

{ #category : #arithmetic }
Coset >> inverse [
	^ self class on: subgroup representative: representative inverse
]

{ #category : #arithmetic }
Coset >> negated [
	^ self class on: subgroup representative: representative negated
]

{ #category : #printing }
Coset >> printOn: aStream [
	aStream nextPut: $[; print: representative; nextPut: $]
"	| op |
	op := subgroup operation name ifNil: ['*'].
	aStream print: subgroup; space; nextPutAll: op; space; print: representative"
]

{ #category : #arithmetic }
Coset >> quotequote: aCoset [ "î"
	^ 'self class on: subgroup representative: representative î aCoset representative'
]

{ #category : #arithmetic }
Coset >> reciprocal [
	^ self class on: subgroup representative: representative reciprocal
]

{ #category : #accessing }
Coset >> representative [
	^ representative
]

{ #category : #'accessing-private' }
Coset >> representative: anObject [
	representative := anObject
]

{ #category : #accessing }
Coset >> subgroup [
	^ subgroup
]

{ #category : #'accessing-private' }
Coset >> subgroup: aSubgroup [
	subgroup := aSubgroup
]
