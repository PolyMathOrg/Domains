"
Semirings of Ideals in a given Ring.
"
Class {
	#name : #IdealSemiring,
	#superclass : #Semiring,
	#instVars : [
		'ring'
	],
	#category : #'Mathematics-Rings'
}

{ #category : #'instance creation' }
IdealSemiring class >> on: aRing [
	^ self new ring: aRing
]

{ #category : #comparing }
IdealSemiring >> = anObject [
	^ (anObject isKindOf: IdealSemiring) and: [anObject ring = ring]
]

{ #category : #enumerating }
IdealSemiring >> do: aBlock [
	^ ring idealsDo: aBlock
]

{ #category : #comparing }
IdealSemiring >> hash [
	^ ring hash
]

{ #category : #testing }
IdealSemiring >> includes: anIdeal [
	^ (anIdeal isKindOf: Ideal) and: [anIdeal scalars = ring]
]

{ #category : #testing }
IdealSemiring >> isCommutative [
	^ ring isCommutative
]

{ #category : #accessing }
IdealSemiring >> one [
	^ ring * ring one
]

{ #category : #printing }
IdealSemiring >> printOn: aStream [
	aStream nextPutAll: 'Ideals('; print: ring; nextPut: $)
]

{ #category : #accessing }
IdealSemiring >> ring [
	^ ring
]

{ #category : #'accessing-private' }
IdealSemiring >> ring: aRing [
	ring := aRing
]

{ #category : #accessing }
IdealSemiring >> zero [
	^ ring * ring zero
]
