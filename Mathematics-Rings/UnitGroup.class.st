"
Given a ring R, the group of units of R is the set of elements of R that have multiplicative inverse, and they form a group under multiplication. For a field F (or more generally a division ring), the units are all the non-zero elements F \ {0}.

Categorically, this construction is a functor from the cateogory of rings to the category of groups. This functor has a left adjoint which is the integral group ring construction (see GroupRing).

References:
	https://en.wikipedia.org/wiki/Unit_(ring_theory)
"
Class {
	#name : #UnitGroup,
	#superclass : #Group,
	#instVars : [
		'ring'
	],
	#category : #'Mathematics-Rings'
}

{ #category : #'instance creation' }
UnitGroup class >> on: aRing [
	^ self new ring: aRing
]

{ #category : #testing }
UnitGroup >> contains: anElement [
	^ ring isUnit: anElement
]

{ #category : #enumerating }
UnitGroup >> do: aBlock [
	ring unitsDo: aBlock
]

{ #category : #accessing }
UnitGroup >> identity [
	^ ring one
]

{ #category : #testing }
UnitGroup >> includes: anElement [
	^ (ring includes: anElement) and: [ring isUnit: anElement]
]

{ #category : #accessing }
UnitGroup >> inverseMap [
	^ self multiplicativeInverseMap
]

{ #category : #accessing }
UnitGroup >> operation [
	^ self multiplicativeOperation
]

{ #category : #printing }
UnitGroup >> printOn: aStream [
	aStream print: ring; nextPutAll: Character times asString super 
]

{ #category : #'accessing-private' }
UnitGroup >> ring: aRing [
	ring := aRing
]
