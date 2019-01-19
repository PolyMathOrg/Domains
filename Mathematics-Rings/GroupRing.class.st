"
Given a ring R and a group G, the group ring R[G] can be seen as a ring or as a free R-module with basis one-to-one with G. As a ring, its addition law is that of the free module, and the multiplication extends by linearity the given group law on the basis.

The elements of the group ring R[G] are finite formal linear combinations of elements of G with coefficients in R, or the finite-support functions from G to R (see GroupRingElement).

When the ring R is commutative, the group ring is also referred to as a group algebra.

Categorically, the group ring construction is left adjoint to the group of units (see UnitGroup). It's also a 'category algebra' analogous to the monoid ring for monoids and incidence algebra for posets.

References:
	https://en.wikipedia.org/wiki/Group_ring
"
Class {
	#name : #GroupRing,
	#superclass : #Ring,
	#instVars : [
		'group',
		'scalars'
	],
	#category : #'Mathematics-Rings'
}

{ #category : #'instance creation' }
GroupRing class >> on: aGroup over: aRing [
	^ self new group: aGroup; scalars: aRing
]

{ #category : #elements }
GroupRing >> ! anObject [
	(self group includes: anObject)
		ifTrue: [^ self embed: anObject].
	(self scalars includes: anObject)
		ifTrue: [^ self one * anObject].
	^ super ! anObject
]

{ #category : #comparing }
GroupRing >> <= aGroupRing [
	(aGroupRing isKindOf: GroupRing) ifFalse: [^ super <= aGroupRing].
	^ self scalars <= aGroupRing scalars and: [self group <= aGroupRing group]
]

{ #category : #comparing }
GroupRing >> = anObject [
	self == anObject ifTrue: [^ true].
	^ (anObject isKindOf: GroupRing) and: [anObject scalars = scalars and: [anObject group = group]]
]

{ #category : #morphisms }
GroupRing >> augmentation [
	"Answer the augmentation map, a ring homomorphism (an epimorphism) from the receiver to the ring of scalars."
	^ self to: self scalars evaluating: [:f| f augmentation]
]

{ #category : #accessing }
GroupRing >> augmentationIdeal [
	^ self augmentation kernel
]

{ #category : #elements }
GroupRing >> coefficients: aFormalSum [
	^ (GroupRingElement coefficients: aFormalSum) parent: self
]

{ #category : #testing }
GroupRing >> contains: anObject [
	anObject coefficients keysAndValuesDo: [:key :value|
		(group includes: key) ifFalse: [^ false].
		(scalars includes: value) ifFalse: [^ false]].
	^ true
]

{ #category : #morphisms }
GroupRing >> embed: aGroupElement [
	^ self coefficients: ((Dictionary new: 1) at: aGroupElement put: self scalars one; yourself)
]

{ #category : #morphisms }
GroupRing >> embedding [
	^ (Function from: self group to: self evaluating: [:g| self embed: g]) name: 'i' "should be a group homomorphism in Hom(Grp,Ab)?"
]

{ #category : #morphisms }
GroupRing >> from: aDomain [
	"aDomain  self group ifNotNil: [:aMorphism| ^ self embedding î aMorphism]."
	^ super from: aDomain
]

{ #category : #accessing }
GroupRing >> generators [
	^ (self group generators ifNil: [^ nil]) apply: self embedding
]

{ #category : #accessing }
GroupRing >> group [
	^ group
]

{ #category : #'accessing-private' }
GroupRing >> group: aGroup [
	group := aGroup
]

{ #category : #comparing }
GroupRing >> hash [
	^ scalars hash + group hash hashMultiply
]

{ #category : #testing }
GroupRing >> includes: anObject [
	^ (anObject isKindOf: GroupRingElement) and: [anObject parent = self]
]

{ #category : #testing }
GroupRing >> isCommutative [
	^ scalars isCommutative and: [group isCommutative]
]

{ #category : #testing }
GroupRing >> isFinite [
	^ scalars isFinite and: [group isFinite]
]

{ #category : #accessing }
GroupRing >> one [
	^ self embed: self group identity
]

{ #category : #printing }
GroupRing >> printOn: aStream [
	aStream print: self scalars; nextPut: $[; print: self group; nextPut: $]
]

{ #category : #accessing }
GroupRing >> scalars [
	^ scalars
]

{ #category : #'accessing-private' }
GroupRing >> scalars: aRing [
	scalars := aRing
]
