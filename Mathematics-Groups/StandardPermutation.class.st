"
Bijective functions on a set [1..n]. Permutations under composition form groups (see StandardSymmetricGroup and PermutationGroup).
"
Class {
	#name : #StandardPermutation,
	#superclass : #AbstractPermutation,
	#instVars : [
		'map'
	],
	#category : #'Mathematics-Groups-Permutations'
}

{ #category : #'instance creation' }
StandardPermutation class >> map: anArray [
	^ self basicNew map: anArray
]

{ #category : #'instance creation' }
StandardPermutation class >> new [
	^ self shouldNotImplement
]

{ #category : #'instance creation' }
StandardPermutation class >> new: anInteger [
	^ self map: (1 to: anInteger) asArray
]

{ #category : #'instance creation' }
StandardPermutation class >> new: n cycle: aCollection [
	| answer first last |
	answer := self new: n.
	aCollection do: [:each|
		first isNil
			ifTrue: [first := each]
			ifFalse: [answer at: last put: each].
		last := each].
	answer at: last put: first.
	^ answer
]

{ #category : #'instance creation' }
StandardPermutation class >> new: n cycles: anArray [
	^ anArray inject: (self new: n) into: [:answer :each| answer * (self new: n cycle: each)]
]

{ #category : #'instance creation' }
StandardPermutation class >> new: anInteger evaluating: aBlock [
	^ self map: ((1 to: anInteger) collect: aBlock)
]

{ #category : #'instance creation' }
StandardPermutation class >> new: n transposing: a with: b [
	^ (self new: n)
		at: a put: b;
		at: b put: a;
		yourself
]

{ #category : #arithmetic }
StandardPermutation >> * aPermutation [
	"Answer the product (function composition) of the receiver with the argument.
	This is the group operation."
	| otherMap newMap |
	(map size = aPermutation map size)
		ifFalse: [^ DomainError signal: 'permutation of different degree'].
	otherMap := aPermutation map.
	newMap := map class new: map size.
	1 to: map size do: [:i| newMap at: i put: (map at: (otherMap at: i))].
	^ self species map: newMap
]

{ #category : #comparing }
StandardPermutation >> = aPermutation [
	^ self class = aPermutation class and: [map = aPermutation map]
]

{ #category : #converting }
StandardPermutation >> asArray [
	^ map
]

{ #category : #accessing }
StandardPermutation >> at: anInteger [
	^ map at: anInteger ifAbsent: [anInteger]
]

{ #category : #accessing }
StandardPermutation >> at: anInteger put: anotherInteger [
	^ map at: anInteger put: anotherInteger
]

{ #category : #enumerating }
StandardPermutation >> changesDo: aBlock [
	1 to: map size do: [:i| (map at: i) = i ifFalse: [aBlock value: i]]
]

{ #category : #accessing }
StandardPermutation >> degree [
	^ map size
]

{ #category : #accessing }
StandardPermutation >> domain [
	^ 1 to: map size
]

{ #category : #comparing }
StandardPermutation >> hash [
	| answer |
	answer := 0.
	1 to: map size do: [:i| | value |
		(value := map at: i) = i ifFalse: [answer := answer bitXor: i hash hashMultiply + value hash]].
	^ answer
]

{ #category : #arithmetic }
StandardPermutation >> identity [
	"Answer the identity permutation."
	^ self species new: self degree
]

{ #category : #arithmetic }
StandardPermutation >> inverse [
	"Answer the compositive inverse of the receiver."
	| values |
	values := map class new: map size.
	1 to: map size do: [:i| values at: (map at: i) put: i].
	^ self species map: values
]

{ #category : #'accessing-private' }
StandardPermutation >> map [
	^ map
]

{ #category : #'accessing-private' }
StandardPermutation >> map: aCollection [
	map := aCollection
]

{ #category : #private }
StandardPermutation >> species [
	^ StandardPermutation
]

{ #category : #accessing }
StandardPermutation >> transpositions [
	"Answer the decomposition of the receiver in product of transpositions."
	| answer last value |
	answer := OrderedCollection new.
	self changesDo: [:each|	
		last := each.
		answer reverseDo: [:one| last := one at: last].
		(value := self at: each) = last
			ifFalse: [answer addFirst: (self species new: self degree transposing: last with: value)]].
	^ answer
]
