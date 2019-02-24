"
Finite-support bijective functions. Permutations under composition form groups (see SymmetricGroup and PermutationGroup).
"
Class {
	#name : #Permutation,
	#superclass : #AbstractPermutation,
	#instVars : [
		'map'
	],
	#category : #'Mathematics-Groups-Permutations'
}

{ #category : #'instance creation' }
Permutation class >> cycle: aCollection [
	| answer first last |
	answer := self new.
	aCollection do: [:each|
		first isNil
			ifTrue: [first := each]
			ifFalse: [answer at: last put: each].
		last := each].
	answer at: last put: first.
	^ answer
]

{ #category : #'instance creation' }
Permutation class >> cycles: anArray [
	^ anArray inject: self new into: [:answer :each| answer * (self cycle: each)]
]

{ #category : #'instance creation' }
Permutation class >> keys: anArray values: anotherArray [
	| answer |
	answer := self new.
	anArray with: anotherArray do: [:x :y| answer at: x put: y].
	^ answer
]

{ #category : #'instance creation' }
Permutation class >> new [
	"Answer a new instance of the receiver representing the identity permutation."
	^ super new map: Dictionary new
]

{ #category : #'instance creation' }
Permutation class >> on: aSet evaluating: aBlock [
	| answer |
	answer := self new.
	aSet do: [:each| answer at: each put: (aBlock value: each)].
	^ answer
]

{ #category : #'instance creation' }
Permutation class >> transposing: anObject with: anotherObject [
	"Answer the tranposition of anObject with anotherObject."
	^ self new
		at: anObject put: anotherObject;
		at: anotherObject put: anObject;
		yourself
]

{ #category : #arithmetic }
Permutation >> * aPermutation [
	"Answer the product (function composition) of the receiver with the argument.
	This is the group product operation."
	| answer |
	answer := self species new.
	self changesDo: [:each|
		answer at: each put: (self at: (aPermutation at: each))].
	aPermutation changesDo: [:each|
		answer at: each put: (self at: (aPermutation at: each))].
	^ answer
]

{ #category : #comparing }
Permutation >> = aPermutation [
	(aPermutation isKindOf: self species)
		ifFalse: [ ^ super = aPermutation ].
	map
		keysAndValuesDo: [ :key :value | 
			(aPermutation at: key) = value
				ifFalse: [ ^ false ] ].
	aPermutation map size <= map size
		ifTrue: [ ^ true ].
	aPermutation map
		keysAndValuesDo: [ :key :value | 
			value = (self at: key)
				ifFalse: [ ^ false ] ].
	^ true
]

{ #category : #converting }
Permutation >> asArray [
	^ (1 to: map size) collect: [ :each | self at: each ]
]

{ #category : #accessing }
Permutation >> at: anObject [
	^ map at: anObject ifAbsent: [ anObject ] 
]

{ #category : #accessing }
Permutation >> at: anObject put: anotherObject [
	anObject = anotherObject ifTrue: [^ anotherObject].
	^ map at: anObject put: anotherObject
]

{ #category : #enumerating }
Permutation >> changesDo: aBlock [
	map keysDo: aBlock
]

{ #category : #accessing }
Permutation >> domain [
	^ map keys as: Domain
]

{ #category : #comparing }
Permutation >> hash [
	| answer |
	answer := 0.
"	self changesDo: [:each| answer := answer + each hash]."
	map keysAndValuesDo: [:key :value| key = value ifFalse: [answer := answer bitXor: key hash hashMultiply + value hash]].
	^ answer
]

{ #category : #arithmetic }
Permutation >> identity [
	"Answer the identity permutation."
	^ self species new
]

{ #category : #arithmetic }
Permutation >> inverse [
	"Answer the compositive inverse of the receiver."

	| answer |
	answer := self species new.
	self changesDo: [:each| answer at: (self at: each) put: each].
	^ answer
]

{ #category : #testing }
Permutation >> isTransposition [
	"Answer true if the receiver is a transposition."

	^ self size = 2
]

{ #category : #'accessing-private' }
Permutation >> map [
	^ map
]

{ #category : #'accessing-private' }
Permutation >> map: aCollection [
	map := aCollection
]

{ #category : #private }
Permutation >> species [
	^ Permutation
]

{ #category : #accessing }
Permutation >> transpositions [
	"Answer the decomposition of the receiver in product of transpositions."
	| answer last value |
	answer := OrderedCollection new.
	self changesDo: [:each|	
		last := each.
		answer reverseDo: [:one| last := one at: last].
		(value := self at: each) = last
			ifFalse: [answer addFirst: (self species transposing: last with: value)]].
	^ answer
]
