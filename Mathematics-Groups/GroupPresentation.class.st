Class {
	#name : #GroupPresentation,
	#superclass : #Object,
	#instVars : [
		'generators',
		'relators'
	],
	#category : #'Mathematics-Groups'
}

{ #category : #examples }
GroupPresentation class >> C: n [
	"Answer the cyclic group of order n."
	| x |
	x := Word x: 1.
	^ self generators: {x} relators: {x raiseTo: n}
]

{ #category : #examples }
GroupPresentation class >> D: n [
	"Answer the dihedral group of order n."
	| x1 x2 |
	x1 := Word x: 1.
	x2 := Word x: 2.
	^ 'self generators: {x1. x2} relators: {x1^n. x2^2. (x1*x2)^2}'
]

{ #category : #examples }
GroupPresentation class >> free: aCollection [
	"Answer the free group on aCollection."
	^ self generators: aCollection relators: #()
]

{ #category : #'instance creation' }
GroupPresentation class >> generators: aCollection relators: anotherCollection [
	^ self new generators: aCollection; relators: anotherCollection
]

{ #category : #morphisms }
GroupPresentation >> * aPresentation [
	"Answer the free product of the receiver with the argument."
	^ self class generators: (generators, aPresentation generators) relators: (relators, aPresentation relators)
]

{ #category : #accessing }
GroupPresentation >> deficiency [
	^ generators size - relators size
]

{ #category : #accessing }
GroupPresentation >> generators [
	^ generators
]

{ #category : #'accessing-private' }
GroupPresentation >> generators: aCollection [
	generators := aCollection
]

{ #category : #printing }
GroupPresentation >> printOn: aStream [
	aStream nextPut: $<.
	generators do: [:each| aStream print: each] separatedBy: [aStream nextPut: $,].
	aStream nextPutAll: ' | '.
	relators isEmpty ifTrue: [aStream nextPut: Character emptySet].
	relators do: [:each| aStream print: each; nextPutAll: '=1'] separatedBy: [aStream nextPut: $,].
	aStream nextPut: $>
]

{ #category : #accessing }
GroupPresentation >> relators [
	^ relators
]

{ #category : #'accessing-private' }
GroupPresentation >> relators: aCollection [
	relators := aCollection
]

{ #category : #morphisms }
GroupPresentation >> square: aPresentation [ "◊ "
	^ self class generators: (generators, aPresentation generators) relators: (relators, aPresentation relators, (self commutatorWith: aPresentation))
]
