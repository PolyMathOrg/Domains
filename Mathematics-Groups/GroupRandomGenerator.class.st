"
Product Replacement Algorithm for generating random elements in a group from a set of generators. Essentially, it performs a random walk on a Cayley graph.
"
Class {
	#name : #GroupRandomGenerator,
	#superclass : #RandomGenerator,
	#instVars : [
		'state'
	],
	#category : #'Mathematics-Groups'
}

{ #category : #accessing }
GroupRandomGenerator >> generators: aCollection [
	state := aCollection asOrderedCollection.
	60 - (state size min: 10) timesRepeat: [self next] "initial precomputation takes about 60 multiplications / inversions in the group"
]

{ #category : #generating }
GroupRandomGenerator >> next [
	"Product Replacement Algorithm. After the initial precomputation, every new random element takes one multiplication and 1/2 inversion in the group."
	| g h i |
	state isNil ifTrue: [self generators: self domain generators].
	g := state atRandom: random.
	[(state at: (i := state size atRandom: random)) == g and: [state size > 1 "otherwise fails with cyclic groups"]] whileTrue.
	(2 atRandom: random) = 1 ifTrue: [g := self domain inverseMap value: g].
	h := self domain operation value: ({g. state at: i} shuffleBy: random).
	state size < 10 ifTrue: [state add: h] ifFalse: [state at: i put: h].
	^ h
]
