"
Block or product monomial orderings. They are used, for example, to define elimination orderings such that a subset of the indeterminates are always greater and the rest of the indeterminates.
"
Class {
	#name : #BlockMonomialOrdering,
	#superclass : #MonomialOrdering,
	#instVars : [
		'blocks'
	],
	#category : #'Mathematics-Monomials-Orderings'
}

{ #category : #'instance creation' }
BlockMonomialOrdering class >> blocks: anArray [
	^ self new blocks: anArray
]

{ #category : #operations }
BlockMonomialOrdering >> , aMonomialOrdering [
	^ self species blocks: blocks, aMonomialOrdering
]

{ #category : #'accessing-private' }
BlockMonomialOrdering >> blocks: anArray [
	blocks := anArray.
	indeterminates := Array streamContents: [:aStream| blocks do: [:each| aStream nextPutAll: each indeterminates]]
]

{ #category : #ordering }
BlockMonomialOrdering >> compare: aMonomial with: anotherMonomial [
	| result |
	blocks do: [:each|
		(result := each blockCompare: aMonomial with: anotherMonomial) == 0 ifFalse: [^ result]].
	^ result
]

{ #category : #testing }
BlockMonomialOrdering >> isGlobal [
	^ blocks allSatisfy: [:each| each isGlobal]
]

{ #category : #testing }
BlockMonomialOrdering >> isLocal [
	^ blocks allSatisfy: [:each| each isLocal]
]

{ #category : #printing }
BlockMonomialOrdering >> printOn: aStream [
	blocks do: [:each| aStream print: each] separatedBy: [aStream space; nextPut: Character times; space]
]
