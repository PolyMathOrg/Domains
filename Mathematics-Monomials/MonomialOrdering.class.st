"
A monomial ordering is a total order on the set of all monomials in n indeterminates, satisfying the properties:
- respects multiplication: if u <= v, then u*w <= v*w for any other monomial w;
- 1 <= u for any monomial u.

Orderings are used in the computation of Groebner bases and more generally standard bases. See StandardBasis.

"
Class {
	#name : #MonomialOrdering,
	#superclass : #Object,
	#instVars : [
		'indeterminates'
	],
	#category : #'Mathematics-Monomials-Orderings'
}

{ #category : #examples }
MonomialOrdering class >> glex: anArray [
	^ GradedLexicographicOrdering indeterminates: anArray
]

{ #category : #examples }
MonomialOrdering class >> grevlex: anArray [
	^ GradedReverseLexicographicOrdering indeterminates: anArray
]

{ #category : #'instance creation' }
MonomialOrdering class >> indeterminates: anArray [
	anArray isInteger ifTrue: [^ self new: anArray].
	^ self new indeterminates: anArray
]

{ #category : #examples }
MonomialOrdering class >> lex: anArray [
	^ LexicographicOrdering indeterminates: anArray
]

{ #category : #examples }
MonomialOrdering class >> lglex: anArray [
	^ LocalGradedLexicographicOrdering indeterminates: anArray
]

{ #category : #examples }
MonomialOrdering class >> lgrevlex: anArray [
	^ LocalGradedReverseLexicographicOrdering indeterminates: anArray
]

{ #category : #examples }
MonomialOrdering class >> llex: anArray [
	^ LocalLexicographicOrdering indeterminates: anArray
]

{ #category : #'instance creation' }
MonomialOrdering class >> new: anInteger [
	^ self new indeterminates: (1 to: anInteger)
]

{ #category : #operations }
MonomialOrdering >> , aMonomialOrdering [
	^ BlockMonomialOrdering blocks: {self. aMonomialOrdering}
]

{ #category : #comparing }
MonomialOrdering >> = aMonomialOrdering [
	self == aMonomialOrdering ifTrue: [^ true].
	aMonomialOrdering isSymbol ifTrue: [^ self type = aMonomialOrdering].
	^ false
]

{ #category : #ordering }
MonomialOrdering >> blockCompare: aMonomial with: anotherMonomial [
	^ self compare: aMonomial with: anotherMonomial
]

{ #category : #ordering }
MonomialOrdering >> compare: aMonomial with: anotherMonomial [
	^ self subclassResponsibility
]

{ #category : #copying }
MonomialOrdering >> copyWithout: anIndeterminate [
	^ self copy indeterminates: (indeterminates copyWithout: indeterminates size)
]

{ #category : #comparing }
MonomialOrdering >> hash [
	^ self type hash
]

{ #category : #accessing }
MonomialOrdering >> indeterminates [
	^ indeterminates
]

{ #category : #'accessing-private' }
MonomialOrdering >> indeterminates: anArray [
	indeterminates := anArray asArray
]

{ #category : #testing }
MonomialOrdering >> isGlobal [
	"Answer true if the receiver is a noetherian or global ordering (as opposed to a local ordering).
	Global orderings satisfy 1 < m for all nontrivial monomials m."
	^ false
]

{ #category : #testing }
MonomialOrdering >> isGraded [
	"Answer true if the receiver is a graded (also called total) ordering."
	^ false
]

{ #category : #testing }
MonomialOrdering >> isLocal [
	"Answer true if the receiver is a local (or non-noetherian) ordering.
	Local orderings satisfy 1 > m for all nontrivial monomials m."
	^ false
]

{ #category : #printing }
MonomialOrdering >> printOn: aStream [
	| M |
	self type isNil
		ifTrue: [super printOn: aStream]
		ifFalse: [aStream nextPutAll: self type].
	M := FreeAbelianMonoid new: indeterminates max.
	aStream nextPut: $[.
	self indeterminates do: [:i| aStream print: (M x: i)] separatedBy: [aStream nextPut: $,].
	aStream nextPut: $]
]

{ #category : #accessing }
MonomialOrdering >> rank [
	^ indeterminates size
]

{ #category : #accessing }
MonomialOrdering >> type [
	^ nil
]
