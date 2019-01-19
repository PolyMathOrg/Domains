"
Morphisms of simplicial complexes. See SimplicialComplex.
"
Class {
	#name : #SimplicialMap,
	#superclass : #Function,
	#instVars : [
		'map'
	],
	#category : #'Mathematics-Homology'
}

{ #category : #'instance creation' }
SimplicialMap class >> from: aSimplicialComplex to: anotherSimplicialComplex evaluating: aBlock [
	^ self from: aSimplicialComplex to: anotherSimplicialComplex mapping: [:v| (aBlock value: (Simplex vertices: {v})) vertices anyOne]
]

{ #category : #'instance creation' }
SimplicialMap class >> from: aSimplicialComplex to: anotherSimplicialComplex map: aDictionary [
	^ self new domain: aSimplicialComplex; codomain: anotherSimplicialComplex; map: aDictionary
]

{ #category : #'instance creation' }
SimplicialMap class >> from: aSimplicialComplex to: anotherSimplicialComplex mapping: aBlock [
	| map |
	map := Dictionary new.
	aSimplicialComplex support do: [:each| map at: each put: (aBlock value: each)].
	^ self from: aSimplicialComplex to: anotherSimplicialComplex map: map
]

{ #category : #comparing }
SimplicialMap >> = aSimplicialMap [
	self == aSimplicialMap ifTrue: [^ true].
	(aSimplicialMap isKindOf: SimplicialMap)
		ifFalse: [^ false].
	(self domain = aSimplicialMap domain and: [self codomain = aSimplicialMap codomain])
		ifFalse: [^ false].
	^ map = aSimplicialMap map
]

{ #category : #operations }
SimplicialMap >> fiberedProduct: aSimplicialMap [ "◊ "
	"Answer the fibered product of the receiver and the argument."
	self codomain = aSimplicialMap codomain ifFalse: [^ DomainError signal: 'codomains don''t match'].
	^ self domain fiberedProduct: aSimplicialMap domain to: self codomain evaluating: [:each| Simplex vertices: (each vertices collect: [:v| {self map value: (v at: 1). aSimplicialMap map value: (v at: 2)}]) asSet]
]

{ #category : #testing }
SimplicialMap >> isInjective [
	^ map asSet size = map size
]

{ #category : #testing }
SimplicialMap >> isSurjective [
	^ self codomain = self image
]

{ #category : #'accessing-private' }
SimplicialMap >> map: aDictionary [
	map := aDictionary
]

{ #category : #printing }
SimplicialMap >> printOn: aStream [
	self domain vertices do: [:each| aStream print: each -> (map at: each)] separatedBy: [aStream nextPutAll: ', ']
]

{ #category : #operations }
SimplicialMap >> value: aSimplex [
	^ Simplex vertices: (aSimplex vertices collect: [:each| map at: each]) asSet
]
