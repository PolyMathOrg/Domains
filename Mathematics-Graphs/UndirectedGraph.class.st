"
Undirected graphs. The vertices (values) can be arbitrary objects, and the edges are MutualAssociations v1 <-> v2.

Internally, graphs are represented as symmetric digraphs (i.e., whenever the edge v1 -> v2 is present, v2 -> v1 is also present).

Structure:
 digraph 		The associated directed graph (which is always symmetric)
"
Class {
	#name : #UndirectedGraph,
	#superclass : #Graph,
	#instVars : [
		'digraph'
	],
	#category : #'Mathematics-Graphs'
}

{ #category : #'instance creation' }
UndirectedGraph class >> digraph: aDigraph [
	^ self basicNew digraph: aDigraph
]

{ #category : #'adding/removing' }
UndirectedGraph >> add: anObject [
	^ digraph add: anObject
]

{ #category : #'adding/removing' }
UndirectedGraph >> addEdgeFrom: source to: target [ 
	| sourceNode targetNode |
	sourceNode := self add: source.
	targetNode := self add: target.
	sourceNode addNeighbor: targetNode.
	targetNode addNeighbor: sourceNode
]

{ #category : #'adding/removing' }
UndirectedGraph >> addEdgeFrom: source to: target label: label [
	"pre: (self nodeAt: edge key) isLabeled"
	| sourceNode targetNode |
	sourceNode := self add: source.
	targetNode := self add: target.
	sourceNode addNeighbor: targetNode label: label.
	targetNode addNeighbor: sourceNode label: label
]

{ #category : #converting }
UndirectedGraph >> asDirected [
	^ digraph
]

{ #category : #random }
UndirectedGraph >> atRandom: aRandom [
	^ digraph atRandom: aRandom
]

{ #category : #operations }
UndirectedGraph >> complement [
	^ self class digraph: digraph complement
]

{ #category : #enumerating }
UndirectedGraph >> componentsDo: aBlock [
	digraph componentsDo: [:each| aBlock value: (self class digraph: each)]
]

{ #category : #copying }
UndirectedGraph >> copy [
	^ self class digraph: digraph copy
]

{ #category : #copying }
UndirectedGraph >> copyEmpty [
	^ self class digraph: digraph copyEmpty
]

{ #category : #initialization }
UndirectedGraph >> digraph: aDigraph [
	digraph := aDigraph
]

{ #category : #random }
UndirectedGraph >> edgeAtRandom: aRandom [
	^ (digraph edgeAtRandom: aRandom) as: MutualAssociation
]

{ #category : #enumerating }
UndirectedGraph >> edgesAndLabelsDo: aBinaryBlock [
	| visited |
	visited := Set new.
	digraph edgesAndLabelsDo: [:each :label|
		(visited includes: each value -> each key)
			ifFalse: [aBinaryBlock value: (each as: MutualAssociation) value: label].
		visited add: each]
]

{ #category : #enumerating }
UndirectedGraph >> edgesDo: aBlock [
	| visited |
	visited := Set new.
	digraph edgesDo: [:each|
		(visited includes: each value -> each key)
			ifFalse: [aBlock value: (each as: MutualAssociation)].
		visited add: each]
]

{ #category : #operations }
UndirectedGraph >> flowPolynomial [
	"The flow polynomial F(G,k) is a polynomial in k that counts the number of nowhere-zero k-flows of G."
	| x |
	x := ZZ polynomials x.
	^ (-1)raisedTo:(self size + self numberOfEdges + self components size) * (self tuttePolynomial value: {0. 1 - x})
]

{ #category : #enumerating }
UndirectedGraph >> fullEdgesAndLabelsDo: aBinaryBlock [
	| visited |
	visited := Set new.
	digraph fullEdgesAndLabelsDo: [:each :label|
		(visited includes: each value -> each key)
			ifFalse: [aBinaryBlock value: (each as: MutualAssociation) value: label].
		visited add: each]
]

{ #category : #enumerating }
UndirectedGraph >> fullEdgesDo: aBlock [
	| visited |
	visited := Set new.
	digraph fullEdgesDo: [:each|
		(visited includes: each value -> each key)
			ifFalse: [aBlock value: (each as: MutualAssociation)].
		visited add: each]
]

{ #category : #testing }
UndirectedGraph >> isDirected [
	^ false
]

{ #category : #testing }
UndirectedGraph >> isImplicit [
	^ digraph isImplicit
]

{ #category : #testing }
UndirectedGraph >> isLabeled [
	^ digraph isLabeled
]

{ #category : #testing }
UndirectedGraph >> isOrdered [
	^ digraph isOrdered
]

{ #category : #testing }
UndirectedGraph >> isSymmetric [
	^ true
]

{ #category : #testing }
UndirectedGraph >> isTransitive [
	^ true
]

{ #category : #accessing }
UndirectedGraph >> nodes [
	^ digraph nodes
]

{ #category : #enumerating }
UndirectedGraph >> nodesDo: aBlock [
	digraph nodesDo: aBlock
]

{ #category : #accessing }
UndirectedGraph >> numberOfEdges [
	^ digraph numberOfEdges / 2
]

{ #category : #testing }
UndirectedGraph >> occurrencesOf: anObject [ 
	"Answer how many of the receiver's elements are equal to anObject."

	^(self includes: anObject) ifTrue: [1] ifFalse: [0]
]

{ #category : #'adding/removing' }
UndirectedGraph >> remove: aGraphNode ifAbsent: exceptionBlock [ 
	"Remove the given node, evaluate exceptionBlock if it's not part of the graph.
	pre: the node shouldn't be the target of an edge."
	^ digraph remove: aGraphNode ifAbsent: exceptionBlock
]

{ #category : #'adding/removing' }
UndirectedGraph >> removeEdgeFrom: source to: target ifAbsent: exceptionBlock [ 
	"Remove the given edge, evaluate exceptionBlock if it doesn't exist. 
	pre: both the source and target of the edge must be in the graph."
	| sourceNode targetNode |
	sourceNode := self nodeAt: source.
	targetNode := self nodeAt: target.
	(sourceNode hasEdgeTo: targetNode)
		ifTrue:
			[sourceNode removeNeighbor: targetNode.
			targetNode removeNeighbor: sourceNode]
		ifFalse: [^ exceptionBlock value]
]

{ #category : #operations }
UndirectedGraph >> symmetric [
	^ self
]

{ #category : #operations }
UndirectedGraph >> transposed [
	^ self
]

{ #category : #operations }
UndirectedGraph >> tuttePolynomial [
	| P K G |
	P := ZZ polynomialsIn: #(x y).
	self isEdgeless ifTrue: [^ P one].
	K := self components size.
	self edgesDo: [:e|
		e key = e value "it's a loop"
			ifTrue: [^ P y * (self - e) tuttePolynomial]
			ifFalse:
				[G := self - e.
				G components size > K "it's a bridge"
					ifTrue: [^ P x * (self / e) tuttePolynomial]
					ifFalse: [^ G tuttePolynomial + (self / e) tuttePolynomial]]].
	^ self error: 'inconsistency, this line should have been reaached'
]

{ #category : #accessing }
UndirectedGraph >> type [
	^ digraph type
]
