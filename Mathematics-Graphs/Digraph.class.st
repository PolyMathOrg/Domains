"
Directed graphs (digraphs). The vertices (values) can be arbitrary objects, and the edges are Associations v1 -> v2. It uses a sparse representation, implemented as a collection of nodes (GraphNodes) where each node knows its neighbors.

Some properties of the graph are encoded in the class of its nodes (e.g. whether the graph is ordered, has a fixed arity, or the edges are labeled). The 'creation block' is initialized so that appropriate nodes are made.

Structure:
 nodes 			Set of GraphNodes
 nodeCreator 	a block which is evaluated to create a new node
 type 			a Symbol indicating what the default node type is
"
Class {
	#name : #Digraph,
	#superclass : #Graph,
	#instVars : [
		'nodes',
		'nodeCreator',
		'type'
	],
	#classVars : [
		'InitializationBlocks'
	],
	#category : #'Mathematics-Graphs'
}

{ #category : #'instance creation' }
Digraph class >> arity: n [
	"Create a new ordered graph with fixed arity."
	^ self basicNew initialize arity: n
]

{ #category : #'instance creation' }
Digraph class >> arityLabeled: n [
	"Create a new labeled, ordered graph with fixed arity."
	^ self basicNew initialize arityLabeled: n
]

{ #category : #'instance creation' }
Digraph class >> binary [
	"Create an ordered graph with arity of 2 (ie each vertex has exactly two connecting edges)."
	^ self basicNew initialize binary
]

{ #category : #'instance creation' }
Digraph class >> binaryLabeled [
	"Create an labeled, ordered graph with arity of 2 (ie each vertex has exactly two connecting edges)."
	^ self basicNew initialize binaryLabeled
]

{ #category : #'instance creation' }
Digraph class >> implicitCollection: collectionBlock [
	"Create a new graph, using the structure implicit in existing objects.
	Each node is the graph is accessed by evaluating collectionBlock to yield a collection of neighbouring nodes."
	^ self basicNew initialize implicitCollection: collectionBlock
]

{ #category : #'instance creation' }
Digraph class >> implicitIteratorBlock: iteratorBlock [
	"Create a new graph, using the structure implicit in existing objects.
	Each node is the graph is accessed by evaluating iteratorBlock to iterate over a collection of neighbouring nodes."
	^ self basicNew initialize implicitIteratorBlock: iteratorBlock
]

{ #category : #initialization }
Digraph class >> initialize [
	"Digraph initialize"
	InitializationBlocks	:=  Dictionary new.
	InitializationBlocks
		at: #binary
		put: [:value | ExplicitGraphNode binary: value];
		at: #arity
		put: [:n | [:value | ExplicitGraphNode on: value arity: n]];
		at: #ordered
		put: [:value | ExplicitGraphNode ordered: value];
		at: #unordered
		put: [:value | ExplicitGraphNode newOn: value];
		at: #arityLabeled
		put: [:n | [:value | LabeledExplicitGraphNode on: value arity: n]];
		at: #binaryLabeled
		put: [:value | LabeledExplicitGraphNode binary: value];
		at: #orderedLabeled
		put: [:value | LabeledExplicitGraphNode ordered: value];
		at: #unorderedLabeled
		put: [:value | LabeledExplicitGraphNode newOn: value];
		at: #implicitCollection
		put: [:graph :collectionBlock | [:value | ImplicitGraphNode
				on: value
				collectionBlock: [(collectionBlock value: value)
						collect: [:node | graph add: node]]]];
		at: #implicitIteratorBlock
		put: [:graph :iteratorBlock | [:value | 
			| iterator | 
			iterator := iteratorBlock value: value.
			ImplicitGraphNode
				on: value
				iteratorBlock: [:aBlock | iterator
						value: [:node | aBlock
								value: (graph nodes add: node)]]]]
]

{ #category : #'instance creation' }
Digraph class >> ordered [
	"Create a new ordered graph."
	^ self basicNew initialize ordered
]

{ #category : #'instance creation' }
Digraph class >> orderedLabeled [
	"Create a new labeled, ordered graph."
	^ self basicNew initialize orderedLabeled
]

{ #category : #'instance creation' }
Digraph class >> unordered [
	"Create a new unordered graph."
	^ self basicNew initialize unordered
]

{ #category : #'instance creation' }
Digraph class >> unorderedLabeled [
	"Create a new labeled, unordered graph."
	^ self basicNew initialize unorderedLabeled
]

{ #category : #'adding/removing' }
Digraph >> add: anObject [
	"Create a new GraphNode for the value (if necessary), and add it to the graph. You shouldn't be calling this unless you're sure what you're doing. Better to add nodes by adding edges."
	^ nodes at: anObject ifAbsentPut: [nodeCreator value: ((anObject isKindOf: GraphNode) ifTrue: [anObject value] ifFalse: [anObject])]
]

{ #category : #'adding/removing' }
Digraph >> addEdgeFrom: source to: target [ 
	| sourceNode targetNode |
	sourceNode := self add: source.
	targetNode := self add: target.
	sourceNode addNeighbor: targetNode
]

{ #category : #'adding/removing' }
Digraph >> addEdgeFrom: source to: target label: label [
	"pre: (self nodeAt: edge key) isLabeled"
	| sourceNode targetNode |
	sourceNode := self add: source.
	targetNode := self add: target.
	sourceNode addNeighbor: targetNode label: label
]

{ #category : #initialization }
Digraph >> arity: n [
	type := #(#arity).
	nodeCreator := (InitializationBlocks at: #arity) value: n
]

{ #category : #initialization }
Digraph >> arityLabeled: n [
	type := #(#arity #labeled).
	nodeCreator := (InitializationBlocks at: #arityLabeled) value: n
]

{ #category : #converting }
Digraph >> asRooted [
	| answer |
	answer := RootedDigraph unordered.
	answer addAll: self.
	self edgesDo: [:each| answer addEdge: each].
	answer findRoots.
	^ answer
]

{ #category : #converting }
Digraph >> asUndirected [
	^ UndirectedGraph digraph: self symmetric
]

{ #category : #random }
Digraph >> atRandom: aRandom [
	^ (nodes atRandom: aRandom) value
]

{ #category : #initialization }
Digraph >> binary [
	type := #(#binary).
	nodeCreator := InitializationBlocks at: #binary
]

{ #category : #initialization }
Digraph >> binaryLabeled [
	type := #(#binary #labeled).
	nodeCreator := InitializationBlocks at: #binaryLabeled
]

{ #category : #operations }
Digraph >> complement [
	"Answer the complement graph, i.e. the graph where two vertices are connected iff they are *not* connected in the receiver."
	| answer |
	answer := self copyEmpty.
	self nodesDo: [:x|
		| neighbors |
		answer add: x.
		neighbors := x neighbors.
		self nodesDo: [:y| (neighbors includes: y) ifFalse: [answer addEdgeFrom: x to: y]]].
	^ answer
]

{ #category : #enumerating }
Digraph >> componentsDo: aBlock [
	"Iterate over the Strongly Connected Components of the receiver."
	| component remainingNodes node |
	remainingNodes := self nodes copy.
	[remainingNodes isEmpty]
		whileFalse:
			[node := remainingNodes anyOne.
			component := self copyEmpty.
			node markDo: [:each|
				component nodes add: each.
				remainingNodes remove: each ifAbsent: []].
			aBlock value: component]
]

{ #category : #copying }
Digraph >> copy [
	^ self collect: [:each| each]
]

{ #category : #copying }
Digraph >> copyEmpty [
	"Return a graph of the same type with no nodes or edges."
	^self isImplicit
		ifTrue: [self class ordered]
		ifFalse: [super copy initialize]
]

{ #category : #random }
Digraph >> edgeAtRandom: aRandom [
	| count |
	3 timesRepeat:
		[| source |
		(source := nodes atRandom: aRandom) neighbors
			ifNotEmpty: [:neighbors| ^ source -> (neighbors atRandom: aRandom)]].
	count := self numberOfEdges atRandom.
	self edgesDo: [:each| (count := count - 1) > 0 ifFalse: [^ each]].
	self error: 'inconsitency problem, edge not found'
]

{ #category : #enumerating }
Digraph >> edgesAndLabelsDo: aBinaryBlock [
	self nodesDo: [:node| node neighborsAndLabelsDo: [:n :label| aBinaryBlock value: (Association key: node value value: n value) value: label]]
]

{ #category : #enumerating }
Digraph >> edgesDo: aBlock [
	self nodesDo: [:node| node neighborsDo: [:n| aBlock value: (Association key: node value value: n value)]]
]

{ #category : #enumerating }
Digraph >> fullEdgesAndLabelsDo: aBinaryBlock [
	self nodesDo: [:node| node neighborsAndLabelsDo: [:n :label| aBinaryBlock value: (Association key: node value: n) value: label]]
]

{ #category : #enumerating }
Digraph >> fullEdgesDo: aBlock [
	self nodesDo: [:node| node neighborsDo: [:n| aBlock value: (Association key: node value: n)]]
]

{ #category : #initialization }
Digraph >> implicitCollection: collectionBlock [
	type := #(#implicitCollection).
	nodeCreator := (InitializationBlocks at: #implicitCollection) value: self value: collectionBlock
]

{ #category : #initialization }
Digraph >> implicitIteratorBlock: iteratorBlock [
	type := #(#implicitIteratorBlock).
	nodeCreator := (InitializationBlocks at: #implicitIteratorBlock) value: self value: iteratorBlock
]

{ #category : #initialization }
Digraph >> initialize [
	nodes := KeyedSet new
]

{ #category : #private }
Digraph >> isDirected [
	^ true
]

{ #category : #private }
Digraph >> isImplicit [
	"Is the node creator for implicit nodes?"
	^(type includes: #implicitCollection) or: [type includes: #implicitIteratorBlock]
]

{ #category : #private }
Digraph >> isLabeled [
	"Is the node creator for labeled nodes?"
	^type includes: #labeled
]

{ #category : #testing }
Digraph >> isOrdered [
	^ self type includes: #ordered
]

{ #category : #testing }
Digraph >> isOriented [
	self nodesDo: [:each|
		each neighborsDo: [:neighbor|
			(neighbor hasEdgeTo: each) ifTrue: [^ false]]].
	^ true
]

{ #category : #testing }
Digraph >> isSymmetric [
	^ nodes allSatisfy: [:each| each isSymmetric]
]

{ #category : #testing }
Digraph >> isTransitive [
	^ nodes allSatisfy: [:each| each isTransitive]
]

{ #category : #testing }
Digraph >> isUnordered [
	^ self type includes: #unordered
]

{ #category : #testing }
Digraph >> isWeaklyConnected [
	"A graph is said to be 'weakly connected' when its symmetric closure is connected."
	^ self symmetric isConnected
]

{ #category : #private }
Digraph >> nodeCreator: n [
	nodeCreator := n
]

{ #category : #accessing }
Digraph >> nodes [
	^ nodes
]

{ #category : #enumerating }
Digraph >> nodesDo: aBlock [
	self isImplicit
		ifTrue: [nodes asOrderedCollection do: aBlock]
		ifFalse: [nodes do: aBlock]
]

{ #category : #initialization }
Digraph >> ordered [
	type := #(#ordered).
	nodeCreator := InitializationBlocks at: #ordered
]

{ #category : #initialization }
Digraph >> orderedLabeled [
	type := #(#ordered #labeled).
	nodeCreator := InitializationBlocks at: #orderedLabeled
]

{ #category : #'adding/removing' }
Digraph >> remove: aGraphNode ifAbsent: exceptionBlock [ 
	"Remove the given node, evaluate exceptionBlock if it's not part of the graph.
	pre: the node shouldn't be the target of an edge."
	^nodes remove: aGraphNode ifAbsent: exceptionBlock
]

{ #category : #'adding/removing' }
Digraph >> removeEdgeFrom: source to: target ifAbsent: exceptionBlock [ 
	"Remove the given edge, evaluate exceptionBlock if it doesn't exist. 
	pre: both the source and target of the edge must be in the graph."
	| sourceNode targetNode |
	sourceNode := self nodeAt: source.
	targetNode := self nodeAt: target.
	(sourceNode hasEdgeTo: targetNode)
		ifTrue: [sourceNode removeNeighbor: targetNode]
		ifFalse: [^ exceptionBlock value]
]

{ #category : #accessing }
Digraph >> type [
	^ type
]

{ #category : #initialization }
Digraph >> unordered [
	type := #(#unordered).
	nodeCreator := InitializationBlocks at: #unordered
]

{ #category : #initialization }
Digraph >> unorderedLabeled [
	type := #(#unordered #labeled).
	nodeCreator := InitializationBlocks at: #unorderedLabeled
]
