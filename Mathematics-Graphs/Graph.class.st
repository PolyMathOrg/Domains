"
Abstract class for (directed or undirected) graphs. See subclasses.
"
Class {
	#name : #Graph,
	#superclass : #Collection,
	#category : #'Mathematics-Graphs'
}

{ #category : #'example graphs' }
Graph class >> C: n [
	"Answer the cycle of n vertices 1 -> 2 -> ... -> n -> 1."
	| C |
	C := self unordered.
	1 to: n-1 do: [:i| C addEdge: i->(i+1)].
	n >= 1 ifTrue: [C addEdge: n -> 1]. "the extremal case of n = 1 is just a loop"
	^ C
]

{ #category : #'example graphs' }
Graph class >> K: n [
	"Answer the n-complete graph."
	| K |
	K := self unordered.
	1 to: n do: [:i| K add: i].
	1 to: n do: [:i| 1 to: i do: [:j| i ~= j ifTrue: [K addEdge: i->j]]].
	^ K
]

{ #category : #'example graphs' }
Graph class >> N: n [
	"Answer the null graph with n vertices {1..n}."
	^ self unordered addAll: (1 to: n); yourself
]

{ #category : #'example graphs' }
Graph class >> P: n [
	"Answer the path of n vertices 1 -> 2 -> ... -> n."
	| P |
	n > 1 ifFalse: [self error: 'path graph only definted for >= 2 vertices'].
	P := self unordered.
	1 to: n-1 do: [:i| P addEdge: i->(i+1)].
	^ P
]

{ #category : #'example graphs' }
Graph class >> S: n [
	"Answer the star graph of n vertices."
	| S |
	S := self unordered.
	2 to: n do: [:i| S addEdge: 1 -> i].
	^ S
]

{ #category : #'example graphs' }
Graph class >> W: n [
	"Answer the wheel graph of n vertices."
	| W |
	W := self unordered.
	2 to: n do: [:i| W addEdge: 1 -> i; addEdge: i -> (i=n ifTrue: [2] ifFalse: [i+1])].
	^ W
]

{ #category : #'instance creation' }
Graph class >> arity: n [
	"Create a new ordered graph with fixed arity."
	^ UndirectedGraph digraph: (Digraph arity: n)
]

{ #category : #'instance creation' }
Graph class >> arityLabeled: n [
	"Create a new labeled, ordered graph with fixed arity."
	^ UndirectedGraph digraph: (Digraph arityLabeled: n)
]

{ #category : #'instance creation' }
Graph class >> binary [
	"Create an ordered graph with arity of 2 (ie each vertex has exactly two connecting edges)."
	^ UndirectedGraph digraph: Digraph binary
]

{ #category : #'instance creation' }
Graph class >> binaryLabeled [
	"Create an labeled, ordered graph with arity of 2 (ie each vertex has exactly two connecting edges)."
	^ UndirectedGraph digraph: Digraph binaryLabeled
]

{ #category : #'example graphs' }
Graph class >> cube [
	^ self cube: 3
]

{ #category : #'example graphs' }
Graph class >> cube: n [
	"Answer an n-cube."
	| G H |
	G := self unordered addEdge: 1 -> 2; yourself.
	H := G.
	n - 1 timesRepeat: [H := H product: G].
	^ H
]

{ #category : #'example graphs' }
Graph class >> desargues [
	"Answer the Desargues graph."
	^ self petersen: 10 order: 3
]

{ #category : #'example graphs' }
Graph class >> dodecahedron [
	^ self petersen: 10 order: 2
]

{ #category : #'example graphs' }
Graph class >> durer [
	"Answer the Durer graph."
	^ self petersen: 6 order: 2
]

{ #category : #'example graphs' }
Graph class >> exampleImplicitGraph [
	"Graph exampleImplicitGraph. BUG : There is a problem when you don't  
	test classes without subclasses, maybe a problem in the block creation  
	for ImplicitGraphNode (cf. Graph>>initialize)"
	| tree |
	tree := self implicitCollection: [:class | class subclasses].
	Magnitude withAllSubclasses
		do: [:class| "class subclasses isEmpty ifFalse: ["tree add: class"]"].
	^ tree
]

{ #category : #'example graphs' }
Graph class >> exampleImplicitGraph2 [
	| forest |
	forest := self implicitCollection: [:class | class ~= ProtoObject ifTrue: [{class superclass}] ifFalse:[#()]].
	(Smalltalk organization listAtCategoryNamed: 'Mathematics-Graphs') do: [:className| forest add: (Smalltalk at: className)].
	^ forest
]

{ #category : #'example graphs' }
Graph class >> exampleImplicitGraph3 [
	"Graph exampleImplicitGraph3"
	| tree |
	tree := self implicitIteratorBlock: [:class| [:aBlock| class subclasses do: aBlock]].
	RootedDigraph withAllSuperclasses do: [:class| tree add: class].
	^tree
]

{ #category : #'example graphs' }
Graph class >> icosahedron [
	^ self unordered addEdges:
		{1->2. 2->3. 3->1.
		4->5. 5->6. 6->7. 7->8. 8->9. 9->4.
		1->9. 1->4. 1->5. 2->5. 2->6. 2->7. 3->7. 3->8. 3->9.
		10->11. 11->12. 12->10.
		10->4. 10->5. 10->6. 11->6. 11->7. 11->8. 12->8. 12->9. 12->4}; yourself
]

{ #category : #'instance creation' }
Graph class >> implicitCollection: collectionBlock [
	"Create a new graph, using the structure implicit in existing objects.
	Each node is the graph is accessed by evaluating collectionBlock to yield a collection of neighbouring nodes."
	^ UndirectedGraph digraph: (Digraph implicitCollection: collectionBlock)
]

{ #category : #'instance creation' }
Graph class >> implicitIteratorBlock: iteratorBlock [
	"Create a new graph, using the structure implicit in existing objects.
	Each node is the graph is accessed by evaluating iteratorBlock to iterate over a collection of neighbouring nodes."
	^ UndirectedGraph digraph: (Digraph implicitIteratorBlock: iteratorBlock)
]

{ #category : #'example graphs' }
Graph class >> moebiusKantor [
	"Answer the Moebius-Kantor graph."
	^ self petersen: 8 order: 3
]

{ #category : #'example graphs' }
Graph class >> nauru [
	"Answer the Nauru graph."
	^ self petersen: 12 order: 5
]

{ #category : #private }
Graph class >> new [
	^ self shouldNotImplement
]

{ #category : #'example graphs' }
Graph class >> octahedron [
	^ self unordered addEdges: {1->2. 2->3. 3->1. 1->4. 2->4. 2->5. 3->5. 3->6. 1->6. 4->5. 5->6. 6->4}; yourself
]

{ #category : #'instance creation' }
Graph class >> ordered [
	"Create a new ordered graph."
	^ UndirectedGraph digraph: Digraph ordered
]

{ #category : #'instance creation' }
Graph class >> orderedLabeled [
	"Create a new labeled, ordered graph."
	^ UndirectedGraph digraph: Digraph orderedLabeled
]

{ #category : #'example graphs' }
Graph class >> petersen [
	^ self unordered addEdges:
		{1->2. 2->3. 3->4. 4->5. 5->1.
		1->6. 2->7. 3->8. 4->9. 5->10.
		6->8. 6->9. 7->9. 7->10. 8->10}; yourself
]

{ #category : #'example graphs' }
Graph class >> petersen: n order: k [
	"Answer the generalized Petersen graph G(n,k)."
	| G |
	k < (n/2) ifFalse: [^ DomainError signal].
	G := self unordered.
	0 to: n-1 do: [:i|
		G addEdges: {i->(i+1\\n). i->(i+n). i+n->(i+k\\n+n)}].
	^ G 
]

{ #category : #'example graphs' }
Graph class >> prism: n [
	"Answer an n-prism."
	^ self petersen: n order: 1
]

{ #category : #'example graphs' }
Graph class >> square [
	^ self unordered addEdges: {1 -> 2. 2 -> 3. 3 -> 4. 4 -> 1}; yourself
]

{ #category : #'example graphs' }
Graph class >> triangle [
	^ self unordered addEdges: {1->2. 2->3. 3->1}; yourself
]

{ #category : #'instance creation' }
Graph class >> unordered [
	"Create a new unordered graph."
	^ UndirectedGraph digraph: Digraph unordered
]

{ #category : #'instance creation' }
Graph class >> unorderedLabeled [
	"Create a new labeled, unordered graph."
	^ UndirectedGraph digraph: Digraph unorderedLabeled
]

{ #category : #operations }
Graph >> * aGraph [
	"Answer the graph with all edges that connect the vertices of the receiver with the vertices of the argument. This is a commutative operation (for unlabeled graphs)."
	^ self join: aGraph
]

{ #category : #operations }
Graph >> + aGraphOrEdge [
	"Answer the dijoint union of the receiver with the argument. Assume they are disjoint."
	(aGraphOrEdge isKindOf: Association)
		ifFalse: [^ self ñ aGraphOrEdge].
	(self hasEdge: aGraphOrEdge)
		ifFalse: [^ self copy addEdge: aGraphOrEdge; yourself]
]

{ #category : #operations }
Graph >> - anEdge [
	"Answer the graph obtained by removing anEdge."
	(self hasEdge: anEdge)
		ifTrue: [^ self copy removeEdge: anEdge; yourself]
]

{ #category : #operations }
Graph >> / anEdge [
	"Answer the graph obtained by contracting the given edge a -> b, by removing the edge and collapsing a with b in a single node."

	| answer newNode found |
	(self hasEdge: anEdge) ifFalse: [^ self].
	answer := self copyEmpty.
	newNode := anEdge.
	answer add: newNode.
	self nodesDo: [:each| (each = anEdge key or: [each = anEdge value]) ifFalse: [answer add: each]].
	found := false.
	self edgesDo: [:each|
		(each = anEdge and: [found not])
			ifTrue: [found := true]
			ifFalse:
				[| e |
				e := each.
				(e key = anEdge key or: [e key = anEdge value])
					ifTrue: [e := newNode -> e value].
				(e value = anEdge key or: [e value = anEdge value])
					ifTrue: [e := e key -> newNode].
				answer addEdge: e]].
	^ answer
]

{ #category : #comparing }
Graph >> < aGraph [
	"Answer true if the receiver is a proper subgraph of aGraph."
	(aGraph isKindOf: self species) ifFalse: [^ aGraph >= self].
	self size < aGraph size ifFalse: [^ false].
	self nodesDo: [:each|
		| node |
		(aGraph includes: each value) ifFalse: [^ false].
		node := aGraph nodeAt: each value.
		each neighborsDo: [:n| (node hasEdgeTo: n value) ifFalse: [^ false]]].
	^ true
]

{ #category : #comparing }
Graph >> <= aGraph [
	"Answer true if the receiver is a subgraph of aGraph."
	(aGraph isKindOf: self species) ifFalse: [^ aGraph >= self].
	self size <= aGraph size ifFalse: [^ false].
	self nodesDo: [:each|
		| node |
		(aGraph includes: each value) ifFalse: [^ false].
		node := aGraph nodeAt: each value.
		each neighborsDo: [:n| (node hasEdgeTo: n value) ifFalse: [^ false]]].
	^ true
]

{ #category : #comparing }
Graph >> = aGraph [
	^ (aGraph isKindOf: self species) and: [self nodes = aGraph nodes and: [self edges asBag = aGraph edges asBag]]
]

{ #category : #comparing }
Graph >> > aGraph [
	"Answer true if aGraph is a proper subgraph of the receiver."
	^ aGraph < self
]

{ #category : #comparing }
Graph >> >= aGraph [
	"Answer true if aGraph is a subgraph of the receiver."
	^ aGraph <= self
]

{ #category : #'adding/removing' }
Graph >> addEdge: edge [ 
	"Add an edge (represented by an Association)."

	self addEdgeFrom: edge key to: edge value.
	^ edge
]

{ #category : #'adding/removing' }
Graph >> addEdge: edge label: label [
	"Add an edge (represented by an Association), with given label.
	pre: (self nodeAt: edge key) isLabeled"

	self addEdgeFrom: edge key to: edge value label: label.
	^edge
]

{ #category : #'adding/removing' }
Graph >> addEdges: aCollection [
	aCollection do: [:each| self addEdge: each].
	^ aCollection
]

{ #category : #operations }
Graph >> adjacencyMatrix [
	"Answer the adjacency matrix of the receiver, assuming that the vertices are the integers {1,..,n}.
	If the graph is labelled, use the labels as entries in the matrix."
	| n matrix |
	n := self order.
	matrix := (ZZ raisedTo: (n@n)) zero.
	self edgesAndLabelsDo: [:edge :label| matrix at: edge key @ edge value add: (label ifNil: [1])].
	^ matrix
]

{ #category : #operations }
Graph >> adjacencyMatrix: vertices [
	"Answer the adjacency matrix of the receiver, using the vertex ordering given by the argument."
	^ ZZ raisedTo: (vertices size @ vertices size) evaluating: [:i :j| self multiplicityFrom: (vertices at: i) to: (vertices at: j)]
]

{ #category : #enumerating }
Graph >> apply: aFunction [
	"Answer a new graph like the receiver but with vertices values mapped by aFunction."
	^ self collect: aFunction
]

{ #category : #converting }
Graph >> asMorph [
	| answer components |
	(components := self components) size = 1
		ifTrue: [^ SpringGraphMorph new graph: self].
	answer := CompositeGraphMorph newRow.
	components do: [:each|
		answer addComponent: (SpringGraphMorph new graph: each)].
	^ answer
]

{ #category : #converting }
Graph >> asStandard [
	^ self asStandard: self values asArray
]

{ #category : #converting }
Graph >> asStandard: verticesArray [
	^ self collect: [:each| verticesArray indexOf: each]
]

{ #category : #operations }
Graph >> automorphisms [
	"Answer the group of symmetries of the receiver, i.e. the group of permutations of vertices that don't change the graph."
	^ (SymmetricGroup on: self values) select: [:each| (self apply: each) = self]
]

{ #category : #operations }
Graph >> automorphismsWithInvariant: aBlock [
	"Answer the group of symmetries of the receiver, i.e. the group of permutations of vertices that don't change the graph."
	| partition |
	partition := Dictionary new.
	self nodesDo: [:each| (partition at: (aBlock value: each) ifAbsentPut: [OrderedCollection new]) add: each value].
	^ self automorphismsWithPartition: partition
]

{ #category : #operations }
Graph >> automorphismsWithPartition: aCollection [
	"Answer the group of symmetries of the receiver, i.e. the group of permutations of vertices that don't change the graph."
	| product automorphisms |
	product := CartesianProduct components: (aCollection collect: [:each| SymmetricGroup on: each]).
	automorphisms := OrderedCollection new.
	product do: [:each|
		| f |
		f := each product.
		(self apply: f) = self ifTrue: [automorphisms add: f]].
	^ PermutationGroup on: self values elements: automorphisms
]

{ #category : #statistics }
Graph >> averageDegree [
	"The average degree of the graph."
	"^ 2 * self numberOfEdges / self size"
	| sum |
	sum := self nodes sum: [:node | node degree].
	^ sum / self size
]

{ #category : #statistics }
Graph >> averagePathLength [
	"The average path length of the graph."
	| sum n progress max |
	self flag: #bug. "bug with implicit graph since nodes are labelled with integer"
	sum := 0.
	n := 2.
	max := (self order * (self order - 1) / 2) asFloat.
	"p := 1 / self order."
	progress := ProgressMorph label: 'Average path length progress'.
	progress submorphs first color: Color paleGreen lighter lighter lighter.
	progress submorphs first borderWidth: 1.
	progress openInWorld.
	self
		nodesDo: [:node1 | 
			n
				to: self order
				do: [:node2 | sum := sum
								+ (self
										breadthFirstPathFrom: node1
										to: (self nodeAt: node2))].
			n := n + 1.
			progress incrDone: self order - n / max].
	progress delete.
	^ (sum / max) asFloat
]

{ #category : #statistics }
Graph >> averagePathLength2 [
	"The average path length of the graph."
	| sum n max |
	sum := 0.
	n := 2.
	max := (self order * (self order - 1) / 2) asFloat.
	self
		nodesDo: [:node1 | 
			n
				to: self order
				do: [:node2 | sum := sum
								+ (self
										breadthFirstPathFrom: node1
										to: (self nodeAt: node2))].
			n := n + 1.].
	^ (sum / max) asFloat
]

{ #category : #statistics }
Graph >> averagePathLengthAcuteAt [
	"The aproximate average path length of the graph."
	| sum n progress p max nodesList |
	sum := 0.
	n := 2.
	max := 0.
	progress := ProgressMorph label: 'Average path length progress'.
	progress submorphs first color: Color paleGreen lighter lighter lighter.
	progress submorphs first borderWidth: 1.
	progress openInWorld.
	nodesList := OrderedCollection new.
	(0.1 * self order) rounded
		timesRepeat: [nodesList
				add: self nodes atRandom].
	p := 1 / nodesList size.
	nodesList
		do: [:node1 | 
			n
				to: nodesList size
				do: [:node2 | 
					max := max + 1.
					sum := sum
								+ (self
										breadthFirstPathFrom: node1
										to: (self nodeAt: node2))].
			n := n + 1.
			progress incrDone: p].
	progress delete.
	^ (sum / max) asFloat
]

{ #category : #statistics }
Graph >> averagePathLengthAcuteAt: percentage [
	"The aproximate average path length of the graph."
	| sum n max nodesList |
	sum := 0.
	n := 2.
	max := (self order * (self order - 1) / 2) asFloat.
	"p := 1 / self order. 
	progress := ProgressMorph label: 'Average path length progress'. 
	progress submorphs first color: Color paleGreen lighter lighter lighter. 
	progress submorphs first borderWidth: 1. 
	progress openInWorld."
	nodesList := OrderedCollection new.
	(percentage * self order) timesRepeat: [nodesList add: self nodes atRandom].
	nodesList
				do: [:node1 | 
					n
						to: nodesList size
						do: [:node2 | sum := sum
										+ (self
												breadthFirstPathFrom: node1
												to: (self nodeAt: node2))].
					n := n + 1].
	"progress delete."
	^ (sum / max) asFloat
]

{ #category : #operations }
Graph >> breadthFirstPath2From: origin to: target with: visitedNodes [ 
	| queue node nodesLevels |
	nodesLevels := Dictionary new.
	nodesLevels at: origin value put: 0.
	queue := OrderedCollection with: origin.
	visitedNodes add: origin.
	[queue isEmpty]
		whileFalse: [node := queue removeFirst.
			node neighborsDo:
				[:each | (visitedNodes includes: each)
						ifFalse: [queue addLast: each.
							visitedNodes add: each.
							nodesLevels at: each value put: (nodesLevels at: node value)
									+ 1.
							each = target
								ifTrue: [^ nodesLevels at: each value]]]].
	"No path From origin to target, i.e. the two subgraph are not conected"
	^ 0
]

{ #category : #operations }
Graph >> breadthFirstPathFrom: source to: target [ 
	| visitedNodes |
	(source isLeaf
			or: [target isLeaf])
		ifTrue: [^ 0]
		ifFalse: [visitedNodes := Set new.
			^ self
				breadthFirstPath2From: source
				to: target
				with: visitedNodes]
]

{ #category : #operations }
Graph >> breadthFirstPathFrom: origin to: target with: visitedNodes [ 
	| queue node nodesLevels |
	nodesLevels := Bag new.
	queue := OrderedCollection with: origin.
	visitedNodes add: origin.
	[queue isEmpty]
		whileFalse: [node := queue removeFirst.
			node neighborsDo:
				[:each | (visitedNodes includes: each)
						ifFalse: [queue addLast: each.
							visitedNodes add: each.
							nodesLevels add: each withOccurrences: (nodesLevels occurrencesOf: node)
									+ 1.
							each = target
								ifTrue: [^ nodesLevels occurrencesOf: each]]]].
	"No path From origin to target, i.e. the two subgraph are not conected"
	^ 0
]

{ #category : #operations }
Graph >> center [
	"Answer the center of the receiver, i.e. the subset of vertices with maximal eccentricity.
	Using Dijsktra shortest path algorithm this computation requires time O(|V|^3)."
	| radius |
	radius := self radius.
	^ self values select: [:each| (self eccentricityOf: each) = radius]
]

{ #category : #operations }
Graph >> chromaticNumber [
	"The minimum number of colors to do a proper coloring of the graph."
	| chi |
	chi := self chromaticPolynomial.
	^ (1 to: self size) detect: [:i| (chi value: i) > 0]
]

{ #category : #operations }
Graph >> chromaticPolynomial [
	"The chromatic polynomial P(G,k) is a polynomial in k that counts the number of k-colorings of G."
	^ self chromaticPolynomialAt: ZZ polynomials x
]

{ #category : #operations }
Graph >> chromaticPolynomialAt: k [
	"The chromatic polynomial P(G,k) is a polynomial in k that counts the number of k-colorings of G. Answer the evaluation at k."
	self isEdgeless ifTrue: [^ k raisedTo: self size].
	self edgesDo: [:each|
		each key = each value
			ifFalse: [^ ((self - each) chromaticPolynomialAt: k) - ((self / each) chromaticPolynomialAt: k)]].
	^ k*0
]

{ #category : #operations }
Graph >> circumference [
	"Answer the length of the longest cycle."
	^ self notYetImplemented
]

{ #category : #statistics }
Graph >> clusteringCoefficient [
	| sum |
	sum := 0.
	self nodesDo: [:node | node degree > 1 ifTrue: [sum := sum + node clusteringCoefficient]].
	^ (sum / self order) asFloat
]

{ #category : #enumerating }
Graph >> collect: aBlock [
	"Answer a new graph like the receiver but with vertices values mapped by aBlock."
	| answer |
	answer := self copyEmpty.
	self nodesDo: [:each| answer add: (aBlock value: each value)].
	self edgesDo: [:each| answer addEdgeFrom: (aBlock value: each key) to: (aBlock value: each value)].
	^ answer
]

{ #category : #enumerating }
Graph >> collect: aBlock labels: labelBlock [
	"Answer a new graph like the receiver but with vertices values mapped by aBlock."
	| answer |
	answer := self copyEmpty.
	self do: [:each| answer add: (aBlock value: each)].
	self edgesAndLabelsDo: [:each :label| answer addEdgeFrom: (aBlock value: each key) to: (aBlock value: each value) label: (labelBlock value: label)].
	^ answer
]

{ #category : #operations }
Graph >> components [
	"Answer the Strongly Connected Components of the receiver."
	^ Set accumulate: [:aBlock | self componentsDo: aBlock]
]

{ #category : #accessing }
Graph >> degree [
	self isEmpty ifTrue: [^ 0].
	^ self nodes max: [:each| each degree]
]

{ #category : #statistics }
Graph >> degreeDistribution [
	"The distribution degree of the graph."
	| b |
	b := Bag new: self size.
	self nodesDo: [:each| b add: each degree].
	^ b frequencyDistribution
]

{ #category : #accessing }
Graph >> density [
	"Answer a measure of the graph density (vs sparsity), a number between 0 and 1.
	A graph is dense if the number of edges is close to the maximum (for the given number of vertices).
	pre: assume the graph is simple."
	| V E |
	V := self size.
	E := self numberOfEdges.
	^ self isDirected ifTrue: [2*E/(V*(V-1))] ifFalse: [E/(V*(V-1))]
]

{ #category : #operations }
Graph >> diameter [
	^ self nodes max: [:each| self eccentricityOf: each]
]

{ #category : #operations }
Graph >> distanceFrom: source to: target [
	^ (Dijkstra graph: self source: source) distanceTo: target
]

{ #category : #enumerating }
Graph >> do: aBlock [
	"Iterate over the vertices of the receiver (the values, not GraphNodes)."
	self nodesDo: [:each| aBlock value: each value]
]

{ #category : #operations }
Graph >> eccentricityOf: anObject [
	^ (Dijkstra graph: self source: anObject) eccentricity
]

{ #category : #random }
Graph >> edgeAtRandom [
	^ Random withDefaultDo: [:aRandom| self edgeAtRandom: aRandom]
]

{ #category : #accessing }
Graph >> edges [
	^ Iterator on: self performing: #edgesDo:
]

{ #category : #operations }
Graph >> girth [
	"Answer the length of the shortest cycle."
	^ self notYetImplemented
]

{ #category : #testing }
Graph >> hasEdge: edge [
	^ self hasEdgeFrom: edge key to: edge value
]

{ #category : #testing }
Graph >> hasEdgeFrom: a to: b [
	^ (self nodeAt: a ifAbsent: [^ false]) hasEdgeTo: b
]

{ #category : #testing }
Graph >> hasLoop [
	self nodesDo: [:each| each hasLoop ifTrue: [^ true]].
	^ false
]

{ #category : #comparing }
Graph >> hash [
	^ self nodes hash
]

{ #category : #testing }
Graph >> includes: anObject [
	"Answer whether anObject is one of the vertices of the receiver."
	^ self nodes includes: anObject
]

{ #category : #operations }
Graph >> intersection: aGraph [
	"Answer the graph whose vertices and edges is the intersection of the vertices and edges of the receiver and the argument."
	| answer |
	answer := self copyEmpty.
	aGraph nodesDo: [:each|
		(self nodeAt: each ifAbsent: [])
			ifNotNil: [:node|
				answer add: each.
				each neighborsDo: [:n|
					(node hasEdgeTo: n)
						ifTrue: [answer addEdgeFrom: each to: n]]]].
	^ answer
]

{ #category : #testing }
Graph >> isChain [
	"Answer whether the graph is a chain - path graph."
	^ (self select: [:each| each isAnExtremity]) size + (self select:[:each| each isMiddle]) size = self order
]

{ #category : #testing }
Graph >> isComplete [
	self nodesDo: [:x| self nodesDo: [:y| (x hasEdgeTo: y) ifFalse: [^ false]]].
	^ true
]

{ #category : #testing }
Graph >> isConnected [
	| count |
	count := 0.
	self componentsDo: [:each| count := count + 1. count > 1 ifTrue: [^ false]].
	^ true
]

{ #category : #testing }
Graph >> isCubic [
	^ self nodes allSatisfy: [:each| each degree = 3]
]

{ #category : #testing }
Graph >> isCyclic [
	[self topologicalSort] on: Error do: [^ true].
	^ false
"	| remainingNodes |
	remainingNodes := self nodes copy.
	[remainingNodes isEmpty]
		whileFalse:
			[Transcript show: 'pick'; newLine.
			remainingNodes anyOne walkPre: [:each|
					Transcript show: each printString; newLine.
					remainingNodes remove: each ifAbsent: [^ true]] post: [:ignore]].
	Transcript show: 'done'; newLine.
	^ false"
]

{ #category : #testing }
Graph >> isEdgeless [
	^ self numberOfEdges = 0
]

{ #category : #testing }
Graph >> isEmpty [
	"Answer whether the receiver contains any elements."

	^ self nodes isEmpty
]

{ #category : #testing }
Graph >> isEulerian [
	"Answer true if the receiver has an Eurlerian path."
	| count |
	self flag: #fix. "it should be 'has an Eulerian circuit', and isSemiEulerian must be implemented."
	count := 0.
	self nodesDo: [:each| each degree odd ifTrue: [(count := count + 1) > 2 ifTrue: [^ false]]].
	^ count = 0 or: [count = 2]
]

{ #category : #testing }
Graph >> isHamiltonian [
	"Answer true if the receiver has a Hamiltonian cycle (or Hamiltonian circuit, vertex tour, or graph cycle), which is a cycle that visits each node once except for the start/end node that is visited twice."
	^ self closure isComplete "Bondy-Chvatai theorem"
]

{ #category : #testing }
Graph >> isReflexive [
	^ self nodes allSatisfy: [:each| each isReflexive]
]

{ #category : #testing }
Graph >> isRegular [
	| n |
	self isEmpty ifTrue: [^ true].
	n := self nodes anyOne degree.
	^ self nodes allSatisfy: [:each| each degree = n]
]

{ #category : #testing }
Graph >> isSemiEulerian [
	"Answer true if the receiver has an Eurlerian path but not an Eulerian circuit."
	self notYetImplemented
]

{ #category : #testing }
Graph >> isSimple [
	"A graph is simple if doesn't countain multiple edges with the same endpoints."
	^ self nodes allSatisfy: [:each| each isSimple]
]

{ #category : #testing }
Graph >> isTraceable [
	"Answer true if the receiver has a Hamiltonian path (or traceable path), which is a path that visits each vertex exactly once."
	^ self notYetImplemented
]

{ #category : #testing }
Graph >> isUndirected [
	^ self isDirected not
]

{ #category : #operations }
Graph >> join: aGraph [
	"Answer the graph with all edges that connect the vertices of the receiver with the vertices of the argument. This is a commutative operation (for unlabeled graphs)."
	| answer |
	answer := self copyEmpty.
	self edgesDo: [:each| (aGraph includes: each value) ifTrue: [answer addEdge: each]].
	aGraph edgesDo: [:each| (self includes: each key) ifTrue: [answer addEdge: each]].
	^ answer
]

{ #category : #operations }
Graph >> line [
	"Answer the line graph of the receiver, i.e. the graph L(G) such that:
	 - each edge of G is a vertex of L(G);
	 - if two edges of G share a common endpoint, the correspondng vertices in L(G) are connected." 
	| answer |
	self flag: #fix.
	answer := self copyEmpty.
	self fullEdgesDo: [:each| "each contains GraphNodes, not values"
		each value neighborsDo: [:n|
			answer addEdgeFrom: each to: (Association key: each value value value: n value)]].
	^ answer
]

{ #category : #operations }
Graph >> maxmimumDegree [
	^ self nodes inject: Infinity negative into: [:maximum :each| maximum max: each degree]
]

{ #category : #operations }
Graph >> minimumDegree [
	^ self nodes inject: Infinity positive into: [:minimum :each| minimum min: each degree]
]

{ #category : #operations }
Graph >> multiplicity [
	^ self edges max: [:each| self multiplicityFrom: each key to: each value]
]

{ #category : #operations }
Graph >> multiplicityFrom: source to: target [
	^ (self nodeAt: source) neighbors occurrencesOf: target
]

{ #category : #operations }
Graph >> neighborhoodOf: node [
	"Answer the subgraph of everything that is reachable from the given vertex."
	^ self subgraphInducedBy: (self nodeAt: node) neighbors
]

{ #category : #accessing }
Graph >> nodeAt: anObject [
	^ self nodeAt: anObject ifAbsent: [self errorNotFound: anObject]
]

{ #category : #accessing }
Graph >> nodeAt: anObject ifAbsent: exceptionBlock [
	^ self nodes at: anObject ifAbsent: exceptionBlock
]

{ #category : #accessing }
Graph >> numberOfEdges [
	"This is commonly known as the size of the graph, but the size message returns the order (number of vertices), as this fits in better with Smalltalk usage."
	| count |
	count := 0.
	self nodesDo: [:each| count := count + each neighbors size].
	^ count
]

{ #category : #accessing }
Graph >> order [
	"The size of a graph G=(V,E) is the number of vertices |V|, contrary to the more common convention of defining it as |E|."
	^ self size
]

{ #category : #printing }
Graph >> printOn: aStream [
	self isEmpty ifTrue: [aStream nextPut: Character emptySet. ^ self].
	super printOn: aStream
]

{ #category : #operations }
Graph >> product: aGraph [
	"Answer the cartesian product of the receiver with the argument. This is a commutative and associative operation (for unlabeled graphs)."
	| G |
	G := self copyEmpty.
	self do: [:x| aGraph do: [:y| G add: (x, y)]].
	self do: [:x| aGraph edgesDo: [:e| G addEdgeFrom: (x, e key) to: (x, e value)]].
	self edgesDo: [:e| aGraph do: [:y| G addEdgeFrom: (e key, y) to: (e value, y)]].
	^ G
]

{ #category : #operations }
Graph >> quotient [
	| Q |
	self isLabeled ifFalse: [DomainError signal: 'not a lebeled graph'].
	Q := self copyEmpty.
	self nodesDo: [:each| Q add: each label].
	self fullEdgesAndLabelsDo: [:each :label| Q addEdgeFrom: each key label to: each value label label: label].
	^ Q
]

{ #category : #operations }
Graph >> radius [
	^ self nodes min: [:each| self eccentricityOf: each]
"	^ (FloydWarshall graph: self) radius"
]

{ #category : #operations }
Graph >> reflexive [
	"Answer the reflexive closure of the receiver."
	| answer |
	answer := self copy.
	answer nodesDo: [:each | each hasLoop ifFalse: [answer addEdgeFrom: each to: each]].
	^ answer
]

{ #category : #'adding/removing' }
Graph >> removeEdge: anEdge [
	"Remove the given edge.
	pre: the edge must be in the graph."
	self removeEdge: anEdge ifAbsent: [self errorNotFound: anEdge]
]

{ #category : #'adding/removing' }
Graph >> removeEdge: edge ifAbsent: exceptionBlock [ 
	"Remove the given edge, evaluate exceptionBlock if it doesn't exist.
	pre: both the source and target of the edge must be in the graph."
	^self removeEdgeFrom: edge key to: edge value ifAbsent: exceptionBlock
]

{ #category : #'adding/removing' }
Graph >> removeEdgeFrom: src to: dest [
	"Remove the given edge.
	pre: the edge must be in the graph."
	^self removeEdgeFrom: src to: dest ifAbsent: [self errorNotFound: src -> dest]
]

{ #category : #enumerating }
Graph >> select: aBlock [
	"Answer the subgraph of the receiver whose vertices satisfy aBlock."
	| answer |
	answer := self copyEmpty.
	self do: [:each| (aBlock value: each) ifTrue: [answer add: each]].
	self edgesDo: [:each|
		((aBlock value: each key) and: [aBlock value: each value])
			ifTrue: [answer addEdgeFrom: each key to: each value]].
	^ answer
]

{ #category : #operations }
Graph >> shortestPathFrom: source to: target [
	^ (Dijkstra graph: self source: source) shortestPathTo: target
]

{ #category : #random }
Graph >> shuffled [
	^ Random withDefaultDo: [:aRandom| self shuffledBy: aRandom]
]

{ #category : #random }
Graph >> shuffledBy: aRandom [
	^ self collect: ((SymmetricGroup on: self values) atRandom: aRandom)
]

{ #category : #accessing }
Graph >> size [
	"The size of a graph G=(V,E) is the number of vertices |V|, contrary to the more common convention of defining it as |E|."
	^ self nodes size
]

{ #category : #operations }
Graph >> subgraphInducedBy: aSet [
	"Answer the subgraph induces by aSet of vertices."
	| answer |
	answer := self copy.
	self edgesDo: [:each|
		((aSet includes: each key) and: [aSet includes: each value])
			ifTrue: [answer addEdge: each]].
	^ answer
]

{ #category : #operations }
Graph >> symmetric [
	"Answer the symmetric closure of the receiver."
	| answer |
	answer := self copy.
	self edgesDo: [:each | answer addEdge: (Association key: each value value: each key)].
	^ answer
]

{ #category : #operations }
Graph >> tensorProduct: aGraph [
	"Answer the tensor product (or direct graph product, categorical graph product, cardinal graph product, Kronecker graph product) of the receiver with the argument. This is a commutative operation (for unlabeled graphs)."
	| G |
	G := self class ordered.
	self do: [:x| aGraph do: [:y| G add: (x, y)]].
	self edgesDo: [:e1|
		aGraph edgesDo: [:e2|
			G addEdgeFrom: (e1 key, e2 key) to: (e1 value, e2 value)]].
	^ G
]

{ #category : #operations }
Graph >> topologicalSort [
	"Answer a topological sort of the receiver. This is a linear ordering of its vertices such that for each edge a -> b, a comes before to b in the ordering.
	This is Kahn's algorithm."
	| answer G S n |
	answer := OrderedCollection new.
	G := self copy.
	S := G nodes select: [:each| each inDegree = 0].
	[S notEmpty]
		whileTrue:
			[n := S anyOne.
			S remove: n.
			answer add: n.
			n neighbors do: [:m|
				n removeNeighbor: m.
				m inDegree = 0 ifTrue: [S add: m]]].
	G isEdgeless ifFalse: [^ self error: 'the graph has at least one cycle'].
	^ answer
]

{ #category : #operations }
Graph >> transposed [
	"Answer the transpose of the receiver. This is the graphs where edges a->b are inverted as b->a."
	| answer |
	answer := self copyEmpty.
	self edgesDo: [:each | answer addEdge: (Association key: each value value: each key)].
	^ answer
]

{ #category : #operations }
Graph >> union: aGraph [
	"Answer the graph whose vertices and edges are the union of the vertices and edges of the receiver and the argument."
	| answer |
	answer := self copy.
	aGraph do: [:each| answer add: each].
	aGraph edgesDo: [:each| answer addEdgeFrom: each key to: each value].
	^ answer
]

{ #category : #accessing }
Graph >> values [
	"Answer the set of vertices of the receievr ('values', as opposed to 'nodes' which are GraphNodes)."
	^ self nodes collect: [:each| each value]
]

{ #category : #comparing }
Graph >> ~ aGraph [
	"Answer true if the receiver is isomorphic to aGraph."
	| n G H |
	self isLabeled ifTrue: [self notYetImplemented].
	self species = aGraph species ifFalse: [^ false].
	(n := self size) = aGraph size ifFalse: [^ false].
	"we could insert some heuristic tests here, comparing easy-to-compute invariants"
	G := self asStandard.
	H := aGraph asStandard.
	(SymmetricGroup new: n) do: [:each| (G apply: each) = H ifTrue: [^ true]].
	^ false
]
