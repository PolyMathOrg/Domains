"
Directed graphs with some distinguished vertices that we call 'roots'.

Structure:
 roots 		Set of root objects

"
Class {
	#name : #RootedDigraph,
	#superclass : #Digraph,
	#instVars : [
		'roots'
	],
	#category : #'Mathematics-Graphs'
}

{ #category : #'example graphs' }
RootedDigraph class >> exampleDAG [
	"RootedGraph exampleDAG."
	| d |
	d := self unordered.
	d addRoot: #r1.
	d addRoot: #r2.
	d addEdge: #r1 -> #n1.
	d addEdge: #r1 -> #n2.
	d addEdge: #r2 -> #n2.
	d addEdge: #n1 -> #n3.
	d addEdge: #n2 -> #n3.
	^d
]

{ #category : #'example graphs' }
RootedDigraph class >> exampleForest [
	"RootedGraph exampleForest"
	^self unordered roots: (Set with: Number with: Stream) children: [ :class | class subclasses]
]

{ #category : #'example graphs' }
RootedDigraph class >> exampleImplicitLargeTree [
	"RootedGraph exampleImplicitLargeTree"
	^(self
		implicitCollection:
			[ :class |
				class == Class
					ifTrue: [#()]
					ifFalse: [class subclasses asSortedCollection: [ :x :y | x name < y name]]]) 		buildFromRoots: (Array with: Object)
]

{ #category : #'example graphs' }
RootedDigraph class >> exampleImplicitSmallTree [
	"RootedGraph exampleImplicitSmallTree"
	^(self implicitCollection: [ :class | class subclasses]) buildFromRoots: (Set with: Number)
]

{ #category : #'example graphs' }
RootedDigraph class >> exampleLargeTree [
	"RootedGraph exampleLargeTree"
	^self ordered roots: (Array with: Object) children:
		[ :class | class == Class
					ifTrue: [#()]
					ifFalse: [class subclasses asSortedCollection: [ :x :y | x name < y name]]]
]

{ #category : #'example graphs' }
RootedDigraph class >> exampleMediumLabelledTree [
	"RootedGraph exampleMediumLabelledTree"
	^self unorderedLabeled
		roots: (Set with: Collection)
		children: [ :class | class subclasses]
		label: [ :src :trg |
				trg isVariable
					ifTrue: [trg isBits ifTrue: [#variableByte] ifFalse: [#variable]]
					ifFalse: [#normal]]
]

{ #category : #'example graphs' }
RootedDigraph class >> exampleMediumTree [
	^self unordered roots: (Set with: Collection) children: [ :class | class subclasses]
]

{ #category : #'example graphs' }
RootedDigraph class >> exampleMediumTree2 [
	^self unordered roots: (Set with: Collection) children: [ :class | class subclasses]
]

{ #category : #'example graphs' }
RootedDigraph class >> exampleSmallLabelledTree [
	"RootedGraph exampleSmallLabelledTree"
	^self unorderedLabeled
		roots: (Set with: Number)
		children: [ :class | class subclasses]
		label: [ :src :trg | trg category]
]

{ #category : #'example graphs' }
RootedDigraph class >> exampleSmallLabelledTree2 [
	"RootedGraph exampleSmallLabelledTree2"
	^self unorderedLabeled
		roots: (Set with: Magnitude)
		children: [ :class | class subclasses]
		label: [ :src :trg |
				trg isVariable
					ifTrue: [trg isBits ifTrue: [#variableByte] ifFalse: [#variable]]
					ifFalse: [#normal]]
]

{ #category : #'example graphs' }
RootedDigraph class >> exampleSmallTree [
	"RootedGraph exampleSmallTree"
	^self unordered roots: (Set with: Number) children: [ :class | class subclasses]
]

{ #category : #'example graphs' }
RootedDigraph class >> exampleSmallTree2 [
	"RootedGraph exampleSmallTree2"
	^self unordered roots: (Set with: Magnitude) childrenMsg: #subclasses
]

{ #category : #adding }
RootedDigraph >> addEdgeFrom: source to: target [
	super addEdgeFrom: source to: target.
	roots remove: target ifAbsent: []
]

{ #category : #adding }
RootedDigraph >> addEdgeFrom: source to: target label: label [
	super addEdgeFrom: source to: target label: label.
	roots remove: target ifAbsent: []
]

{ #category : #adding }
RootedDigraph >> addRoot: anObject [
	"Add anObject as a root of the graph."
	| node |
	node := self add: anObject.
	roots add: node value.
	^ node
]

{ #category : #enumerating }
RootedDigraph >> breadthFirstDo: aBlock [
	"Evaluate aBlock for each set of nodes at a given depth in the graph.
	A node is at depth n if the longest path to that node from a root has n steps.
	pre: self isCyclic not"

	| df current |
	df := self frontier.
	[current := df frontier copy.
	current isEmpty] whileFalse:
		[aBlock value: current.
		df removeAll: current]
]

{ #category : #adding }
RootedDigraph >> buildFromRoots: rootCollection [
	"Build the graph with given roots.
	The nodes should all be ImplicitGraphNodes, or have outgoing edges attached."
	self roots: rootCollection.
	self markDo: [ :junk ]
]

{ #category : #enumerating }
RootedDigraph >> collect: aBlock [
	"Answer a new graph like the receiver but with vertices values mapped by aBlock.
	Note that aBlock is evaluated on the nodes, not the values."
	| answer |
	answer := super copyEmpty.
	answer roots: (roots collect: aBlock).
	self do: [:each| answer add: (aBlock value: each)].
	self edgesDo: [:each| answer addEdgeFrom: (aBlock value: each key) to: (aBlock value: each value)].
	^ answer
]

{ #category : #enumerating }
RootedDigraph >> collect: aBlock labels: labelBlock [
	"Answer a new graph like the receiver but with vertices values mapped by aBlock.
	Note that aBlock is evaluated on the nodes, not the values."
	| answer |
	answer := super copyEmpty.
	self rootNodes do: [:each| answer addRoot: (aBlock value: each)].
	self do: [:each| answer add: (aBlock value: each)].
	self edgesAndLabelsDo: [:each :label| answer addEdgeFrom: (aBlock value: each key) to: (aBlock value: each value) label: (labelBlock value: label)].
	^ answer
]

{ #category : #copying }
RootedDigraph >> copyEmpty [
	"Return a new graph of the same type, with the same roots, but no edges."
	^ super copyEmpty roots: roots copy asSet
]

{ #category : #operations }
RootedDigraph >> depthList [
	"Partitions the DAG, returning a SequenceableCollection of Sets of nodes in the graph.  Element n in the SequenceableCollection is the Set of nodes in the graph reachable in n-1 steps by the longest route from a root."
	^OrderedCollection accumulate: [ :incBlock | self breadthFirstDo: incBlock]
]

{ #category : #initialization }
RootedDigraph >> findRoots [
	"Find all nodes that are not the targets of an edge and make them the roots."
	roots := self values.
	self nodesDo: [:node| node neighborsDo: [:n| roots remove: n value ifAbsent: []]]
]

{ #category : #enumerating }
RootedDigraph >> frontier [
	"Return a DAGFrontier object, capable of iterating over this DAG."
	^ DAGFrontier on: self
]

{ #category : #initialization }
RootedDigraph >> initialize [
	super initialize.
	roots := Set new
]

{ #category : #testing }
RootedDigraph >> isCyclic [
	"Is the graph cyclic?"

	| frontier remaining |
	frontier := self rootNodes.
	"Build a Bag of non-root nodes, each node once in the Bag for every predecessor."
	remaining := Bag new.
	nodes do: [:node | remaining addAll: node neighbors].
	
	[| next |
	next := frontier anyIfNone: [^remaining isEmpty not].
	frontier remove: next.
	next neighborsDo: 
			[:neighbor | 
			(remaining remove: neighbor) = 0 ifTrue: [frontier add: neighbor]]] 
			repeat
]

{ #category : #testing }
RootedDigraph >> isEmpty [
	"Answer whether the receiver contains any elements."

	^roots isEmpty
]

{ #category : #testing }
RootedDigraph >> isTree [
	"Is the graph a tree (more accurately, a forest)?
	It is if every node has at most one predecessor."
	| visited |
	visited := Set new.
	nodes do: [ :node |
		node neighborsDo: [ :neighbor |
			(visited includes: neighbor) ifTrue: [^false].
			visited add: neighbor]].
	^true
]

{ #category : #enumerating }
RootedDigraph >> markDo: aBlock [
	"Visit each node in the graph once, applying aBlock.
	A node is only visited after at least one of its predecessors, but not necessarily after all the predecessors."
	| todo visited |
	todo := self rootNodes as: Set.
	visited := Set new.
	[todo isEmpty] whileFalse:
		[| node |
		node := todo anyOne.
		visited add: node.
		aBlock value: node.
		node neighborsDo:
			[ :child |
				(visited includes: child)
					ifFalse: [todo add: child]].
		todo remove: node]
]

{ #category : #enumerating }
RootedDigraph >> preOrderDo: aBlock [ 
	"Walk the graph, evaluating aBlock for each node.  Evaluate each node before its successors, but in no particular order when there is a choice.
	pre: self isCyclic not"

	| frontier remaining |
	frontier := self rootNodes.
	"Build a Bag of non-root nodes, each node once in the Bag for every predecessor."
	remaining := Bag new.
	nodes do: [:node | remaining addAll: node neighbors].
	
	[| next |
	next := frontier anyIfNone: [^self].
	aBlock value: next.
	frontier remove: next.
	next neighborsDo: 
			[:neighbor | 
			(remaining remove: neighbor) = 0 ifTrue: [frontier add: neighbor]]] 
			repeat
]

{ #category : #operations }
RootedDigraph >> reduce [
	"Remove all redundant edges to form the transitive reduction.

	Based on Algorithm 4 in 'An Algorithm for Finding a Minimum Equivalent Graph of a Digraph', by D. M. Moyles and G. L. Thompson, JACM 16(3), July 1969, pp455-60 (with obvious simplifications for acyclic graphs)."
	
	self rootNodes do: [ :root | self reduceStep: root with: OrderedCollection new]
]

{ #category : #operations }
RootedDigraph >> reduceSlow [
	"Remove all redundant edges to form the transitive reduction.

	Based on Algorithm 4 in 'An Algorithm for Finding a Minimum Equivalent Graph of a Digraph', by D. M. Moyles and G. L. Thompson, JACM 16(3), July 1969, pp455-60 (with obvious simplifications for acyclic graphs).
	
	This version sometimes builds huge sets!"
	
	| seqSet |
	seqSet := Set accumulate: [ :incBlock |
				self rootNodes do: [ :root | incBlock value: (Array with: root)]].

	[seqSet isEmpty] whileFalse:
		[| newSeqSet |
"Transcript show: seqSet size printString ; cr."
		newSeqSet := Set new.
		seqSet do: [ :seq || tail |
			tail := seq last.
			tail neighborsDo: [ :neighbor |
				seq do: [ :node |
					(node ~= tail and: [node hasEdgeTo: neighbor])
						ifTrue: [
"Transcript show: node printString, ' -> ', neighbor printString ; cr."
								self removeEdgeFrom: node to: neighbor]].
				newSeqSet add: (seq copyWith: neighbor)]].
		seqSet := newSeqSet]
]

{ #category : #operations }
RootedDigraph >> reduceStep: node with: sofar [ 
	node degree = 0 ifTrue: [^self].
	node neighbors copy do: 
			[:succ | 
			sofar 
				do: [:done | (done hasEdgeTo: succ) ifTrue: [self removeEdgeFrom: done to: succ]].
			sofar addLast: node.
			self reduceStep: succ with: sofar.
			sofar removeLast]
]

{ #category : #removing }
RootedDigraph >> removeAllFrom: aNode [ 
	"Remove the subtree below aNode (and associated edges), excluding aNode itself.
	Note that nodes are removed from the graph without being sent any messages."

	aNode walkPre: [:junk | ]
		post: 
			[:child | 
			child == aNode 
				ifTrue: [aNode neighbors copy do: [:n | aNode removeNeighbor: n]]
				ifFalse: [self remove: child]]
]

{ #category : #accessing }
RootedDigraph >> root [
	"pre: roots size = 1"
	^ roots anyOne
]

{ #category : #accessing }
RootedDigraph >> rootNode [
	"return the GraphNode for the root.
	pre: roots size = 1"
	^self nodeAt: roots anyOne
]

{ #category : #accessing }
RootedDigraph >> rootNodes [
	"Return the GraphNodes for the roots."
	^roots collect: [ :root | self nodeAt: root]
]

{ #category : #accessing }
RootedDigraph >> roots [
	^ roots
]

{ #category : #initialization }
RootedDigraph >> roots: aCollection [
	roots := aCollection asSet.
	roots do: [:each| self add: each]
]

{ #category : #adding }
RootedDigraph >> roots: rootNodes children: aBlock [
	"Build the graph with given rootNodes.
	Evaluate aBlock for each node to obtain a Collection of its children."
	^self roots: rootNodes childrenGenerator:
		[ :node | [ :iterationBlock | (aBlock value: node) do: iterationBlock]]
]

{ #category : #adding }
RootedDigraph >> roots: rootNodes children: aBlock label: labelBlock [
	"Build the graph with given rootNodes.
	Evaluate aBlock for each node to obtain a Collection of its children."
	^self
		roots: rootNodes 
		childrenGenerator: [ :node | [ :iterationBlock | (aBlock value: node) do: iterationBlock]]
		label: labelBlock
]

{ #category : #adding }
RootedDigraph >> roots: rootNodes childrenGenerator: aBlock [
	"Build the graph with given rootNodes.
	Evaluate aBlock for each node to obtain an iterator over a Collection of its children."
	^self roots: rootNodes childrenGenerator: aBlock label: nil
]

{ #category : #adding }
RootedDigraph >> roots: rootNodes childrenGenerator: aBlock label: labelBlock [
	"Build the graph with given rootNodes.
	Evaluate aBlock for each node to obtain an iterator over a Collection of its children.
	Evaluate labelBlock (if not nil) for each node and child to obtain a label for the edge."
	| todo |
	self roots: rootNodes.
	todo := rootNodes asSet copy.
	[todo isEmpty] whileFalse:
		[| node |
		node := todo anyOne.
		(aBlock value: node) value:
			[ :child |
				(self includes: child) ifFalse: [todo add: child].
				labelBlock isNil
					ifTrue: [self addEdgeFrom: node to: child]
					ifFalse: [self addEdgeFrom: node to: child label: (labelBlock value: node value: child)]].
			todo remove: node].
	^self
]

{ #category : #adding }
RootedDigraph >> roots: rootNodes childrenLabelGenerator: aBlock [
	"Build the graph with given rootNodes.
	Evaluate aBlock for each node to obtain an iterator over a Collection of its children and labels."
	| todo |
	self roots: rootNodes.
	todo := rootNodes asSet copy.
	[todo isEmpty] whileFalse:
		[| node |
		node := todo anyOne.
		(aBlock value: node) value:
			[ :child :label |
				(self includes: child) ifFalse: [todo add: child].
				self addEdgeFrom: node to: child label: label].
			todo remove: node].
	^self
]

{ #category : #adding }
RootedDigraph >> roots: rootNodes childrenMsg: msg [
	"Build the graph with given rootNodes.
	Send msg to each node to obtain a Collection of its children."
	^self roots: rootNodes childrenGenerator:
		[ :node | [ :iterationBlock | (node perform: msg) do: iterationBlock]]
]

{ #category : #testing }
RootedDigraph >> test [
	^ #[1 2 3 4]
]

{ #category : #enumerating }
RootedDigraph >> walkPre: preBlock post: postBlock [
	"Recursively walk the tree(s).  Apply preBlock to each node, then walk the subtree below node, then apply postBlock to the node."
	self rootNodes do: [ :root | root walkPre: preBlock post: postBlock]
]
