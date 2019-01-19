"
Abstract class for nodes that are held in a graph.

Each node holds on to a corresponding object that is the value of that node.

Subclasses add state/behaviour to represent edges in the graph.
"
Class {
	#name : #GraphNode,
	#superclass : #Object,
	#instVars : [
		'value'
	],
	#category : #'Mathematics-Graphs-Parts'
}

{ #category : #comparing }
GraphNode >> = anObject [
	"Comparison is delegated to the value of the node.
	Argument and receiver are reversed to dereference through other GraphNodes."
	^anObject = value
]

{ #category : #statistics }
GraphNode >> clusteringCoefficient [
	| links k |
	links := Set new.
	self neighborsDo: [:n1 |
		self neighborsDo: [:n2 |
			(n1 ~= n2 and: [n1 hasEdgeTo: n2])
				ifTrue: [links add: {n1 value. n2 value}]]].
	k := self neighbors size.
	^ links size / (k * (k - 1))
]

{ #category : #'accessing edges' }
GraphNode >> degree [
	"How many edges does this node have?"
	self subclassResponsibility
]

{ #category : #'testing edges' }
GraphNode >> hasEdgeTo: anObject [
	"Is there an edge from this node to anObject?"
	self subclassResponsibility
]

{ #category : #'testing edges' }
GraphNode >> hasLoop [
	^ self hasEdgeTo: self
]

{ #category : #comparing }
GraphNode >> hash [
	^value hash
]

{ #category : #'testing edges' }
GraphNode >> isLeaf [
	^self degree = 0
]

{ #category : #'testing edges' }
GraphNode >> isReflexive [
	^ self hasEdgeTo: self
]

{ #category : #'testing edges' }
GraphNode >> isSimple [
	^ self neighbors asSet size = self neighbors size and: [self hasLoop not]
]

{ #category : #'testing edges' }
GraphNode >> isSymmetric [
	self neighborsDo: [:each| (each hasEdgeTo: self) ifFalse: [^ false]].
	^ true
]

{ #category : #'testing edges' }
GraphNode >> isTransitive [
	self neighborsDo: [:each|
		each neighborsDo: [:other| (other hasEdgeTo: self) ifFalse: [^ false]]].
	^ true
]

{ #category : #enumerating }
GraphNode >> markDo: aBlock [
	"Visit each node in the graph once, applying aBlock.
	A node is only visited after at least one of its predecessors, but not necessarily after all the predecessors."
	| todo visited |
	todo := Set with: self.
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

{ #category : #'accessing edges' }
GraphNode >> neighbors [
	"Return a collection of nodes connected to outgoing edges."
	self subclassResponsibility
]

{ #category : #'accessing edges' }
GraphNode >> neighborsAndLabelsDo: aBlock [
	"Evaluate aBlock for each node connected to an outgoing edge, and the label on that edge (nil if no label)."
	"The default definition assumes no labels are present."
	self neighborsDo: [ :n | aBlock value: n value: nil]
]

{ #category : #'accessing edges' }
GraphNode >> neighborsDo: aBlock [
	"Evaluate aBlock for each node connected to an outgoing edge."
	self subclassResponsibility
]

{ #category : #printing }
GraphNode >> printOn: aStream [
	aStream nextPut: $[; print: value; nextPut: $]
]

{ #category : #operations }
GraphNode >> span [
	"Answer the spanning tree of the receiver."
	| tree |
	tree := RootedDigraph ordered.
	tree roots: (Set with: self).
	self markDo: [:each| tree add: each].
	^ tree
]

{ #category : #'accessing value' }
GraphNode >> value [
	^value
]

{ #category : #'accessing value' }
GraphNode >> value: anObject [
	value := anObject
]

{ #category : #enumerating }
GraphNode >> walkPre: preBlock post: postBlock [
	"Recursively walk the subtree rooted at me.  Apply preBlock to each node, then walk the subtree below node, then apply postBlock to the node."
	preBlock value: self.
	self neighborsDo: [ :child | child walkPre: preBlock post: postBlock].
	postBlock value: self
]
