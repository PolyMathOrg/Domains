"
A labeled explicit node associates a label with each neighbor, and a label with the node itself; i.e. nodes and edges are labeled.

When adding neighbors, the edge label must be given.
"
Class {
	#name : #LabeledExplicitGraphNode,
	#superclass : #ExplicitGraphNode,
	#instVars : [
		'label'
	],
	#category : #'Mathematics-Graphs-Parts'
}

{ #category : #comparing }
LabeledExplicitGraphNode >> = anObject [
	anObject class = self class ifTrue: [^ value = anObject value and: [label = anObject label]].
	^ super = anObject
]

{ #category : #'changing edges' }
LabeledExplicitGraphNode >> addNeighbor: aNode [
	self shouldNotImplement
]

{ #category : #'changing edges' }
LabeledExplicitGraphNode >> addNeighbor: aNode at: index [
	self shouldNotImplement
]

{ #category : #'changing edges' }
LabeledExplicitGraphNode >> addNeighbor: aNode at: index label: label [
	"pre: self isOrdered"
	outNeighbors at: index put: aNode -> label.
	^ aNode
]

{ #category : #'changing edges' }
LabeledExplicitGraphNode >> addNeighbor: aNode label: label [
	self flag: #fix.
	(outNeighbors includes: aNode) "inefficient"
		ifFalse: 
			[outNeighbors add: aNode -> label.
			aNode addInNeighborNoCheck: self].
	^aNode
]

{ #category : #'testing edges' }
LabeledExplicitGraphNode >> hasEdgeTo: anObject [ 
	^outNeighbors anySatisfy: [:assoc | assoc key = anObject]
]

{ #category : #accessing }
LabeledExplicitGraphNode >> label [
	^ label
]

{ #category : #accessing }
LabeledExplicitGraphNode >> label: anObject [
	label := anObject
]

{ #category : #'accessing edges' }
LabeledExplicitGraphNode >> labelOfEdgeTo: anObject [ 
	"Return the label associated with the edge to anObject; otherwise signal an error."

	^(outNeighbors detect: [:assoc | assoc key = anObject]) value
]

{ #category : #'accessing edges' }
LabeledExplicitGraphNode >> labelOfEdgeTo: anObject ifNone: aBlock [ 
	"Return the label associated with the edge to anObject; return the value of the block is no such edge exists."

	^(outNeighbors detect: [:assoc | assoc key = anObject]
		ifNone: [^aBlock value]) value
]

{ #category : #'accessing edges' }
LabeledExplicitGraphNode >> neighbors [
	^outNeighbors collect: [:assoc | assoc key]
]

{ #category : #'accessing edges' }
LabeledExplicitGraphNode >> neighborsAndLabelsDo: aBlock [ 
	"Evaluate aBlock for each node connected to an outgoing edge, and the label on that edge (nil if no label)."

	^outNeighbors do: [:assoc | aBlock value: assoc key value: assoc value]
]

{ #category : #'accessing edges' }
LabeledExplicitGraphNode >> neighborsDo: aBlock [ 
	^outNeighbors do: [:assoc | aBlock value: assoc key]
]

{ #category : #'changing edges' }
LabeledExplicitGraphNode >> removeNeighbor: aNode [ 
	outNeighbors remove: (outNeighbors detect: [:assoc | assoc key = aNode])
]
