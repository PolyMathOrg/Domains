"
An explicit nodes stores the edges in a collection, an instance variable. The type of the collection varies as to whether the graph is ordered, of fixed arity, etc.

To change the edge collection, addNeighbor: and removeNeighbor: messages are supplied.

"
Class {
	#name : #ExplicitGraphNode,
	#superclass : #GraphNode,
	#instVars : [
		'inNeighbors',
		'outNeighbors'
	],
	#category : #'Mathematics-Graphs-Parts'
}

{ #category : #'instance creation' }
ExplicitGraphNode class >> arity: n [
	"Create a new ordered node with fixed arity n."
	^super new initializeFixed: n
]

{ #category : #'instance creation' }
ExplicitGraphNode class >> binary [
	"Create a new binary node."
	^super new initializeFixed: 2
]

{ #category : #'instance creation' }
ExplicitGraphNode class >> binary: value [
	"Create a new binary node, and given value."
	^super new initializeFixed: 2; value: value
]

{ #category : #'instance creation' }
ExplicitGraphNode class >> new [
	"Create a new unordered node."
	^super new initializeUnordered
]

{ #category : #'instance creation' }
ExplicitGraphNode class >> newOn: value [
	"Create a new unordered node, and given value."
	^super new initializeUnordered; value: value
]

{ #category : #'instance creation' }
ExplicitGraphNode class >> on: value arity: n [
	"Create a new ordered node with fixed arity n, and given value."
	^super new initializeFixed: n; value: value
]

{ #category : #'instance creation' }
ExplicitGraphNode class >> ordered [
	"Create a new ordered node."
	^super new initializeOrdered
]

{ #category : #'instance creation' }
ExplicitGraphNode class >> ordered: value [
	"Create a new ordered node, and given value."
	^super new initializeOrdered; value: value
]

{ #category : #private }
ExplicitGraphNode >> addInNeighborNoCheck: aNode [
	^ inNeighbors add: aNode
]

{ #category : #'changing edges' }
ExplicitGraphNode >> addNeighbor: aNode [ 
	outNeighbors add: aNode.
	aNode addInNeighborNoCheck: self.
	^ aNode
"	self flag: #fix.
	(outNeighbors includes: aNode)
		ifFalse: 
			[outNeighbors add: aNode.
			aNode addInNeighborNoCheck: self].
	^aNode"
]

{ #category : #'changing edges' }
ExplicitGraphNode >> addNeighbor: aNode at: index [ 
	"pre: self isOrdered"
	outNeighbors at: index put: aNode.
	aNode addInNeighborNoCheck: self.
	^aNode
]

{ #category : #copying }
ExplicitGraphNode >> copy [
	^ super copy setNeighbors: outNeighbors copy; setInNeighbors: inNeighbors copy
]

{ #category : #'accessing edges' }
ExplicitGraphNode >> degree [
	"If I am in my neighborhood, don't count the loop edge"

	^ (outNeighbors includes: self) 
		ifTrue: [outNeighbors size - 1]
		ifFalse: [outNeighbors size]
]

{ #category : #'testing edges' }
ExplicitGraphNode >> hasEdgeTo: anObject [ 
	^outNeighbors includes: anObject
]

{ #category : #'accessing edges' }
ExplicitGraphNode >> inDegree [
	"If I am in my neighborhood, don't count the loop edge"
	(inNeighbors includes: self)
		ifTrue: [^ inNeighbors size - 1]
		ifFalse: [^ inNeighbors size]

]

{ #category : #'accessing edges' }
ExplicitGraphNode >> inNeighbors [
	^inNeighbors
]

{ #category : #initialize }
ExplicitGraphNode >> initializeFixed: arity [ 
	outNeighbors := Array new: arity.
	inNeighbors := Bag new
]

{ #category : #initialize }
ExplicitGraphNode >> initializeOrdered [
	outNeighbors := OrderedCollection new.
	inNeighbors := Bag new
]

{ #category : #initialize }
ExplicitGraphNode >> initializeUnordered [
	outNeighbors := Bag new.
	inNeighbors := Bag new
]

{ #category : #testing }
ExplicitGraphNode >> isAnExtremity [
	^ self isFinal | self isInitial | self isExtremal
]

{ #category : #testing }
ExplicitGraphNode >> isExtremal [
	"o<-->..."
	^ self degree = 1 and: [self inNeighbors asSet = self neighbors asSet]
]

{ #category : #testing }
ExplicitGraphNode >> isFinal [
" o<--..."
	^ self inDegree = 1 and: [self degree = 0]
]

{ #category : #testing }
ExplicitGraphNode >> isInitial [
	"o-->..."
	^ self inDegree = 0 and: [self degree = 1]
]

{ #category : #testing }
ExplicitGraphNode >> isMiddle [
	"..--o--..."
	^ (self inDegree + self degree between: 2 and: 4)
		and: [(self inNeighbors ñ self neighbors) size = 2]
]

{ #category : #testing }
ExplicitGraphNode >> isOrdered [
	^outNeighbors isSequenceable
]

{ #category : #'accessing edges' }
ExplicitGraphNode >> neighbors [
	^outNeighbors
]

{ #category : #'accessing edges' }
ExplicitGraphNode >> neighborsDo: aBlock [ 
	outNeighbors do: aBlock
]

{ #category : #'changing edges' }
ExplicitGraphNode >> removeInNeighbor: aNode [ 
	^ inNeighbors remove: aNode ifAbsent: [aNode]
]

{ #category : #'changing edges' }
ExplicitGraphNode >> removeNeighbor: aNode [
	aNode removeInNeighbor: self.
	^outNeighbors remove: aNode
]

{ #category : #private }
ExplicitGraphNode >> setInNeighbors: aCollection [
	inNeighbors := aCollection
]

{ #category : #private }
ExplicitGraphNode >> setNeighbors: aCollection [
	outNeighbors := aCollection
]

{ #category : #'accessing edges' }
ExplicitGraphNode >> strictInNeighbors [
	(inNeighbors includes: self) ifTrue: [^ inNeighbors copyWithout: self].
	^ inNeighbors
]

{ #category : #'accessing edges' }
ExplicitGraphNode >> strictNeighbors [
	(outNeighbors includes: self) ifTrue: [^ outNeighbors copyWithout: self].
	^ outNeighbors
]
