"
An implicit node has the edge structure represented within its value, and therefore forwards messages to the value to access edges.

To change the edge collection, you must send messages to the value.

Subclasses decide as to whether the value can yield a collection of edges more efficiently than iterating over them.
"
Class {
	#name : #ImplicitGraphNode,
	#superclass : #GraphNode,
	#category : #'Mathematics-Graphs-Parts'
}

{ #category : #'instance creation' }
ImplicitGraphNode class >> on: aValue collectionBlock: aBlock [
	^ImplicitCollectionGraphNode on: aValue collectionBlock: aBlock
]

{ #category : #'instance creation' }
ImplicitGraphNode class >> on: aValue iterator: anIterator [
	^ImplicitIteratorGraphNode on: aValue iterator: anIterator
]

{ #category : #'instance creation' }
ImplicitGraphNode class >> on: aValue iteratorBlock: iteratorBlock [
	^ImplicitIteratorGraphNode on: aValue iteratorBlock: iteratorBlock
]

{ #category : #'accessing edges' }
ImplicitGraphNode >> neighbors [
	^OrderedCollection accumulate: [:incBlock | self neighborsDo: incBlock]
]

{ #category : #'accessing edges' }
ImplicitGraphNode >> neighborsDo: aBlock [ 
	self neighbors do: aBlock
]
