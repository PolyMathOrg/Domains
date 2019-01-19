"
Implicit graphs nodes that access the collection of edges by evaluating a block.
"
Class {
	#name : #ImplicitCollectionGraphNode,
	#superclass : #ImplicitGraphNode,
	#instVars : [
		'collectionBlock'
	],
	#category : #'Mathematics-Graphs-Parts'
}

{ #category : #'instance creation' }
ImplicitCollectionGraphNode class >> on: aValue collectionBlock: aBlock [ 
	^ self new value: aValue; collectionBlock: aBlock
]

{ #category : #initialisation }
ImplicitCollectionGraphNode >> collectionBlock: aBlock [
	collectionBlock := aBlock
]

{ #category : #'accessing edges' }
ImplicitCollectionGraphNode >> degree [
	^self neighbors size
]

{ #category : #'testing edges' }
ImplicitCollectionGraphNode >> hasEdgeTo: anObject [ 
	^self neighbors includes: anObject
]

{ #category : #'accessing edges' }
ImplicitCollectionGraphNode >> neighbors [
	^collectionBlock value
]
