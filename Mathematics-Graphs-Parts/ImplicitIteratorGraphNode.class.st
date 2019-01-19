"
Implicit graph nodes that iterate over the collection of edges by evaluating the iterator.
"
Class {
	#name : #ImplicitIteratorGraphNode,
	#superclass : #ImplicitGraphNode,
	#instVars : [
		'iterator'
	],
	#category : #'Mathematics-Graphs-Parts'
}

{ #category : #'instance creation' }
ImplicitIteratorGraphNode class >> on: aValue iterator: anIterator [
	^(self new) value: aValue ; iterator: anIterator
]

{ #category : #'instance creation' }
ImplicitIteratorGraphNode class >> on: aValue iteratorBlock: iteratorBlock [
	^self on: aValue iterator: (Iterator on: iteratorBlock)
]

{ #category : #'accessing edges' }
ImplicitIteratorGraphNode >> degree [
	^iterator size
]

{ #category : #'testing edges' }
ImplicitIteratorGraphNode >> hasEdgeTo: anObject [
	^iterator includes: anObject
]

{ #category : #initialisation }
ImplicitIteratorGraphNode >> iterator: anIterator [
	iterator := anIterator
]

{ #category : #'accessing edges' }
ImplicitIteratorGraphNode >> neighborsDo: aBlock [
	iterator do: aBlock
]
