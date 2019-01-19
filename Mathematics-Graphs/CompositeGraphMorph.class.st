Class {
	#name : #CompositeGraphMorph,
	#superclass : #Object,
	#category : #'Mathematics-Graphs-Morphic'
}

{ #category : #'as yet unclassified' }
CompositeGraphMorph >> addComponent: aGraphMorph [
	self addMorph: aGraphMorph proportionalWidth: 1
]

{ #category : #'as yet unclassified' }
CompositeGraphMorph >> componentsDo: aBlock [
	self submorphsDo: [:each| (each isKindOf: GraphMorph) ifTrue: [aBlock value: each]]
]

{ #category : #'as yet unclassified' }
CompositeGraphMorph >> dimension: anInteger [
	self componentsDo: [:each| each dimension: anInteger]
]

{ #category : #'as yet unclassified' }
CompositeGraphMorph >> edgeAt: anEdge [ 
	^ self nodeAt: anEdge ifAbsent: [self error: 'edge not found']
]

{ #category : #'as yet unclassified' }
CompositeGraphMorph >> edgeAt: anEdge ifAbsent: exceptionBlock [
	self componentsDo: [:each| (each edgeAt: anEdge ifAbsent: []) ifNotNil: [:edge| ^edge]].
	^ exceptionBlock value
]

{ #category : #'as yet unclassified' }
CompositeGraphMorph >> edgesAndLabelsDo: aBlock [ 
	self componentsDo: [:each| each edgesAndLabelsDo: aBlock]
]

{ #category : #'as yet unclassified' }
CompositeGraphMorph >> hideLabels [
	self componentsDo: [:each| each hideLabels]
]

{ #category : #'as yet unclassified' }
CompositeGraphMorph >> initialize [
	super initialize.
	self color: Color transparent.
	self morphExtent: 600 @ 300
]

{ #category : #'as yet unclassified' }
CompositeGraphMorph >> nodeAt: anObject [ 
	^ self nodeAt: anObject ifAbsent: [self error: 'node not found']
]

{ #category : #'as yet unclassified' }
CompositeGraphMorph >> nodeAt: anObject ifAbsent: exceptionBlock [
	self componentsDo: [:each| (each nodeAt: anObject ifAbsent: []) ifNotNil: [:node| ^node]].
	^ exceptionBlock value
]

{ #category : #'as yet unclassified' }
CompositeGraphMorph >> nodesDo: aBlock [
	self componentsDo: [:each| each nodesDo: aBlock]
]
