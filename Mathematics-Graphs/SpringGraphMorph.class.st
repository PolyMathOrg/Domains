Class {
	#name : #SpringGraphMorph,
	#superclass : #GraphMorph,
	#category : #'Mathematics-Graphs-Morphic'
}

{ #category : #'event handling' }
SpringGraphMorph >> allowSubmorphExtraction [
	" allow extraction so submorphs can be grabbed and dragged to a new position.
	  usefull to rearrange the vertices manually"
	^ true
]

{ #category : #stepping }
SpringGraphMorph >> approachComponents [
	| componentsDesiredDistance |
	(components isNil or: [components size < 2])
		ifTrue: [^ self].
	componentsDesiredDistance := 1.
	components do: [:each|
		components do: [:other|
			each == other
				ifFalse:
					[| source target f currentDistance diff delta |
					source := each atRandom.
					target := other atRandom.
					(currentDistance := (diff := source x + source dx - target x - target dx) norm) > componentsDesiredDistance
						ifTrue:
							[f := (componentsDesiredDistance - currentDistance) asFloat / (currentDistance * 4).
							delta := diff * f / 2.
							"target dx: target dx - delta."
							source dx: source dx + (delta/other size)]]]]
]

{ #category : #stepping }
SpringGraphMorph >> aproachConnectedNodes [
	self edgesDo: [:each| each approachNodes]
]

{ #category : #accessing }
SpringGraphMorph >> desiredDistance: aNumber [
	^ self edgesDo: [:each| each desiredDistance: aNumber]
]

{ #category : #private }
SpringGraphMorph >> edgeClass [
	^ SpringEdgeMorph
]

{ #category : #accessing }
SpringGraphMorph >> graph: aGraph [
	| morph desiredDistance |
	super graph: aGraph.
	(aGraph isKindOf: RootedDigraph)
		ifTrue: [morph := nodeToMorph at: aGraph rootNode.
				morph morphAlign: morph morphBounds center with: self morphExtent // 2].
	aGraph size < 100
		ifTrue: [desiredDistance := (self morphLocalBounds area / (aGraph radius min: 10) / 2) sqrt.
			components := graph components asArray collect: [:each| each asArray collect: [:node| nodeToMorph at: node]]]
		ifFalse:
			[desiredDistance := 10.
			components := nil].
	self edgesDo: [:each| each desiredDistance: desiredDistance "/ each source node degree sqrt"]
]

{ #category : #private }
SpringGraphMorph >> nodeClass [
	^ SpringNodeMorph
]

{ #category : #'event handling' }
SpringGraphMorph >> scaleEdgesBy: aNumber [
	self edgesDo: [:each| each desiredDistance: each desiredDistance * aNumber].
	self startStepping
]

{ #category : #stepping }
SpringGraphMorph >> separateAllNodes [
	self nodesDo: [:each | each separateFromAllNodes]
]

{ #category : #stepping }
SpringGraphMorph >> step [
	| maxDelta |
	self nodesDo: [:each| each dampBy: 1.1]. "damping"
	self aproachConnectedNodes; separateAllNodes; "approachComponents;" alignToCenter.
	maxDelta := 0.
	self nodesDo: [:each| maxDelta := maxDelta max: each doMove].
	self edgesDo: [:each| each adjustBounds].
	self redrawNeeded.
	maxDelta < 0.1 ifTrue: [self stopStepping]
]
