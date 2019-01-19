"
A GraphMorph is composed of nodes and edges (GraphNodeMorph and GraphEdgeMorph or subclasses). Subclasses of GraphMorph implement different layouts.

Examples:
	| A4 a b |
	A4 := AlternatingGroup on: (1 to: 4).
	a := Permutation image: (2,1,4,3).
	b := Permutation image: (2,3,1,4).
	(A4 cayleyGraphMorph: {a.b}) openInWorld.

	| R W |
	R := RootSystem example1.
	W := R dual weylGroup.
	(W cayleyGraphMorph: {W atRandom. W atRandom}) openInWorld

	| G |
	G := Graph exampleImplicitGraph.
	SpringGraphMorph new graph: G; openInWorld 

	| G |
	G := RootedDigraph exampleSmallLabelledTree.
	SpringGraphMorph new graph: G; openInWorld 

"
Class {
	#name : #GraphMorph,
	#superclass : #Object,
	#instVars : [
		'graph',
		'nodeToMorph',
		'edgeToMorph',
		'focusNode',
		'dimension',
		'lastMousePosition',
		'components'
	],
	#category : #'Mathematics-Graphs-Morphic'
}

{ #category : #'event handling' }
GraphMorph >> acceptDroppingMorph: aMorph event: evt [
	(aMorph isKindOf: self nodeClass)
		ifTrue: [self addMorph: aMorph.
				"self focusOn: aMorph node".
				^ self startStepping].
	^ super acceptDroppingMorph: aMorph event: evt
]

{ #category : #private }
GraphMorph >> addEdge: anEdge [
	^ self addEdge: anEdge label: nil
]

{ #category : #private }
GraphMorph >> addEdge: anEdge label: label [ 
	| src dest |
	src := self graph nodeAt: anEdge key.
	dest := self graph nodeAt: anEdge value.
	^ self privateAddEdgeFrom: src to: dest label: label
]

{ #category : #private }
GraphMorph >> addNode: aGraphNode [ 
	| morph |
	(nodeToMorph includesKey: aGraphNode)
		ifTrue: [^ nodeToMorph at: aGraphNode].
	morph := self nodeClass new node: aGraphNode.
	morph dimension: dimension.
	nodeToMorph at: aGraphNode put: morph.
	morph morphPosition: self morphWidth asInteger atRandom @ self morphHeight asInteger atRandom.
	self addMorph: morph.
"	aGraphNode
		neighborsAndLabelsDo: [:each :label|
			self addNode: each.
			self privateAddEdgeFrom: aGraphNode to: each label: label]."
	^ morph
]

{ #category : #stepping }
GraphMorph >> alignToCenter [
	| centerOfMass delta |
	centerOfMass := nodeToMorph anyOne x * 0. "0@0"
	self nodesDo: [:each| centerOfMass := centerOfMass + each x].
	centerOfMass := centerOfMass / graph size.
	centerOfMass isZero ifTrue: [^ self].
	delta := centerOfMass negated.
	self nodesDo: [:each| each translateBy: delta]
]

{ #category : #'event handling' }
GraphMorph >> allowSubmorphExtraction [
	" allow extraction so submorphs can be grabbed and dragged to a new position.
	  usefull to rearrange the vertices manually"
	^ true
]

{ #category : #layout }
GraphMorph >> clearAll [
	self clearEdges.
	self clearNodes.
	
]

{ #category : #layout }
GraphMorph >> clearEdges [
	self edgesDo: [:edgeMorph| edgeMorph delete].
	self initializeEdgeToMorph
]

{ #category : #layout }
GraphMorph >> clearNodes [
	self nodesDo: [:nodeMorph | nodeMorph delete].
	self initializeNodeToMorph
]

{ #category : #accessing }
GraphMorph >> dimension [
	^ dimension
]

{ #category : #accessing }
GraphMorph >> dimension: anInteger [
	dimension := anInteger.
	self nodesDo: [:each| each dimension: anInteger].
	self startStepping
]

{ #category : #accessing }
GraphMorph >> edgeAt: anEdge [
	^ self edgeAt: anEdge ifAbsent: [self error: 'edge not found']
]

{ #category : #accessing }
GraphMorph >> edgeAt: anEdge ifAbsent: exceptionBlock [
	| edge |
	edge := anEdge key -> anEdge value.
	graph isDirected ifFalse: [edge := edge as: MutualAssociation].
	^ edgeToMorph at: edge ifAbsent: exceptionBlock
]

{ #category : #private }
GraphMorph >> edgeClass [
	^ GraphEdgeMorph
]

{ #category : #accessing }
GraphMorph >> edges [
	^ Iterator on: self performing: #edgesDo:
]

{ #category : #enumerating }
GraphMorph >> edgesAndLabelsDo: aBlock [
	graph edgesAndLabelsDo: [:each :label| aBlock value: (self edgeAt: each) value: label]
]

{ #category : #enumerating }
GraphMorph >> edgesDo: aBlock [
	edgeToMorph do: aBlock
]

{ #category : #accessing }
GraphMorph >> focusNode [
	^focusNode
]

{ #category : #accessing }
GraphMorph >> focusOn: aNode [
	focusNode := graph nodeAt: aNode.
	nodeToMorph at: focusNode ifPresent: [:aMorph| aMorph freeze].
	self startStepping
]

{ #category : #accessing }
GraphMorph >> graph [
	^ graph
]

{ #category : #accessing }
GraphMorph >> graph: aGraph [
	self clearAll.
	graph := aGraph.
	graph nodesDo: [:each| self addNode: each].
	graph edgesAndLabelsDo: [:each :label| self addEdge: each label: label].
	graph
		when: #addNode: send: #addNode: to: self;
		when: #addEdge: send: #addEdge: to: self;
		when: #removeNode: send: #removeNode: to: self;
		when: #removeEdge: send: #removeEdge: to: self.
	(graph isKindOf: RootedDigraph)
		ifTrue: [self focusOn: graph rootNode]
		ifFalse: [self focusOn: graph anyOne]
]

{ #category : #'event handling' }
GraphMorph >> handlesMouseDown: aMouseButtonEvent [
	"Do I want to receive mouseDown events (mouseDown:, mouseMove:, mouseUp:)?"
	^true
]

{ #category : #accessing }
GraphMorph >> hideLabels [
	self nodesDo: [:each| each hideLabel].
	self edgesDo: [:each| each hideLabel]
]

{ #category : #initialization }
GraphMorph >> initialize [
	super initialize.
	self morphExtent: 300 @ 300.
	self color: Color transparent.
	self initializeNodeToMorph.
	self initializeEdgeToMorph.
	dimension := 3
]

{ #category : #initialization }
GraphMorph >> initializeEdgeToMorph [
	edgeToMorph := Dictionary new
]

{ #category : #initialization }
GraphMorph >> initializeNodeToMorph [
	nodeToMorph := Dictionary new
]

{ #category : #'event handling' }
GraphMorph >> mouseButton1Down: aMouseButtonEvent localPosition: localEventPosition [
	super mouseButton1Down: aMouseButtonEvent localPosition: localEventPosition.
	lastMousePosition := localEventPosition
]

{ #category : #'event handling' }
GraphMorph >> mouseMove: aMouseMoveEvent localPosition: localEventPosition [
	lastMousePosition isNil
		ifFalse:
			[aMouseMoveEvent shiftPressed
				ifTrue:
					[| bounds d |
					bounds := self morphLocalBounds.
					d := (localEventPosition dist: lastMousePosition) / (bounds width min: bounds height).
					localEventPosition y >= lastMousePosition y ifTrue: [d := d negated].
					self scaleEdgesBy: (2.0 raisedTo: d)]
				ifFalse: [self rotateNodesBy: lastMousePosition - localEventPosition]].
	lastMousePosition := localEventPosition
]

{ #category : #accessing }
GraphMorph >> nodeAt: anObject [
	^ nodeToMorph at: anObject
]

{ #category : #accessing }
GraphMorph >> nodeAt: anObject ifAbsent: exceptionBlock [
	^ nodeToMorph at: anObject ifAbsent: exceptionBlock
]

{ #category : #private }
GraphMorph >> nodeClass [
	^ GraphNodeMorph
]

{ #category : #enumerating }
GraphMorph >> nodesDo: aBlock [
	nodeToMorph do: aBlock
]

{ #category : #accessing }
GraphMorph >> origin [
	^ (nodeToMorph at: (focusNode ifNil: [^ self morphExtent // 2])) morphBounds center
]

{ #category : #accessing }
GraphMorph >> perturbate: n [
	self nodesDo: [:each| each perturbate: n].
	self startStepping
]

{ #category : #private }
GraphMorph >> privateAddEdgeFrom: source to: target label: label [
	| edge morph |
	edge := source -> target.
	graph isDirected ifFalse: [edge := edge as: MutualAssociation].
	(edgeToMorph includesKey: edge)
		ifTrue: [^ (edgeToMorph at: edge) incrementMultiplicity].
	morph := self edgeClass new.
	edgeToMorph at: edge put: morph.
	morph source: (nodeToMorph at: source); target: (nodeToMorph at: target).
	morph label: label.
	graph isDirected ifTrue: [morph showArrowHead] ifFalse: [morph hideArrowHead].
	self addMorphBack: morph.
	^ morph
]

{ #category : #geometry }
GraphMorph >> privateExtent: aPoint [
	^ (super privateExtent: aPoint) ifTrue: [self startStepping]; yourself
]

{ #category : #private }
GraphMorph >> privateRemoveEdgeFrom: source to: target label: label [ 
	| edge |
	edge := source -> target.
	graph isDirected ifFalse: [edge := edge as: MutualAssociation].
	(edgeToMorph removeKey: edge ifAbsent: [^ self]) delete
]

{ #category : #private }
GraphMorph >> removeEdge: anEdge [ 
	^ self removeEdge: anEdge label: nil
]

{ #category : #private }
GraphMorph >> removeEdge: anEdge label: label [ 
	^ self privateRemoveEdgeFrom: anEdge key to: anEdge value label: label
]

{ #category : #'event handling' }
GraphMorph >> rotateNodesBy: aPoint [
	| xSpeed ySpeed |
	self dimension < 3 ifTrue: [^ self].
	xSpeed := Float pi / self morphLocalBounds width.
	ySpeed := Float pi / self morphLocalBounds height.
"	self dimension = 2 ifTrue: [self nodesDo: [:each| |p pp| p := each x. pp := p x @ p y rotatedBy: aPoint y * ySpeed negated + (aPoint x * xSpeed). each x: (pp x, pp y)]. ^ self]."
	self nodesDo: [:each| | p xz yz |
		p := each x.
		xz := p x @ p z.
		xz := xz rotatedBy: aPoint x * xSpeed.
		yz := p y @ xz y.
		yz := yz rotatedBy: aPoint y * ySpeed.
		p := (xz x, yz x, yz y).
		each x: p.
		each dx: p * 0. "optimization, dont rotate the velocities"].
	self startStepping
]

{ #category : #stepping }
GraphMorph >> step [
	| maxDelta |
	self nodesDo: [:each| each dampBy: 1.1]. "damping"
	self alignToCenter.
	maxDelta := 0.
	self nodesDo: [:each| maxDelta := maxDelta max: each doMove].
	self edgesDo: [:each| each adjustBounds].
	self redrawNeeded.
	maxDelta < 0.1 ifTrue: [self stopStepping]
]

{ #category : #stepping }
GraphMorph >> stepTime [
	^ 0
]

{ #category : #stepping }
GraphMorph >> wantsSteps [
	^ true
]
