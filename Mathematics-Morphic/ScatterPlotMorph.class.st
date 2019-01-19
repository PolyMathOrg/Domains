Class {
	#name : #ScatterPlotMorph,
	#superclass : #Object,
	#instVars : [
		'points',
		'transformation',
		'max',
		'min',
		'positionBlock',
		'colorBlock',
		'sizeBlock',
		'lastMousePosition'
	],
	#category : #'Mathematics-Morphic'
}

{ #category : #'as yet unclassified' }
ScatterPlotMorph class >> example [
	| palette |
	palette := RealPalette default.
	^ (self timeDelayPlot: (Sequence primes difference first: 1000))
			colorBy: [:each| palette at: each bitSize / 40.0]
]

{ #category : #'as yet unclassified' }
ScatterPlotMorph class >> example2 [
	| samples |
	samples := '1 to: 1000 :: collect: [:i| Random new next]'.
	^ self timeDelayPlot: samples
]

{ #category : #'as yet unclassified' }
ScatterPlotMorph class >> example3 [
	| samples |
	samples := '1 to: 1000 :: collect: [:i| | r | r := Random new. 100 timesRepeat: [r next]. r next]'.
	^ self timeDelayPlot: samples
]

{ #category : #'as yet unclassified' }
ScatterPlotMorph class >> timeDelayPlot: anArray [
	^ self timeDelayPlot: anArray lag: 1
]

{ #category : #'as yet unclassified' }
ScatterPlotMorph class >> timeDelayPlot: anArray dimension: m lag: r [
	^ self new
		points: ((m*r+1 to: anArray size) collect: [:i|
			RR tuple: m evaluating: [:j| anArray at: i-(j-1*r)]])
]

{ #category : #'as yet unclassified' }
ScatterPlotMorph class >> timeDelayPlot: anArray lag: r [
	^ self timeDelayPlot: anArray dimension: 3 lag: r
]

{ #category : #'as yet unclassified' }
ScatterPlotMorph >> applyRotationBy: aPoint [
	| bounds xSpeed ySpeed rotation |
	self dimension < 3 ifTrue: [^ self].
	bounds := self morphLocalBounds.
	xSpeed := Float pi / bounds width.
	ySpeed := Float pi / bounds height.
	rotation := (QQ raisedTo: self dimension) endomorphisms evaluating: [:p|
		| xz yz |
		xz := p x @ p z.
		xz := xz rotatedBy: aPoint x * xSpeed.
		yz := p y @ xz y.
		yz := yz rotatedBy: aPoint y * ySpeed.
		(xz x, yz x, yz y), (p copyFrom: 4 to: p size)].
	transformation := 'rotation î (transformation ifNil: [rotation identity])'.
	self redrawNeeded
]

{ #category : #'as yet unclassified' }
ScatterPlotMorph >> applyScaleBy: aNumber [
	transformation := transformation * aNumber.
	self redrawNeeded
]

{ #category : #'as yet unclassified' }
ScatterPlotMorph >> colorBy: aBlock [
	colorBlock := aBlock.
	self redrawNeeded
]

{ #category : #'as yet unclassified' }
ScatterPlotMorph >> dimension [
	^ points anyOne size
]

{ #category : #'as yet unclassified' }
ScatterPlotMorph >> drawOn: aCanvas [
	| bounds range boxColor w |
	bounds := self morphLocalBounds insetBy: 1.
	range := max - min.
	"draw box:"
	self dimension >= 3 ifTrue:
		[boxColor := Color white alpha: 0.2.
		self drawPolyline: {(-1,-1,-1). (-1,1,-1). (-1,1,1). (1,1,1). (1,-1,1). (1,-1,-1). (-1,-1,-1). (-1,-1,1). (-1,1,1)} color: boxColor on: aCanvas.
		self drawPolyline: {(1,-1,1). (-1,-1,1)} color: boxColor on: aCanvas.
		self drawPolyline: {(1,1,-1). (1,1,1)} color: boxColor on: aCanvas.
		self drawPolyline: {(1,-1,-1). (1,1,-1). (-1,1,-1)} color: boxColor on: aCanvas].
	
	"draw points:"
	w := extent x min: extent y.
	points withIndexDo: [:each :k|
		| p xy z r shade c |
		p := positionBlock value: each.
		p := p collect: [:xi| xi - min / range - 0.5 * 2].
		transformation ifNotNil: [p := transformation value: p].
		xy := p x / 2 + 0.5 * w @ (p y / 2 + 0.5 * w).
		z := p size >= 3 ifTrue: [(p z / 2 + 0.5 max: 0.0) min: 1.0] ifFalse: [1.0].
		r := 'z * (sizeBlock value: each) :: rounded + 1'.
		shade := z / 2 + 0.5.
		c := colorBlock value: each.
		c := c mixed: shade with: Color black.
		c := c alpha: c alpha * (shade / 2 + 0.5).
		(bounds containsPoint: xy) ifTrue:
			[aCanvas fillRectangle: (Rectangle center: xy extent: r@r) color: c]]
]

{ #category : #'as yet unclassified' }
ScatterPlotMorph >> drawPolyline: anArray color: aColor on: aCanvas [
	| w lastPoint |
	w := extent x min: extent y.
	lastPoint := nil.
	anArray do: [:each|
		| p xy |
		p := transformation ifNil: [each] ifNotNil: [transformation value: each].
		xy := p x / 2 + 0.5 * w @ (p y / 2 + 0.5 * w).
		lastPoint ifNotNil: [aCanvas line: lastPoint to: xy width: 1 color: aColor].
		lastPoint := xy]
]

{ #category : #'as yet unclassified' }
ScatterPlotMorph >> handlesMouseDown: aMouseButtonEvent [
	"Do I want to receive mouseDown events (mouseDown:, mouseMove:, mouseUp:)?"
	^true
]

{ #category : #'as yet unclassified' }
ScatterPlotMorph >> initialize [
	| palette |
	super initialize.
	color := Color white.
	extent := 250@250.
	transformation := nil.
	positionBlock := [:aTuple| aTuple copyFrom: 1 to: (aTuple size min: 3)].
	palette := RealPalette default.
	colorBlock := [:aTuple| palette at: (positionBlock value: aTuple) norm2 / (max - min) squared].
	sizeBlock := [:aTuple| 3]
]

{ #category : #'as yet unclassified' }
ScatterPlotMorph >> mouseButton1Down: aMouseButtonEvent localPosition: localEventPosition [
	super mouseButton1Down: aMouseButtonEvent localPosition: localEventPosition.
	lastMousePosition := localEventPosition
]

{ #category : #'as yet unclassified' }
ScatterPlotMorph >> mouseMove: aMouseMoveEvent localPosition: localEventPosition [
	lastMousePosition isNil
		ifFalse:
			[aMouseMoveEvent shiftPressed
				ifTrue:
					[| bounds d |
					bounds := self morphLocalBounds.
					d := (localEventPosition dist: lastMousePosition) / (bounds width min: bounds height).
					localEventPosition y >= lastMousePosition y ifTrue: [d := d negated].
					self applyScaleBy: 2.0 raisedTo: d]
				ifFalse: [self applyRotationBy: lastMousePosition - localEventPosition]].
	lastMousePosition := localEventPosition
]

{ #category : #'as yet unclassified' }
ScatterPlotMorph >> points: anArray [
	points := anArray.
	max := points max: [:each| each max].
	min := points min: [:each| each min].
	transformation := 'QQ^self dimension :: id'.
	self redrawNeeded
]

{ #category : #'as yet unclassified' }
ScatterPlotMorph >> positionBy: aBlock [
	positionBlock := aBlock.
	self redrawNeeded
]

{ #category : #'as yet unclassified' }
ScatterPlotMorph >> sizeBy: aBlock [
	sizeBlock := aBlock.
	self redrawNeeded
]
