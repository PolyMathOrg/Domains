Class {
	#name : #ImplicitFunctionPlotMorph,
	#superclass : #Object,
	#instVars : [
		'function',
		'image',
		'box'
	],
	#category : #'Mathematics-Morphic'
}

{ #category : #'as yet unclassified' }
ImplicitFunctionPlotMorph class >> example [
	"
	self example
	"
	| function |
	"Descartes folium"
	function := Function from: (QQ raisedTo: 2) to: QQ evaluatingWithArguments: [:x :y| (x raisedTo: 3) + (y raisedTo: 3) - (3*x*y)].
	^ self new function: function
]

{ #category : #'as yet unclassified' }
ImplicitFunctionPlotMorph >> box: aRectangle [
	box := aRectangle.
	image := nil.
	self redrawNeeded
]

{ #category : #'as yet unclassified' }
ImplicitFunctionPlotMorph >> buildImage [
	| lastRow |
	image := Form extent: self morphExtent depth: Display depth.
	lastRow := nil.
	1 to: image height do: [:j|
		| y row lastSign |
		y := j asFloat / image height * box height - box bottom.
		row := Array new: image width.
		lastSign := nil.
		1 to: image width do: [:i|
			| x sign |
			x := i asFloat / image width * box width - box right.
			sign := (function value: (x,y)) sign.
			((lastSign notNil and: [lastSign ~= sign])
				or: [lastRow notNil and: [(lastRow at: i) ~= sign]])
					ifTrue: [image colorAt: i@(image height - j + 1) put: color].
			row at: i put: sign.
			lastSign := sign].
		lastRow := row]
]

{ #category : #'as yet unclassified' }
ImplicitFunctionPlotMorph >> drawOn: aCanvas [
	image isNil ifTrue: [self buildImage].
	aCanvas image: image at: 0@0
]

{ #category : #'as yet unclassified' }
ImplicitFunctionPlotMorph >> function: aFunction [
	function := aFunction.
	image := nil.
	self redrawNeeded
]

{ #category : #'as yet unclassified' }
ImplicitFunctionPlotMorph >> initialize [
	super initialize.
	extent := 150@150.
	color := Color lightGray.
	box := -1@-1 extent: 2@2
]

{ #category : #'as yet unclassified' }
ImplicitFunctionPlotMorph >> morphExtent: aPoint [
	image := nil.
	super morphExtent: aPoint
]
