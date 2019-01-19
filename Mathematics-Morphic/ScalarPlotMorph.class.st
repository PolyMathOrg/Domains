Class {
	#name : #ScalarPlotMorph,
	#superclass : #Object,
	#instVars : [
		'function',
		'palette',
		'xMin',
		'xMax',
		'yMin',
		'yMax',
		'form'
	],
	#category : #'Mathematics-Morphic'
}

{ #category : #'as yet unclassified' }
ScalarPlotMorph >> drawOn: aCanvas [
	| r |
	r := 1.
	0 to: extent x - r by: r do: [:x|
		0 to: extent y - r by: r do: [:y|
			aCanvas fillRectangle: (x@y extent: r@r) color: (palette at: (function value: (self morphToDomain: x@y)))]]

]

{ #category : #'as yet unclassified' }
ScalarPlotMorph >> function: aFunction [
	function := aFunction
]

{ #category : #'as yet unclassified' }
ScalarPlotMorph >> initialize [
	super initialize.
	extent := 100@100.
	function := [:v| v x cos * v y sin].
	xMin := -4. xMax := 4.
	yMin := -4. yMax := 4.
	palette := RealPalette default min: -1.0; max: 1.0
]

{ #category : #'as yet unclassified' }
ScalarPlotMorph >> morphToDomain: aPoint [
	^ (aPoint x * (xMax - xMin) / extent x + xMin, (aPoint y * (yMax - yMin) / extent y + yMin))
]
