Class {
	#name : #MultiplicationTableMorph,
	#superclass : #Object,
	#instVars : [
		'elements',
		'colors',
		'operation'
	],
	#category : #'Mathematics-Morphic'
}

{ #category : #'as yet unclassified' }
MultiplicationTableMorph class >> elements: anArray operation: aBinaryOperation [
	^ self new elements: anArray; operation: aBinaryOperation
]

{ #category : #'as yet unclassified' }
MultiplicationTableMorph >> drawOn: aCanvas [
	| h w |
	w := extent x / elements size.
	h := extent y / elements size.
	w > 10
		ifTrue:
			[1 to: elements size do: [:i|
				1 to: elements size do: [:j|
					aCanvas fillRectangle: ((i-1*w @ (j-1*h)) truncated corner: (i*w-1 @ (j*h-1)) truncated) color: (colors at: (operation value: {elements at: i. elements at: j}))]]]
		ifFalse:
			[1 to: elements size do: [:i|
				1 to: elements size do: [:j|
					aCanvas fillRectangle: ((i-1*w @ (j-1*h)) truncated corner: (i*w @ (j*h)) truncated) color: (colors at: (operation value: {elements at: i. elements at: j}))]]]
		
]

{ #category : #'as yet unclassified' }
MultiplicationTableMorph >> elements: anArray [
	elements := anArray asArray
]

{ #category : #'as yet unclassified' }
MultiplicationTableMorph >> initialize [
	super initialize.
	self morphExtent: 150@150.
	colors := AutomaticPalette new
]

{ #category : #'as yet unclassified' }
MultiplicationTableMorph >> morphExtent: aPoint [
	| max |
	max := aPoint x max: aPoint y.
	super morphExtent: max @ max
]

{ #category : #'as yet unclassified' }
MultiplicationTableMorph >> operation: aBinaryOperation [
	operation := aBinaryOperation
]
