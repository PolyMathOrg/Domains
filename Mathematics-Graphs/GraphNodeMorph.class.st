Class {
	#name : #GraphNodeMorph,
	#superclass : #Object,
	#instVars : [
		'node',
		'x',
		'dx',
		'shape',
		'label',
		'labelMorph'
	],
	#category : #'Mathematics-Graphs-Morphic'
}

{ #category : #accessing }
GraphNodeMorph >> alpha [
	self dimension > 2 ifFalse: [^ 1.0].
	(owner isNil or: [x z >= 0]) ifTrue: [^ 1.0].
	^ (x z / owner morphExtent y + 1) squared min: 1.0 max: 0.0
]

{ #category : #accessing }
GraphNodeMorph >> color [
	^ color
]

{ #category : #accessing }
GraphNodeMorph >> color: aColor [
	color := aColor
]

{ #category : #moving }
GraphNodeMorph >> dampBy: aNumber [
	dx := dx / aNumber
]

{ #category : #accessing }
GraphNodeMorph >> dimension [
	^ x size
]

{ #category : #accessing }
GraphNodeMorph >> dimension: anInteger [
	| n |
	(n := x size) = anInteger
		ifTrue: [^ self].
	n > anInteger
		ifTrue:
			[x := x copyFrom: 1 to: anInteger.
			dx := dx copyFrom: 1 to: anInteger]
		ifFalse:
			[| z |
			z := QQ tuple: anInteger - n evaluating: [:i| 0].
			x := x, z.
			dx := dx, z]
]

{ #category : #moving }
GraphNodeMorph >> doMove [
	| bounds delta |
	x := x + dx.
	bounds := owner morphLocalBounds.
	self morphPosition: bounds center + ((x at: 1) @ (x at: 2)).
	(bounds containsRect: self morphBounds)
		ifFalse: [delta := 2 * (self morphBounds amountToTranslateWithin: bounds).
					x := x + (delta x, delta y).
					self morphPosition: bounds center + ((x at: 1) @ (x at: 2)).
					dx := dx * 0 "0@0"].
	^ dx norm
]

{ #category : #drawing }
GraphNodeMorph >> drawOn: aCanvas [
	(extent x abs < 2 and: [extent y abs < 2]) ifTrue: [^ self].
	shape == #circle
		ifTrue: [aCanvas fillEllipse: self morphLocalBounds color: self color. ^ self].
	shape == #square
		ifTrue: [aCanvas fillRectangle: self morphLocalBounds color: self color. ^ self].
	shape == #squareFrame
		ifTrue: [aCanvas frameRectangle: self morphLocalBounds borderWidth: 1 color: self color. ^ self].
	shape == #circleFrame
		ifTrue: [aCanvas frameEllipse: self morphLocalBounds borderWidth: 1 color: self color. ^ self].
	"otherwise do nothing"
	^ self
]

{ #category : #accessing }
GraphNodeMorph >> dx [
	^ dx
]

{ #category : #accessing }
GraphNodeMorph >> dx: aVector [
	dx := aVector
]

{ #category : #moving }
GraphNodeMorph >> freeze [
	dx := dx * 0.0
]

{ #category : #private }
GraphNodeMorph >> hideLabel [
	labelMorph notNil ifTrue: [labelMorph delete. labelMorph := nil]
]

{ #category : #initialization }
GraphNodeMorph >> initialize [
	super initialize.
	self color: Color gray.
	x := (0,0).
	dx := x.
	shape := #circle.
	extent := 10@10
]

{ #category : #accessing }
GraphNodeMorph >> label [
	^ label
]

{ #category : #accessing }
GraphNodeMorph >> label: aString [
	label := aString.
	label notNil ifTrue: [self showLabel] ifFalse: [self hideLabel]
]

{ #category : #accessing }
GraphNodeMorph >> node [
	^ node
]

{ #category : #accessing }
GraphNodeMorph >> node: aGraphNode [ 
	node := aGraphNode.
	self label: node value printText
]

{ #category : #moving }
GraphNodeMorph >> perturbate: n [
	dx := dx + (dx collect: [:xi| n atRandom - n])
]

{ #category : #moving }
GraphNodeMorph >> perturbation [
	^ x collect: [:xi| 3 atRandom - 2]
]

{ #category : #accessing }
GraphNodeMorph >> radius [
	^ extent x
]

{ #category : #accessing }
GraphNodeMorph >> radius: aNumber [
	self morphExtent: aNumber @ aNumber
]

{ #category : #accessing }
GraphNodeMorph >> shape [
	^ shape
]

{ #category : #accessing }
GraphNodeMorph >> shape: aShapeSymbol [
	shape := aShapeSymbol.
	self redrawNeeded
]

{ #category : #private }
GraphNodeMorph >> showLabel [
	(labelMorph notNil or: [label isNil]) ifTrue: [^ self].
	labelMorph := StringMorph contents: label font: Preferences standardMenuFont.
	labelMorph color: Color white.
	self addMorph: labelMorph.
	labelMorph morphAlign: labelMorph morphBounds leftCenter with: self morphBounds rightCenter + (1@0)
]

{ #category : #moving }
GraphNodeMorph >> translateBy: delta [
	dx := dx + delta
]

{ #category : #accessing }
GraphNodeMorph >> value [
	^ node value
]

{ #category : #accessing }
GraphNodeMorph >> x [
	^ x
]

{ #category : #accessing }
GraphNodeMorph >> x: aPoint [
	x := aPoint
]
