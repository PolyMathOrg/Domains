Class {
	#name : #GraphEdgeMorph,
	#superclass : #Morph,
	#instVars : [
		'source',
		'target',
		'width',
		'drawArrowHead',
		'label',
		'labelMorph',
		'multiplicity'
	],
	#category : #'Mathematics-Graphs-Morphic'
}

{ #category : #private }
GraphEdgeMorph >> adjustBounds [
	| newBounds |
	newBounds := (self externalize: self sourcePoint) rect: (self externalize: self targetPoint).
	self morphBounds: newBounds.
	labelMorph ifNotNil: [labelMorph morphAlign: labelMorph morphBounds center with: newBounds extent // 2]
]

{ #category : #accessing }
GraphEdgeMorph >> alpha [
	^ source alpha + target alpha / 2.0
]

{ #category : #accessing }
GraphEdgeMorph >> color [
	^ color alpha: self alpha
]

{ #category : #accessing }
GraphEdgeMorph >> color: aColor [
	color := aColor
]

{ #category : #drawing }
GraphEdgeMorph >> direction [
	^ (self targetPoint - self sourcePoint) normalized
]

{ #category : #drawing }
GraphEdgeMorph >> drawArcOn: aCanvas from: sourcePoint to: targetPoint [
	multiplicity odd
		ifTrue: [aCanvas line: sourcePoint to: targetPoint width: width color: self color].
	1 to: multiplicity - (multiplicity \\ 2) do: [:i|
		self drawCurveOn: aCanvas from: sourcePoint to: targetPoint curvature: i+1//2 * (i odd ifTrue: [1] ifFalse: [-1])]
]

{ #category : #drawing }
GraphEdgeMorph >> drawArrowOn: aCanvas from: aPoint to: anotherPoint [
	| sourcePoint targetPoint direction |
	sourcePoint := aPoint.
	targetPoint := anotherPoint.
	direction := (targetPoint - sourcePoint) normalized.
	target identityHash < source identityHash
		ifTrue:
			[ | shift |
			shift := (direction rotatedBy: Float pi/2) * 4.
			sourcePoint := sourcePoint + shift.
			targetPoint := targetPoint + shift].
	targetPoint := targetPoint - (direction * target radius).
	sourcePoint := sourcePoint + (direction * source radius).
	self drawArcOn: aCanvas from: sourcePoint to: targetPoint.
	aCanvas line: targetPoint - (direction*3) - ((direction rotatedBy: Float pi / 4) * 4)
		to: targetPoint width: width color: self color.
	aCanvas line: targetPoint - (direction*2) - ((direction rotatedBy: Float pi / 4) * 4)
		to: targetPoint width: width color: self color.
	aCanvas line: targetPoint - (direction*3) - ((direction rotatedBy: Float pi * 7 / 4) * 4)
		to: targetPoint width: width color: self color.
	aCanvas line: targetPoint - (direction*2) - ((direction rotatedBy: Float pi * 7 / 4) * 4)
		to: targetPoint width: width color: self color.

"	self sourcePoint = self targetPoint
		ifFalse: [aCanvas
				drawThinArrowFrom: self sourcePoint
				to: self targetPoint
				width: 1
				color: self color]"
			
	"| circle string |  
	circle := EllipseMorph new extent: 20 @ 20;  
	 
	color: (Color  
	r: 1.0  
	g: 0.452  
	b: 0.065).  
	circle align: circle center with: self center.  
	self addMorph: circle.  
	string := StringMorph new contents: 'test'.  
	string align: string bounds leftCenter with: bounds rightCenter + (4 @  
	0). self addMorph: string"
"	| aa |
	aa := PolygonMorph new.
	aa computeArrowFormAt: self sourcePoint from: self destinationPoint.
	self addMorph: aa"

]

{ #category : #drawing }
GraphEdgeMorph >> drawCurveOn: aCanvas from: sourcePoint to: targetPoint curvature: curvature [
	| perp previous |
	perp := targetPoint - sourcePoint / 10.0 rotatedBy: Float pi / 2.
	0.0 to: 1.0 count: 15 do: [:i|
		| current |
		current := sourcePoint * i + (targetPoint * (1.0-i)).
		current := current + ((0.5 - (0.5-i) abs) sqrt * curvature * perp).
		previous ifNotNil: [aCanvas line: previous to: current width: width color: self color].
		previous := current]
]

{ #category : #drawing }
GraphEdgeMorph >> drawLoopOn: aCanvas at: aPoint [
	aCanvas frameEllipse: (aPoint - (10@20) extent: 20@20) borderWidth: width color: self color
]

{ #category : #drawing }
GraphEdgeMorph >> drawOn: aCanvas [ 
	"frameRectangle: self bounds color: Color black;"
	| sourcePoint targetPoint |
	"aCanvas frameRectangle: self morphLocalBounds borderWidth: 1 color: Color red."
	[sourcePoint := self sourcePoint.
	targetPoint := self targetPoint] on: Error do: [^ self].
	targetPoint = sourcePoint ifTrue: [^ self drawLoopOn: aCanvas at: targetPoint].
	drawArrowHead ifTrue: [^ self drawArrowOn: aCanvas from: sourcePoint to: targetPoint].
	self drawArcOn: aCanvas from: sourcePoint to: targetPoint
]

{ #category : #accessing }
GraphEdgeMorph >> hideArrowHead [
	drawArrowHead := false
]

{ #category : #private }
GraphEdgeMorph >> hideLabel [
	labelMorph notNil ifTrue: [labelMorph delete. labelMorph := nil]
]

{ #category : #accessing }
GraphEdgeMorph >> incrementMultiplicity [
	multiplicity := multiplicity + 1
]

{ #category : #initialization }
GraphEdgeMorph >> initialize [
	super initialize.
	self color: Color gray.
	width := 1.
	drawArrowHead := true.
	multiplicity := 1
]

{ #category : #accessing }
GraphEdgeMorph >> label [
	^ label
]

{ #category : #accessing }
GraphEdgeMorph >> label: aString [
	label := aString.
	label notNil ifTrue: [self showLabel] ifFalse: [self hideLabel]
]

{ #category : #'geometry testing' }
GraphEdgeMorph >> morphContainsPoint: aLocalPoint [
	^ super morphContainsPoint: aLocalPoint
]

{ #category : #accessing }
GraphEdgeMorph >> showArrowHead [
	drawArrowHead := true
]

{ #category : #private }
GraphEdgeMorph >> showLabel [
	(labelMorph notNil or: [label isNil]) ifTrue: [^ self].
	labelMorph := StringMorph contents: label asString font: Preferences standardMenuFont.
	labelMorph color: Color white.
	self addMorph: labelMorph.
	labelMorph morphAlign: labelMorph morphBounds leftCenter with: self morphBounds rightCenter + (1@0)
]

{ #category : #accessing }
GraphEdgeMorph >> source [
	^ source
]

{ #category : #accessing }
GraphEdgeMorph >> source: aMorph [
	source := aMorph
]

{ #category : #accessing }
GraphEdgeMorph >> sourcePoint [
	^ self internalizeFromWorld: source morphBoundsInWorld center
]

{ #category : #stepping }
GraphEdgeMorph >> step [
	(source owner isNil or: [target owner isNil]) ifTrue: [^ self delete].
	self adjustBounds
]

{ #category : #stepping }
GraphEdgeMorph >> stepTime [
	^ 0
]

{ #category : #accessing }
GraphEdgeMorph >> target [
	^ target
]

{ #category : #accessing }
GraphEdgeMorph >> target: aMorph [
	target := aMorph
]

{ #category : #accessing }
GraphEdgeMorph >> targetPoint [
	^ self internalizeFromWorld: target morphBoundsInWorld center
]

{ #category : #stepping }
GraphEdgeMorph >> wantsSteps [
	^ true
]

{ #category : #accessing }
GraphEdgeMorph >> width [
	^ width
]

{ #category : #accessing }
GraphEdgeMorph >> width: anInteger [
	"Set the width of the line to draw."
	width := anInteger
]
