Class {
	#name : #ComplexPlotMorph,
	#superclass : #Object,
	#instVars : [
		'function',
		'image',
		'box',
		'palette'
	],
	#category : #'Mathematics-Morphic'
}

{ #category : #'as yet unclassified' }
ComplexPlotMorph class >> exampleBlaschkeProduct [
	"This is a phase plot of the Blaschke product defined by 40 randomly choosen numbers in the unit disk."
	| random A f |
	random := Random new.
	A := (1 to: 40) collect: [:each| Complex abs: random next arg: Float twoPi * random next].
	f := Function from: CC to: CC evaluating: [:z| A product: [:a| a abs / a * (a - z) / (1 - (a conjugated * z))]].
	^ ComplexPlotMorph new box: (-1 @ -1 corner: 1 @ 1); palette: ComplexPalette phase; function: f
]

{ #category : #'as yet unclassified' }
ComplexPlotMorph class >> exampleReciprocalSinus [
	| f |
	f := Function from: CC to: CC evaluating: [:z| '1/z :: sin'].
	^ self new box: (-2 @ -1 corner: 2 @ 1); palette: ComplexPalette default; function: f
]

{ #category : #'as yet unclassified' }
ComplexPlotMorph class >> exampleRiemannZetaFunction [
	| f |
	f := Function from: CC to: CC evaluating: [:z| '1 to: 100 :: sum: [:n| n^z negated]'].
	^ self new morphExtent: 300@300; box: (-5@-5 corner: 5@5); palette: (ComplexPalette grid: 1@5); function: f
]

{ #category : #'as yet unclassified' }
ComplexPlotMorph class >> exampleSinus [
	| f |
	f := Function from: CC to: CC evaluating: [:z| z sin].
	^ self new box: (-2*Float pi @ -1.5 corner: 2*Float pi @ 1.5); palette: (ComplexPalette grid: 1@10); function: f
]

{ #category : #'as yet unclassified' }
ComplexPlotMorph >> box: aRectangle [
	box := aRectangle.
	image := nil.
	self redrawNeeded.
	self matchBoxRatio.
]

{ #category : #'as yet unclassified' }
ComplexPlotMorph >> buildImage [
	image := Form extent: self morphExtent depth: Display depth.
	1 to: image height do: [:j|
		| y |
		y := j asFloat / image height * box height - box bottom.
		1 to: image width do: [:i|
			| x z c |
			x := i asFloat / image width * box width - box right.
			z := [function value: x + y i] on: ZeroDivide do: [Infinity projective].
			image colorAt: i@(image height - j + 1) put: (palette at: z)]]
]

{ #category : #'as yet unclassified' }
ComplexPlotMorph >> drawOn: aCanvas [
	image isNil ifTrue: [self buildImage].
	aCanvas image: image at: 0@0
]

{ #category : #'as yet unclassified' }
ComplexPlotMorph >> function: aFunction [
	function := aFunction.
	image := nil.
	self redrawNeeded
]

{ #category : #'as yet unclassified' }
ComplexPlotMorph >> initialize [
	super initialize.
	extent := 300@300.
	color := Color lightGray.
	box := -2@0 extent: 4@2.
	palette := ComplexPalette default
]

{ #category : #'as yet unclassified' }
ComplexPlotMorph >> matchBoxRatio [
	| ratio |
	((ratio := box width / box height asFloat) - (extent x / extent y)) abs < 1
		ifFalse:
			[(ratio >= 1 and: [extent x >= extent y])
				ifTrue: [self morphExtent: extent x @ (extent x / ratio)]
				ifFalse: [self morphExtent: extent y * ratio @ extent y]]
]

{ #category : #'as yet unclassified' }
ComplexPlotMorph >> morphExtent: aPoint [
	image := nil.
	super morphExtent: aPoint
]

{ #category : #'as yet unclassified' }
ComplexPlotMorph >> palette: aComplexPalette [
	palette := aComplexPalette
]
