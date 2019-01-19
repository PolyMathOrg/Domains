Class {
	#name : #UnitDiskPlotMorph,
	#superclass : #Object,
	#instVars : [
		'function',
		'image',
		'palette',
		'inverseMap'
	],
	#category : #'Mathematics-Morphic'
}

{ #category : #examples }
UnitDiskPlotMorph class >> exampleBlaschkeProduct [
	"This is a phase plot of the Blaschke product defined by 40 randomly choosen numbers in the unit disk, plotted through a conformal mapping of the complex plane into the unit disk."
	| random A f |
	random := Random new.
	A := (1 to: 40) collect: [:each| Complex abs: random next arg: Float twoPi * random next].
	f := Function from: CC to: CC evaluating: [:z| A product: [:a| a abs / a * (a - z) / (1 - (a conjugated * z))]].
	^ UnitDiskPlotMorph new mapPlaneToUnitDisk; palette: ComplexPalette phase; function: f
]

{ #category : #'as yet unclassified' }
UnitDiskPlotMorph >> buildImage [
	image := Form extent: self morphExtent depth: Display depth.
	1 to: image height do: [:j|
		| y |
		y := j asFloat / image height * 2 - 1.
		1 to: image width do: [:i|
			| x z c |
			x := i asFloat / image width * 2 - 1.
			(x squared + y squared) sqrt < 1
				ifTrue:
					[| w |
					z := x + y i.
					w := [function value: (inverseMap value: z)] on: ZeroDivide do: [Infinity projective].
					image colorAt: i@j put: (palette at: w)]]]
]

{ #category : #'as yet unclassified' }
UnitDiskPlotMorph >> drawOn: aCanvas [
	image isNil ifTrue: [self buildImage].
	aCanvas image: image at: 0@0
]

{ #category : #'as yet unclassified' }
UnitDiskPlotMorph >> function: aFunction [
	function := aFunction.
"	function domain = HH
		ifTrue: [self mapUpperHalfPlaneToUnitDisk]
		ifFalse: [function domain = CC ifTrue: [self mapPlaneToUnitDisk]]."
	image := nil.
	self redrawNeeded
]

{ #category : #'as yet unclassified' }
UnitDiskPlotMorph >> initialize [
	super initialize.
	extent := 300@300.
	color := Color lightGray.
	palette := ComplexPalette default.
	inverseMap := [:z| z] "by default use the identity map"
]

{ #category : #'as yet unclassified' }
UnitDiskPlotMorph >> mapPlaneToUnitDisk [
	inverseMap := [:z| z / (1 - z abs squared)]
]

{ #category : #'as yet unclassified' }
UnitDiskPlotMorph >> mapUpperHalfPlaneToUnitDisk [
	inverseMap := [:z| 1 + z / (1 - z) * 1 i]
]

{ #category : #'as yet unclassified' }
UnitDiskPlotMorph >> morphExtent: aPoint [
	| side |
	image := nil.
	side := aPoint x min: aPoint y.
	super morphExtent: side @ side
]

{ #category : #'as yet unclassified' }
UnitDiskPlotMorph >> palette: aComplexPalette [
	palette := aComplexPalette
]
