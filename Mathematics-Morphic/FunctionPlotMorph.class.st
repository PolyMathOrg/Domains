Class {
	#name : #FunctionPlotMorph,
	#superclass : #Object,
	#instVars : [
		'backgroundColor',
		'fillColor',
		'textColor',
		'function',
		'xMin',
		'xMax',
		'yMin',
		'yMax',
		'evaluationPoints',
		'values',
		'firstMousePosition',
		'lastMousePosition'
	],
	#category : #'Mathematics-Morphic'
}

{ #category : #examples }
FunctionPlotMorph class >> example [
	"
	FunctionPlotMorph example
	"
	| sin |
	sin := Function evaluating: [:x| x sin].
	^ FunctionPlotMorph new evaluationPoints: (0.0 to: Float pi * 2 count: 100); function: sin; color: (Color red alpha: 0.5)
]

{ #category : #examples }
FunctionPlotMorph class >> example2 [
	"
	FunctionPlotMorph example2
	"
	^ FunctionPlotMorph new
		color: (Color skyBlue alpha: 0.5);
		function: Sequence phi;
		evaluationPoints: (1 to: 150)
]

{ #category : #examples }
FunctionPlotMorph class >> example3 [
	"
	FunctionPlotMorph example3
	"
	^ FunctionPlotMorph new
		evaluationPoints: (1 to: 150);
		function: Sequence calkinWilf;
		color: (Color yellow alpha: 0.5)
]

{ #category : #examples }
FunctionPlotMorph class >> example4 [
	"
	FunctionPlotMorph example4
	"
	^ FunctionPlotMorph new
		evaluationPoints: (1 to: 5);
		function: Sequence primes;
		yMin: 0 yMax: 12;
		color: (Color orange alpha: 0.5)
]

{ #category : #private }
FunctionPlotMorph >> computeEvaluationPoints [
	evaluationPoints := xMin to: xMax by: 1/100.0
]

{ #category : #private }
FunctionPlotMorph >> computeValues [
	values := self evaluationPoints collect: [:x| [function value: x] on: Error do: [0]].
	yMin isNil
		ifTrue:
			[yMin := values min.
			yMax := values max]
]

{ #category : #drawing }
FunctionPlotMorph >> drawOn: aCanvas [
	| rect p lastP font |
	values isNil ifTrue: [self computeValues].
	rect := self morphLocalBounds.
	aCanvas fillRectangle: rect color: backgroundColor.
	aCanvas line: (self localToMorphic:0@yMin)-(0@1) to: (self localToMorphic: 0 @ yMax)+(0@1) width: 1 color: textColor.
	aCanvas line: (self localToMorphic: xMin@0)+(1@0) to: (self localToMorphic: xMax@0)-(1@0) width: 1 color: textColor.

	lastP := nil.
	self evaluationPoints with: values do: [:x :value|
		| y |
		y := value ifNil: [0].
		(y between: yMin and: yMax)
			ifTrue:
				[p := (self xToMorphic: x)@(self yToMorphic: y).
				p := p rounded.
				lastP notNil
					ifTrue:
						[| y0 |
						aCanvas line: lastP to: p width: 1 color: color.
						y0 := (self yToMorphic: 0) rounded.
						y > 0
							ifTrue: [aCanvas fillRectangle: (lastP corner: (p x @ (y0 min: rect bottom))) color: fillColor]
							ifFalse: [aCanvas fillRectangle: (lastP x @ (y0 max: rect top) corner: p) color: fillColor]].
					lastP := p]
			ifFalse:
				[lastP := nil]].

	font := AbstractFont default. " Preferences standardButtonFont."
	aCanvas drawString: (yMax roundTo: 0.01) printString at: rect left + 2 @ (rect top + 2) font: font color: textColor.
	aCanvas drawString: (yMin roundTo: 0.01)  printString at: rect left + 2 @ (rect bottom - (font height * 2) - 2) font: font color: textColor.
	aCanvas drawString: (xMax roundTo: 0.01) printString at: rect right - (font widthOfString: (xMax  roundTo: 0.01) printString) - 2 @ (rect bottom - font height - 2) font: font color: textColor.
	aCanvas drawString: (xMin roundTo: 0.01) printString at: rect left + 2 + 20 @ (rect bottom - font height - 2) font: font color: textColor
]

{ #category : #accessing }
FunctionPlotMorph >> evaluationPoints [
	evaluationPoints isNil ifTrue: [self computeEvaluationPoints].
	^ evaluationPoints
]

{ #category : #accessing }
FunctionPlotMorph >> evaluationPoints: aCollection [
	xMin := aCollection first.
	xMax := aCollection last.
	evaluationPoints := aCollection.
	values := nil
]

{ #category : #accessing }
FunctionPlotMorph >> function: aFunction [
	function := aFunction.
	yMin := nil. yMax := nil
]

{ #category : #'event handling' }
FunctionPlotMorph >> handlesMouseDown: aMouseButtonEvent [
	"Do I want to receive mouseDown events (mouseDown:, mouseMove:, mouseUp:)?"
	^true
]

{ #category : #initialization }
FunctionPlotMorph >> initialize [
	super initialize.
	extent := 280@175.
	color := Color lightGray.
	backgroundColor := Color transparent.
	fillColor := Color transparent.
	textColor := Color gray alpha: 0.5
]

{ #category : #drawing }
FunctionPlotMorph >> localToMorphic: aPoint [
	^(self xToMorphic: aPoint x) @ (self yToMorphic: aPoint y)
]

{ #category : #drawing }
FunctionPlotMorph >> morphicToLocal: aPoint [
	| bounds |
	bounds := self morphLocalBounds.
	^ aPoint x - bounds left / bounds width * (xMax - xMin) + xMin @ (aPoint y - bounds top / bounds height * (yMax - yMin) + yMin)
]

{ #category : #'event handling' }
FunctionPlotMorph >> mouseButton1Down: aMouseButtonEvent localPosition: localEventPosition [
	super mouseButton1Down: aMouseButtonEvent localPosition: localEventPosition.
	firstMousePosition := lastMousePosition := localEventPosition
]

{ #category : #'event handling' }
FunctionPlotMorph >> mouseButton1Up: aMouseButtonEvent localPosition: localEventPosition [
	super mouseButton1Up: aMouseButtonEvent localPosition: localEventPosition.
	self flag: #fix.
"	mouseMoveEventHandler := nil"
]

{ #category : #'event handling' }
FunctionPlotMorph >> mouseMove: aMouseMoveEvent localPosition: localEventPosition [
	firstMousePosition isNil
		ifTrue: [firstMousePosition := localEventPosition]
		ifFalse:
			[aMouseMoveEvent shiftPressed
				ifTrue:
					[| bounds anchor delta |
					bounds := self morphLocalBounds.
					delta := localEventPosition - lastMousePosition / (bounds width max: bounds height).
					self scaleBy: (2.0 raisedTo: (delta x negated)) @ (2.0 raisedTo: delta y) anchor: firstMousePosition]
				ifFalse:
					[| bounds delta |
					bounds := self morphLocalBounds.
					delta := localEventPosition - lastMousePosition / (bounds width max: bounds height).
					self scrollBy: delta]].
	lastMousePosition := localEventPosition
]

{ #category : #'event handling' }
FunctionPlotMorph >> scaleBy: aPoint anchor: anchorPoint [
	| p |
	p := self morphicToLocal: anchorPoint.
	self evaluationPoints: (self evaluationPoints collect: [:each| each - p x * aPoint x + p x]).
	self redrawNeeded
]

{ #category : #'event handling' }
FunctionPlotMorph >> scrollBy: aPoint [
	| dx dy |
	dx := xMin - xMax * aPoint x.
	self evaluationPoints: (self evaluationPoints collect: [:each| each + dx]).
	dy := yMax - yMin * aPoint y.
	yMin := yMin + dy.
	yMax := yMax + dy.
	self redrawNeeded
]

{ #category : #drawing }
FunctionPlotMorph >> xToMorphic: x [
	^x - xMin / (xMax - xMin ) * extent x
]

{ #category : #accessing }
FunctionPlotMorph >> yMin: min yMax: max [
	yMin := min.
	yMax := max
]

{ #category : #drawing }
FunctionPlotMorph >> yToMorphic: y [
	^yMax - y / (yMax - yMin ) * extent y
]
