"
Histograms to be used for statistical purposes. Useful, for example, for many image processing algorithms. See http://en.wikipedia.org/wiki/Histogram .
Counts are currently held in a WordArray, and limited to about 4 billion counts (32 bit unsigned integers)

A good number of bins can be n^(1/2) or n^(1/3), where n is the total number of samples. See Wikipedia article for rationale.
"
Class {
	#name : #HistogramMorph,
	#superclass : #Object,
	#instVars : [
		'backgroundColor',
		'textColor',
		'tallies',
		'extraBinsForClampedValues',
		'lowBinCenter',
		'highBinCenter'
	],
	#category : #'Mathematics-Morphic'
}

{ #category : #examples }
HistogramMorph class >> example [
	"
	HistogramMorph example
	"
	| r h |
	r := Random new.
	h := HistogramMorph new: 500 min: 0 max: 1.
	100000 timesRepeat: [h addValue: r next].
	h openInHand
]

{ #category : #examples }
HistogramMorph class >> example2 [
	"
	HistogramMorph example2
	"
	| h S n |
	S := ZZ raisedTo: 4.
	n := 40.
	h := HistogramMorph new: 500 min: 0 max: n.
	100000 timesRepeat: [h addValue: (S atRandom: n) bitSize].
	h openInHand
]

{ #category : #examples }
HistogramMorph class >> example3 [
	"primes conspiracy"
	| h p r |
	h := HistogramMorph new: 22 min: 1 max: 100.
	p := 2. r := p \\ 10.
	100 timesRepeat:
		[| p2 r2 |
		p2 := p nextPrime. r2 := p2 \\ 10.
		h addValue: (r * 10 + r2).
		r := r2. p := p2].
	^ h
]

{ #category : #'instance creation' }
HistogramMorph class >> new: binCount lowBinCenter: lowBinCenter highBinCenter: highBinCenter [
	"lowBinCenter is the center value of the lowest bin.
	highBinCenter is the center value of the highest bin.
	
	Values lower than the lower bound of the first bin go in the fist bin,
	and values higher or equal than the upper bound of the last bin go in the last bin.
		(i.e., out of range values are simply clamped)
		
	For example, the following will give a histogram where first and last bins have half the counts as all the rest:
		| h r |
		h := Histogram binCount: 10 lowBinCenter: 0 highBinCenter: 100.
		r := Random new.
		10000 timesRepeat: [ h addValue: r next * 100  ].
		h plot
		
	Maybe what we wanted was:
		| h r |
		h := Histogram binCount: 10 lowBinCenter: 5 highBinCenter: 95.
		r := Random new.
		10000 timesRepeat: [ h addValue: r next  * 100 ].
		h plot
	
	Or more simply
		| h r |
		h := Histogram binCount: 10 minValue: 0 maxValue: 100.
		r := Random new.
		10000 timesRepeat: [ h addValue: r next  * 100 ].
		h plot
"

	^self new
		tallies: (WordArray new: binCount)
		lowBinCenter: lowBinCenter
		highBinCenter: highBinCenter
		extraBinsForClampedValues: false
]

{ #category : #'instance creation' }
HistogramMorph class >> new: binCount min: min max: max [
	"min is the lower bound of the lowest bin.
	max is the upper bound of the highest bin.
	
	Values lower than min go in the fist bin, and values higher or equal than max go in the last bin.
		(i.e., out of range values are simply clamped)

		| h r |
		h := Histogram binCount: 10 minValue: 0.0 maxValue: 1.0.
		r := Random new.
		10000 timesRepeat: [ h addValue: r next  ].
		h plot

	"

	^self new: binCount min: min max: max extraBinsForClampedValues: false
]

{ #category : #'instance creation' }
HistogramMorph class >> new: regularBinCount min: min max: max extraBinsForClampedValues: aBoolean [
	"min is the lower bound of the lowest bin.
	max is the upper bound of the highest bin.
	
	If aBoolean is false, values lower than min go in the fist bin, and values higher or equal than max go in the last bin.
		(i.e., out of range values are simply clamped)
	If aBoolean, then extra bins are added at each end for these 'out of range' values

		| h r |
		h := Histogram binCount: 10 minValue: 0.0 maxValue: 1.0 extraBinsForClampedValues: true.
		r := Random new.
		10000 timesRepeat: [ h addValue: r next  ].
		h plot
	"

	| tallies highBinCenter lowBinCenter halfBinWidth |
	halfBinWidth := max - min / regularBinCount / 2.0.
	aBoolean
		ifTrue: [
			tallies := WordArray new: regularBinCount + 2.
			lowBinCenter := min - halfBinWidth.
			highBinCenter := max + halfBinWidth ]
		ifFalse: [
			tallies := WordArray new: regularBinCount.
			lowBinCenter := min + halfBinWidth.
			highBinCenter := max - halfBinWidth ].
	^self new
		tallies: tallies
		lowBinCenter: lowBinCenter
		highBinCenter: highBinCenter
		extraBinsForClampedValues: aBoolean
]

{ #category : #'instance creation' }
HistogramMorph class >> new: binCount samples: aCollection [
	| answer |
	answer := self new: binCount min: aCollection min max: aCollection max.
	aCollection do: [:each| answer addValue: each].
	^ answer
]

{ #category : #building }
HistogramMorph >> accumulate [

	2 to: tallies size do: [ :i |
		tallies at: i put: (tallies at: i) + (tallies at: i-1) ]
]

{ #category : #building }
HistogramMorph >> accumulated [

	^self copy accumulate
]

{ #category : #building }
HistogramMorph >> addValue: aNumber [

	| i |
	i := self indexFor: aNumber.
	tallies at: i put: (tallies at: i) + 1
]

{ #category : #accessing }
HistogramMorph >> countAt: value [
	^tallies at: (self indexFor: value)
]

{ #category : #drawing }
HistogramMorph >> drawOn: aCanvas [
	| rect x dx y min max font |
	rect := self morphLocalBounds.
	aCanvas fillRectangle: rect color: backgroundColor.
	min := 0. max := tallies max.
	max = min ifTrue: [^ self].
	dx := rect width asFloat / tallies size.
	x := rect left.
	tallies do: [:v|
		| bar |
		y := (max-v) / (max-min) * rect height asFloat.
		y := y min: rect height.
		y := y max: 0.
		bar := x truncated @ y corner: ((x := x + dx) ceiling @ rect bottom).
		aCanvas fillRectangle: bar color: color].
	
	font := AbstractFont default. " Preferences standardButtonFont."
	aCanvas drawString: max printString at: rect left + 2 @ (rect top + 2) font: font color: textColor.
	aCanvas drawString: min printString at: rect left + 2 @ (rect bottom - font height - 2) font: font color: textColor

]

{ #category : #'as yet unclassified' }
HistogramMorph >> handlesMouseDown: evt [
	^ true
]

{ #category : #'as yet unclassified' }
HistogramMorph >> handlesMouseOver: evt [
	^ true
]

{ #category : #private }
HistogramMorph >> indexFor: aValue [
	| slotIndex |
	slotIndex := ((aValue - lowBinCenter / (highBinCenter -lowBinCenter )) * (tallies size-1)) rounded + 1.
	^slotIndex min: tallies size max: 1.
]

{ #category : #initialization }
HistogramMorph >> initialize [
	super initialize.
	extent := 280@175.
	color := Color darkGray.
	backgroundColor := Color transparent.
	textColor := Color gray alpha: 0.5
]

{ #category : #building }
HistogramMorph >> inverted [
	"For accumulated histograms, compute de inverse cummulative function.
	This is not an exact inverse, and is so far an experiment.
	Some tests to ensure good properties, and maybe more work, are in order. "
	| answer answerTallies n i k |
	n := self regularTalliesCount.
	answerTallies := WordArray new: n.
	answer := HistogramMorph basicNew
		tallies: answerTallies
		lowBinCenter: 0
		highBinCenter: n
		extraBinsForClampedValues: false.
	i := 1.
	k := 1.0 * n / tallies last.
	1 to: n do: [ :j |
		[ (tallies at: i) * k < j ] whileTrue: [ i := i + 1 ].
		answerTallies at: j put: i
		].
	^answer
]

{ #category : #'as yet unclassified' }
HistogramMorph >> mouseMove: aMouseMoveEvent localPosition: localEventPosition [
	| i |
	i := (localEventPosition x * tallies size / self morphLocalBounds width) truncated + 1.
	i := (i min: tallies size) max: 1.
	self showBalloon: i printString, ' -> ', (tallies at: i) printString
]

{ #category : #copying }
HistogramMorph >> postCopy [
	tallies := tallies copy
]

{ #category : #private }
HistogramMorph >> regularTalliesCount [

	^ extraBinsForClampedValues
		ifTrue: [ tallies size - 2 ]
		ifFalse: [ tallies size ]
]

{ #category : #private }
HistogramMorph >> tallies: anArray lowBinCenter: aNumber highBinCenter: anotherNumber extraBinsForClampedValues: aBoolean [
	tallies := anArray.
	lowBinCenter := aNumber.
	highBinCenter := anotherNumber.
	extraBinsForClampedValues := aBoolean.
	tallies size < 300 ifTrue: [extent := (extent x / tallies size) truncated + 1 * tallies size @ extent y]
]
