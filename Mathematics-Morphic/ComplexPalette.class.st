Class {
	#name : #ComplexPalette,
	#superclass : #Object,
	#instVars : [
		'luminanceBlock',
		'hueBlock',
		'zeroColor',
		'infinityColor'
	],
	#category : #'Mathematics-Morphic'
}

{ #category : #'as yet unclassified' }
ComplexPalette class >> default [
	^ self phase
]

{ #category : #'as yet unclassified' }
ComplexPalette class >> grid: scalePoint [
	"This is a palette that colors each complex value z assigning a hue depending on its phase arg(z), and luminance depending on both phase and modulus |z|. The result is that of showing a grid of shadows over the Riemann sphere similar to a conformal grid mapping. The argument scalePoint determines the number of meridians and separation between parallels."
	^ self basicNew setGrid: scalePoint
]

{ #category : #'as yet unclassified' }
ComplexPalette class >> log [
	^ self basicNew setLog
]

{ #category : #'as yet unclassified' }
ComplexPalette class >> logReversed [
	^ self basicNew setLogReversed
]

{ #category : #'as yet unclassified' }
ComplexPalette class >> magnitude [
	^ self basicNew setMagnitude
]

{ #category : #'as yet unclassified' }
ComplexPalette class >> new [
	^ self default
]

{ #category : #'as yet unclassified' }
ComplexPalette class >> phase [
	"This is a palette that colors each complex value z assigning a hue depending only on its phase arg(z), and constant luminance. The modulus |z| is not depicted."
	^ self basicNew setPhase
]

{ #category : #'as yet unclassified' }
ComplexPalette class >> reversed [
	^ self basicNew setReversed
]

{ #category : #'as yet unclassified' }
ComplexPalette class >> scaled: aNumber [
	^ self basicNew setScaled: aNumber
]

{ #category : #accessing }
ComplexPalette >> at: aNumber [
	aNumber isInfinite ifTrue: [^ infinityColor].
	aNumber isZero ifTrue: [^ zeroColor].
	^ self
		colorHue: ([hueBlock value: aNumber] on: Error do: [^ infinityColor])
		saturation: 1.0
		luminance: ([luminanceBlock value: aNumber] on: Error do: [^ infinityColor])
]

{ #category : #private }
ComplexPalette >> colorHue: hue saturation: saturation luminance: luma [
	| chroma x hf i r1 g1 b1 m | 

	chroma := (1 - (2*luma - 1) abs) * saturation.
	hf := hue \\ 360.
	i := hf // 60.				"integer part of hue"
	x := (hf \\ 60) / 60.0.	"fractional part of hue"
	x := x \\ 2.
	i \\ 2 = 1 ifTrue: [ x := 1.0 - x ].
	x := chroma * x.

	0 = i ifTrue: [ r1 := chroma. g1 := x. b1 := 0.0 ].
	1 = i ifTrue: [ r1 := x. g1 := chroma. b1 := 0.0 ].
	2 = i ifTrue: [ r1 := 0.0. g1 := chroma. b1 := x ].
	3 = i ifTrue: [ r1 := 0.0. g1 := x. b1 := chroma ].
	4 = i ifTrue: [ r1 := x. g1 := 0.0. b1 := chroma ].
	5 = i ifTrue: [ r1 := chroma. g1 := 0.0. b1 := x ].

	m := luma - (chroma / 2) "(0.299*r1) - (0.587*g1) - (0.114*b1)".
	r1 := r1 + m min: 1.0 max: 0.0.
	g1 := g1 + m min: 1.0 max: 0.0.
	b1 := b1 + m min: 1.0 max: 0.0.
	^ Color r: r1 g: g1 b: b1
]

{ #category : #initialization }
ComplexPalette >> setGrid: scalePoint [
	hueBlock := [:z| z arg radiansToDegrees \\ 360].
	luminanceBlock := [:z| (z isZero ifTrue: [1.0] ifFalse: [(z arg / Float twoPi + 0.5 * scalePoint y + 0.999 \\ 1.0) * (z abs ln * scalePoint x \\ 1.0)]) * 0.4 + 0.2].
	zeroColor := Color white.
	infinityColor := Color black
]

{ #category : #initialization }
ComplexPalette >> setLog [
	hueBlock := [:z| z arg radiansToDegrees \\ 360].
	luminanceBlock := [:z| z isZero ifTrue: [1.0] ifFalse: [z abs min: 0.6 max: 0.0]].
	zeroColor := Color white.
	infinityColor := Color black
]

{ #category : #initialization }
ComplexPalette >> setLogReversed [
"	hueBlock := [:z| (z arg + Float pi) radiansToDegrees \\ 360]."
	hueBlock := [:z| z arg radiansToDegrees \\ 360].
	luminanceBlock := [:z| z isZero ifTrue: [0.0] ifFalse: [1.0 - (z abs min: 0.6 max: 0.0)]].
	zeroColor := Color black.
	infinityColor := Color white
]

{ #category : #initialization }
ComplexPalette >> setMagnitude [
	hueBlock := [:z| z arg radiansToDegrees \\ 360].
	luminanceBlock := [:z| '2.0 ^ z abs negated'].
	zeroColor := Color white.
	infinityColor := Color black
]

{ #category : #initialization }
ComplexPalette >> setPhase [
	hueBlock := [:z| z arg radiansToDegrees \\ 360].
	luminanceBlock := [:z| 0.5].
	zeroColor := Color white.
	infinityColor := Color black
]

{ #category : #initialization }
ComplexPalette >> setReversed [
	hueBlock := [:z| z arg radiansToDegrees \\ 360].
"	hueBlock := [:z| (z arg + Float pi) radiansToDegrees \\ 360]."
	luminanceBlock := [:z| 1.0 - ('2.0 ^ z abs negated')].
	zeroColor := Color black.
	infinityColor := Color white
]

{ #category : #initialization }
ComplexPalette >> setScaled: scale [
	hueBlock := [:z| z arg radiansToDegrees \\ 360].
	luminanceBlock := [:z| '2.0 ^ (z abs * scale negated)'].
	zeroColor := Color white.
	infinityColor := Color black
]
