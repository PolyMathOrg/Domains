Class {
	#name : #RealPalette,
	#superclass : #Object,
	#instVars : [
		'colors',
		'min',
		'max'
	],
	#category : #'Mathematics-Morphic'
}

{ #category : #'as yet unclassified' }
RealPalette class >> default [
	| blue green red |
	red := QQ polynomials interpolate: {"0 -> 0.0." 40 -> 0. 65 -> 0.8. "90 -> 0." 100 -> 0. 150 -> 0.5. 200 -> 0.9. 215 -> 1. 255 -> 0.95}.
	green := QQ polynomials interpolate: {0 -> 0.2. 50 -> 0.48. 100 -> 0.68. 150 -> 0.75. 200 -> 0.70. 255 -> 1}.
	blue := QQ polynomials interpolate: {0 -> 0.5. 35 -> 0.9. 85 -> 0.8. 115 -> 0.7. 150 -> 0.5. 200 -> 0.3. 255 -> 0}.
	^ self new colors: ((0 to: 255) collect: [:x| Color fromArray: ({x < 80 ifTrue: [0] ifFalse: [red value: x]. green value: x. blue value: x} collect: [:y| y abs min: 1.0])]); min: 0.0; max: 1.0
]

{ #category : #'as yet unclassified' }
RealPalette class >> grayscale [
	^ (self new: 100 interpolating: {Color darkGray darker. Color white}) min: 0.0; max: 1.0
]

{ #category : #'as yet unclassified' }
RealPalette class >> new: anInteger interpolating: anArray [
	^ self new colors: ((0 to: anInteger-1) collect: [:i|
			| mu |
			mu := i * anArray size / (anInteger-1).
			(anArray atPin: mu floor + 1) mixed: mu - mu floor with: (anArray atPin: mu ceiling + 1)])
]

{ #category : #'as yet unclassified' }
RealPalette >> at: aNumber [
	| v |
	v := (aNumber max: min) min: max.
	^ colors at: (colors size - 1 * (v - min) / (max - min)) truncated + 1
]

{ #category : #'as yet unclassified' }
RealPalette >> colors: anArray [
	colors := anArray
]

{ #category : #'as yet unclassified' }
RealPalette >> max: aNumber [
	max := aNumber
]

{ #category : #'as yet unclassified' }
RealPalette >> min: aNumber [
	min := aNumber
]
