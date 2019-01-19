Class {
	#name : #AutomaticPalette,
	#superclass : #Object,
	#instVars : [
		'map'
	],
	#category : #'Mathematics-Morphic'
}

{ #category : #'as yet unclassified' }
AutomaticPalette >> at: anObject [
	| i n |
	i := map at: anObject ifAbsentPut: [map size].
	n := map size.
	^ Color h: i * 360.0 / (n + 1) + 90.0 \\ 360.0 s: 0.65 v: 0.95
]

{ #category : #'as yet unclassified' }
AutomaticPalette >> initialize [
	map := Dictionary new
]
