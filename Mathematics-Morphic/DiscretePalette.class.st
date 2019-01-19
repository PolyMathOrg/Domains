Class {
	#name : #DiscretePalette,
	#superclass : #Object,
	#instVars : [
		'colors',
		'map'
	],
	#category : #'Mathematics-Morphic'
}

{ #category : #'as yet unclassified' }
DiscretePalette class >> colors: anArray [
	^ self new colors: anArray
]

{ #category : #'as yet unclassified' }
DiscretePalette class >> default [
	^ self colors: (#("brightGreen" periwinkle seaGreen hotPink lightYellow cyan lightPink lightOrange  "lightGreen" "lightRed"  "mustard" ) collect: [:each| Color exactColorNamed: each]) "shuffled"
]

{ #category : #'as yet unclassified' }
DiscretePalette >> at: anObject [
	^ map at: anObject ifAbsentPut: [self newColor]
]

{ #category : #'as yet unclassified' }
DiscretePalette >> colors: anArray [
	colors := anArray.
	map := Dictionary new
]

{ #category : #'as yet unclassified' }
DiscretePalette >> newColor [
	| a b answer |
	map size < colors size ifTrue: [^ colors at: map size + 1].
	[a := colors atRandom.
	[b := colors atRandom. a = b] whileTrue.
	answer := a mixed: 0.5 with: b.
	colors includes: answer] whileTrue.
	^ answer
]
