Class {
	#name : #SLP,
	#superclass : #Object,
	#instVars : [
		'word'
	],
	#category : #'Mathematics-Etc'
}

{ #category : #'as yet unclassified' }
SLP class >> value: anObject [
	^ self word: (Word x: anObject)
]

{ #category : #'as yet unclassified' }
SLP class >> word: aWord [
	^ self new word: aWord
]

{ #category : #'as yet unclassified' }
SLP >> * aSLP [
	^ self class word: (Word syllables: {word -> 1. aSLP word -> 1})
]

{ #category : #'as yet unclassified' }
SLP >> printOn: aStream [
	word printOn: aStream
]

{ #category : #'as yet unclassified' }
SLP >> raisedTo: anInteger [
	"^ "

	anInteger = 0
		ifTrue: [ ^ self class word: Word empty ].
	anInteger = 1
		ifTrue: [ ^ self ].
	^ self class word: (Word x: word to: anInteger)
]

{ #category : #'as yet unclassified' }
SLP >> reciprocal [
	^ self class word: (Word x: word to: -1)
]

{ #category : #'as yet unclassified' }
SLP >> value [
	| answer |
	answer := word value.
	[answer isKindOf: Word] whileTrue: [answer := answer value].
	^ answer
]

{ #category : #'as yet unclassified' }
SLP >> word [
	^ word
]

{ #category : #'as yet unclassified' }
SLP >> word: aWord [
	word := aWord
]
