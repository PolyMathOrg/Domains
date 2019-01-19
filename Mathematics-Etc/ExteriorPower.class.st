"
TODO:
- elements: k-vectors (ExteriorProduct or ExteriorVector?)
- ExteriorAlgebra as a graded algebra, direct sum of /\^i(V) for i in [1..n]
"
Class {
	#name : #ExteriorPower,
	#superclass : #FreeModule,
	#instVars : [
		'space',
		'degree'
	],
	#category : #'Mathematics-Etc'
}

{ #category : #'as yet unclassified' }
ExteriorPower >> degree [
	^ degree
]

{ #category : #'as yet unclassified' }
ExteriorPower >> degree: anInteger [
	degree := anInteger
]

{ #category : #'as yet unclassified' }
ExteriorPower >> printOn: aStream [
	aStream nextPutAll: '/\'; nextPutAll: (aStream isText ifTrue: [self degree printString super] ifFalse: ['^', self degree printString]); nextPut: $(; print: self space; nextPut: $)
]

{ #category : #'as yet unclassified' }
ExteriorPower >> rank [
	^ self space rank choose: self degree
]

{ #category : #'as yet unclassified' }
ExteriorPower >> space [
	^ space
]

{ #category : #'as yet unclassified' }
ExteriorPower >> space: aFreeModule [
	space := aFreeModule
]
