Class {
	#name : #Pixel,
	#superclass : #Object,
	#instVars : [
		'row',
		'column'
	],
	#category : #'Mathematics-Etc'
}

{ #category : #'as yet unclassified' }
Pixel class >> row: anInteger column: anotherInteger [
	^ self new row: anInteger; column: anotherInteger
]

{ #category : #'as yet unclassified' }
Pixel >> column [
	^ column
]

{ #category : #'as yet unclassified' }
Pixel >> column: anInteger [
	column := anInteger
]

{ #category : #'as yet unclassified' }
Pixel >> isDiagonal [
	^ row = column
]

{ #category : #'as yet unclassified' }
Pixel >> printOn: aStream [
	aStream nextPut: $[; print: row; nextPut: $,; print: column; nextPut: $]
]

{ #category : #'as yet unclassified' }
Pixel >> row [
	^ row
]

{ #category : #'as yet unclassified' }
Pixel >> row: anInteger [
	row := anInteger
]

{ #category : #'as yet unclassified' }
Pixel >> transpose [
	^ self class row: column column: row
]
