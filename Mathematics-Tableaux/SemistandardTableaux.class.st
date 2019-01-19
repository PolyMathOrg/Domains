Class {
	#name : #SemistandardTableaux,
	#superclass : #Domain,
	#instVars : [
		'shape',
		'alphabet'
	],
	#category : #'Mathematics-Tableaux'
}

{ #category : #'as yet unclassified' }
SemistandardTableaux class >> alphabet: anArray shape: aPartition [
	^ self new alphabet: anArray; shape: aPartition
]

{ #category : #'as yet unclassified' }
SemistandardTableaux class >> new: anInteger shape: aPartition [
	^ self alphabet: (1 to: anInteger) shape: aPartition
]

{ #category : #'as yet unclassified' }
SemistandardTableaux >> alphabet [
	^ alphabet
]

{ #category : #'as yet unclassified' }
SemistandardTableaux >> alphabet: anArray [
	alphabet := anArray
]

{ #category : #'as yet unclassified' }
SemistandardTableaux >> diagram [
	^ YoungDiagram shape: shape
]

{ #category : #'as yet unclassified' }
SemistandardTableaux >> shape [
	^ shape
]

{ #category : #'as yet unclassified' }
SemistandardTableaux >> shape: aPartition [
	shape := aPartition
]
