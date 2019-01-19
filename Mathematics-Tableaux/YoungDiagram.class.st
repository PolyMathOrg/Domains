Class {
	#name : #YoungDiagram,
	#superclass : #Object,
	#instVars : [
		'shape'
	],
	#category : #'Mathematics-Tableaux'
}

{ #category : #'instance creation' }
YoungDiagram class >> shape: aPartition [
	^ self new shape: aPartition
]

{ #category : #'as yet unclassified' }
YoungDiagram >> conjugate [
	"Answer the Young diagram of the conjugate partition."
	^ self class shape: ((1 to: shape size) collect: [:k| shape findLast: [:i| i >= k]])
]

{ #category : #'as yet unclassified' }
YoungDiagram >> hookLengthAt: aPoint [
	| answer |
	answer := (shape at: aPoint x) - aPoint y. "boxes to the right"
	aPoint x + 1 to: shape size do: [:i|
		(shape at: i) >= aPoint y
			ifFalse: [^ answer].
		answer := answer + 1].
	^ answer
]

{ #category : #'as yet unclassified' }
YoungDiagram >> printOn: aStream [
	self shape do: [:k|
		aStream nextPut: $[.
		(1 to: k) do: [:ignore| aStream space] separatedBy: [aStream nextPut: $|].
		aStream nextPut: $]] separatedBy: [aStream lf; space]
]

{ #category : #'as yet unclassified' }
YoungDiagram >> shape [
	^ shape
]

{ #category : #'as yet unclassified' }
YoungDiagram >> shape: aPartition [
	shape := aPartition
]
