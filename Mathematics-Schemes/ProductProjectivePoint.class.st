Class {
	#name : #ProductProjectivePoint,
	#superclass : #RationalPoint,
	#instVars : [
		'components'
	],
	#category : #'Mathematics-Schemes-Projective-Product'
}

{ #category : #'as yet unclassified' }
ProductProjectivePoint >> = aProductProjectivePoint [
	self class = aProductProjectivePoint class ifFalse: [^ super = aProductProjectivePoint].
	^ self components = aProductProjectivePoint components
]

{ #category : #'as yet unclassified' }
ProductProjectivePoint >> components [
	^ components
]

{ #category : #'as yet unclassified' }
ProductProjectivePoint >> components: anArray [
	components := anArray
]

{ #category : #'as yet unclassified' }
ProductProjectivePoint >> coordinates [
	| answer |
	self components do: [:each|
		answer := answer isNil ifTrue: [each coordinates] ifFalse: [answer, each coordinates]].
	^ answer
]

{ #category : #'as yet unclassified' }
ProductProjectivePoint >> hash [
	^ self components hash
]

{ #category : #'as yet unclassified' }
ProductProjectivePoint >> printOn: aStream [
	aStream nextPut: $[.
	self components do: [:each| each printInsidesOn: aStream] separatedBy: [aStream nextPutAll: ', '].
	aStream nextPut: $]
]
