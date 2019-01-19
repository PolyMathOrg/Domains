Class {
	#name : #ScalarGroup,
	#superclass : #LinearGroup,
	#category : #'Mathematics-Groups-Linear'
}

{ #category : #operations }
ScalarGroup >> asMatrixGroup [
	^ ScalarMatrixGroup on: space coordinates
]

{ #category : #random }
ScalarGroup >> atRandom: aRandom [
	^ space endomorphisms scalar: (space scalars atRandom: aRandom)
]

{ #category : #random }
ScalarGroup >> atRandom: aRandom bits: bitSize [
	^ space endomorphisms scalar: (space scalars atRandom: aRandom bits: bitSize / space dimension)
]

{ #category : #testing }
ScalarGroup >> contains: aLinearMap [
	"Answer true if the receiver contains the given element of its ambient."
	^ aLinearMap isScalar
]

{ #category : #accessing }
ScalarGroup >> dimension [
	^ 1
]

{ #category : #enumerating }
ScalarGroup >> do: aBlock [
	| endos |
	endos := space endomorphisms.
	self scalars do: [:each| aBlock value: (endos scalar: each)]
]

{ #category : #testing }
ScalarGroup >> isCommutative [
	^ space scalars isCommutative
]

{ #category : #printing }
ScalarGroup >> shortName [
	^ 'Z'
]

{ #category : #operations }
ScalarGroup >> special [
	^ SpecialScalarGroup on: space
]
