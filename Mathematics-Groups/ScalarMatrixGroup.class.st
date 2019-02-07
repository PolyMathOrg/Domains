Class {
	#name : #ScalarMatrixGroup,
	#superclass : #MatrixGroup,
	#category : #'Mathematics-Groups-Matrix'
}

{ #category : #random }
ScalarMatrixGroup >> atRandom: aRandom [
	^ self scalars
		matrix: self degree
		scalar: (self scalars atRandom: aRandom) 
]

{ #category : #random }
ScalarMatrixGroup >> atRandom: aRandom bits: bitSize [
	^ self scalars
		matrix: self degree @ self degree
		scalar: (self scalars atRandom: aRandom bits: bitSize / self degree) 
]

{ #category : #testing }
ScalarMatrixGroup >> contains: aMatrix [
	"Answer true if the receiver contains the given element of its ambient."

	^ aMatrix isScalar 
]

{ #category : #accessing }
ScalarMatrixGroup >> dimension [
	^ 1 
]

{ #category : #enumerating }
ScalarMatrixGroup >> do: aBlock [
	self scalars
		do: [ :each | aBlock value: (self scalars matrix: self degree scalar: each) ] 
]

{ #category : #testing }
ScalarMatrixGroup >> isCommutative [
	^ self scalars isCommutative 
]

{ #category : #printing }
ScalarMatrixGroup >> shortName [
	^ 'Z' 
]
