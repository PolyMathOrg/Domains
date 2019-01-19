Class {
	#name : #OrthogonalMatrixGroup,
	#superclass : #MatrixGroup,
	#category : #'Mathematics-Groups-Matrix'
}

{ #category : #testing }
OrthogonalMatrixGroup >> contains: aMatrix [
	"Answer true if the receiver contains the given element of its ambient."
	^ aMatrix isOrthogonal
]

{ #category : #printing }
OrthogonalMatrixGroup >> shortName [
	^ 'O'
]

{ #category : #operations }
OrthogonalMatrixGroup >> special [
	^ SpecialOrthogonalMatrixGroup new: self degree over: self scalars
]
