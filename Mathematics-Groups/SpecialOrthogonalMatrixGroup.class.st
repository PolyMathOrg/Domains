Class {
	#name : #SpecialOrthogonalMatrixGroup,
	#superclass : #MatrixGroup,
	#category : #'Mathematics-Groups-Matrix'
}

{ #category : #testing }
SpecialOrthogonalMatrixGroup >> contains: aMatrix [
	"Answer true if the receiver contains the given element of its ambient."
	^ aMatrix isOrthogonal and: [aMatrix determinant = self scalars one]
]

{ #category : #printing }
SpecialOrthogonalMatrixGroup >> shortName [
	^ 'SO'
]
