Class {
	#name : #SpecialOrthogonalGroup,
	#superclass : #LinearGroup,
	#category : #'Mathematics-Groups-Linear'
}

{ #category : #operations }
SpecialOrthogonalGroup >> affine [
	^ SpecialEuclideanGroup on: space affine
]

{ #category : #operations }
SpecialOrthogonalGroup >> asMatrixGroup [
	^ SpecialOrthogonalMatrixGroup on: space coordinates
]

{ #category : #testing }
SpecialOrthogonalGroup >> contains: aLinearMap [
	"Answer true if the receiver contains the given element of its ambient."
	^ aLinearMap isOrthogonal and: [aLinearMap determinant = self scalars one]
]

{ #category : #printing }
SpecialOrthogonalGroup >> shortName [
	^ 'SO'
]
