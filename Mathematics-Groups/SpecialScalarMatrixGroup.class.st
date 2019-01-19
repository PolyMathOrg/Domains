Class {
	#name : #SpecialScalarMatrixGroup,
	#superclass : #MatrixGroup,
	#category : #'Mathematics-Groups-Matrix'
}

{ #category : #testing }
SpecialScalarMatrixGroup >> contains: aMatrix [
	"Answer true if the receiver contains the given element of its ambient."
	^ aMatrix isScalar and: [aMatrix determinant = self scalars one]
]

{ #category : #testing }
SpecialScalarMatrixGroup >> isCommutative [
	^ self scalars isCommutative
]

{ #category : #printing }
SpecialScalarMatrixGroup >> shortName [
	^ 'SZ'
]
