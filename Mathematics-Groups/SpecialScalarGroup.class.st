Class {
	#name : #SpecialScalarGroup,
	#superclass : #LinearGroup,
	#category : #'Mathematics-Groups-Linear'
}

{ #category : #operations }
SpecialScalarGroup >> asMatrixGroup [
	^ SpecialScalarMatrixGroup on: space coordinates
]

{ #category : #testing }
SpecialScalarGroup >> contains: aLinearMap [
	"Answer true if the receiver contains the given element of its ambient."
	^ aLinearMap isScalar and: [aLinearMap determinant = space scalars one]
]

{ #category : #testing }
SpecialScalarGroup >> isCommutative [
	^ space scalars isCommutative
]

{ #category : #printing }
SpecialScalarGroup >> shortName [
	^ 'SZ'
]
