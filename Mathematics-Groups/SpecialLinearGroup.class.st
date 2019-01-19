Class {
	#name : #SpecialLinearGroup,
	#superclass : #LinearGroup,
	#category : #'Mathematics-Groups-Linear'
}

{ #category : #operations }
SpecialLinearGroup >> asMatrixGroup [
	^ SpecialLinearMatrixGroup on: space coordinates
]

{ #category : #operations }
SpecialLinearGroup >> center [
	^ SpecialScalarGroup on: space
]

{ #category : #testing }
SpecialLinearGroup >> contains: aLinearMap [
	"Answer true if the receiver contains the given element of its ambient."
	^ aLinearMap determinant = space scalars one
]

{ #category : #printing }
SpecialLinearGroup >> shortName [
	^ 'SL'
]
