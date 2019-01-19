"
The special affine group of an affine space, consisting of all invertible affine transformations from the space into itself that preserve volumes.
"
Class {
	#name : #SpecialAffineGroup,
	#superclass : #AffineGroup,
	#category : #'Mathematics-Groups-Affine'
}

{ #category : #testing }
SpecialAffineGroup >> includes: anAffineMap [
	^ anAffineMap domain = space and: [anAffineMap isEndomorphism and: [anAffineMap matrix determinant = space scalars one]]
]

{ #category : #operations }
SpecialAffineGroup >> linear [
	^ SpecialLinearGroup on: space direction
]

{ #category : #printing }
SpecialAffineGroup >> shortName [
	^ 'SA'
]
