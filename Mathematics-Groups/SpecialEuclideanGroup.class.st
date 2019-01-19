"
The special Euclidean group SE(n) or E*(n), a subgroup of the Euclidean group E(n) that consists of rigid motions, i.e. isometries preserving orientation.

"
Class {
	#name : #SpecialEuclideanGroup,
	#superclass : #AffineGroup,
	#category : #'Mathematics-Groups-Affine'
}

{ #category : #testing }
SpecialEuclideanGroup >> includes: anAffineMap [
	^ anAffineMap domain = space and: [anAffineMap isEndomorphism and: [anAffineMap isIsometry and: [anAffineMap matrix determinant = space scalars one]]]
]

{ #category : #operations }
SpecialEuclideanGroup >> linear [
	^ space direction rotations
]

{ #category : #printing }
SpecialEuclideanGroup >> shortName [
	^ 'SE'
]
