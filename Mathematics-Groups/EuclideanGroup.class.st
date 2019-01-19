"
The Euclidean group E(n) or ISO(n), the symmetry group of n-dimensional Euclidean space. Its elements are the isometries associated with the Euclidean metric, and are called Euclidean motions (they are affine maps).

E(n) includes the subgroup E*(n) or SE(n) of isometries preserving orientation, also called rigid motions or special Euclidean group.
"
Class {
	#name : #EuclideanGroup,
	#superclass : #AffineGroup,
	#category : #'Mathematics-Groups-Affine'
}

{ #category : #random }
EuclideanGroup >> atRandom: aRandom [
	^ AffineMap linearPart: (space direction automorphisms orthogonal atRandom: aRandom) translation: (space atRandom: aRandom)
]

{ #category : #random }
EuclideanGroup >> atRandom: aRandom bits: bitSize [
	| n |
	n := bitSize sqrtFloor.
	^ AffineMap linearPart: (space direction automorphisms orthogonal atRandom: aRandom bits: bitSize - n) translation: (space atRandom: aRandom bits: n)
]

{ #category : #accessing }
EuclideanGroup >> dimension [
	| n |
	n := space dimension.
	^ n * (n + 1) / 2
]

{ #category : #testing }
EuclideanGroup >> includes: anAffineMap [
	^ anAffineMap domain = space and: [anAffineMap isEndomorphism and: [anAffineMap isIsometry]]
]

{ #category : #operations }
EuclideanGroup >> linear [
	^ space direction automorphisms orthogonal
]

{ #category : #printing }
EuclideanGroup >> shortName [
	^ 'E'
]

{ #category : #operations }
EuclideanGroup >> special [
	"Answer the special Euclidean group SE(A), the group of direct isometries, i.e. isometries preserving orientation, also called 'rigid motions'. This is a subgroup of the receiver."
	^ SpecialEuclideanGroup on: space
]
