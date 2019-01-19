"
The (general) affine group of an affine space, consisting of all invertible affine transformations from the space into itself.

If the scalar field is R, C or H, this is a Lie group.
"
Class {
	#name : #GeneralAffineGroup,
	#superclass : #AffineGroup,
	#category : #'Mathematics-Groups-Affine'
}

{ #category : #random }
GeneralAffineGroup >> atRandom: aRandom [
	^ (space direction automorphisms atRandom: aRandom) + (space atRandom: aRandom)
]

{ #category : #random }
GeneralAffineGroup >> atRandom: aRandom bits: bitSize [
	| n |
	n := bitSize sqrtFloor.
	^ (self space automorphisms atRandom: aRandom bits: bitSize - n) + (self space atRandom: aRandom bits: n)
]

{ #category : #operations }
GeneralAffineGroup >> euclidean [
	"Answer the Euclidean group E(A), the group of isometries, i.e. distance-preserving morphisms, also called 'motionss'. This is a subgroup of the receiver."
	^ EuclideanGroup on: space
]

{ #category : #testing }
GeneralAffineGroup >> includes: anAffineMap [
	^ anAffineMap domain = space and: [anAffineMap isEndomorphism and: [anAffineMap isMonomorphism]]
]

{ #category : #operations }
GeneralAffineGroup >> linear [
	^ space direction automorphisms
]

{ #category : #printing }
GeneralAffineGroup >> shortName [
	^ 'GA'
]

{ #category : #operations }
GeneralAffineGroup >> special [
	^ SpecialAffineGroup on: space
]
