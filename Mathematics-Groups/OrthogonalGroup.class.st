"
O(V), the Orthogonal Group of a vector space V. This is the group of automorphisms that preserve the inner product.

"
Class {
	#name : #OrthogonalGroup,
	#superclass : #LinearGroup,
	#category : #'Mathematics-Groups-Linear'
}

{ #category : #operations }
OrthogonalGroup >> affine [
	^ EuclideanGroup on: space
]

{ #category : #operations }
OrthogonalGroup >> asMatrixGroup [
	^ OrthogonalMatrixGroup on: space coordinates
]

{ #category : #random }
OrthogonalGroup >> atRandom: aRandom [
	| answer v |
	answer := space id.
	space dimension "heuristic"
		timesRepeat:
			[[(v := space atRandom: aRandom) isZero] whileTrue.
			answer := answer compose: (self reflectionAt: v)].
	^ answer
]

{ #category : #random }
OrthogonalGroup >> atRandom: aRandom bits: bitSize [
	| answer v |
	answer := space id.
	space dimension "heuristic"
		timesRepeat:
			[[(v := space atRandom: aRandom bits: bitSize / space dimension) isZero] whileTrue.
			answer := answer compose: (self reflectionAt: v)].
	^ answer
]

{ #category : #testing }
OrthogonalGroup >> contains: aLinearMap [
	"Answer true if the receiver contains the given element of its ambient."
	^ aLinearMap isOrthogonal
]

{ #category : #operations }
OrthogonalGroup >> coxeter: aMatrix [
	"Answer the geometric Coxeter group associated with the Coxeter matrix aMatrix."
	^ self notYetImplemented
]

{ #category : #elements }
OrthogonalGroup >> reflectionAt: aVector [
	"Answer the orthogonal reflection with mirror hyperplane perpendicular to aVector."
	^ space endomorphisms evaluating: [:v| v - ((space innerProduct value: {v. aVector}) * 2 / (space innerProduct value: {aVector. aVector}) * aVector)]
]

{ #category : #printing }
OrthogonalGroup >> shortName [
	^ 'O'
]

{ #category : #operations }
OrthogonalGroup >> special [
	^ SpecialOrthogonalGroup on: space
]
