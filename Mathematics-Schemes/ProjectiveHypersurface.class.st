"
Projective algebraic hypersurfaces, i.e. schemes of codimension 1 over a projective space. They can be defined by a single homogeneous polynomial (the defining ideal is principal).
"
Class {
	#name : #ProjectiveHypersurface,
	#superclass : #ProjectiveVariety,
	#category : #'Mathematics-Schemes-Projective'
}

{ #category : #'instance creation' }
ProjectiveHypersurface class >> polynomial: aPolynomial [
	^ self coordinateRing: aPolynomial parent / aPolynomial
]

{ #category : #accessing }
ProjectiveHypersurface >> degree [
	"The degree of a projective hypersurface is the degree of the defining homogeneous polynomial."
	^ self polynomial degree
]

{ #category : #accessing }
ProjectiveHypersurface >> dimension [
	^ self ambient dimension - 1
]

{ #category : #accessing }
ProjectiveHypersurface >> dual [
	"Answer the projective dual of the receiver."
	self notYetImplemented
]

{ #category : #'as yet unclassified' }
ProjectiveHypersurface >> gradient [
	| f F |
	f := self polynomial.
	F := self ambient functionField.
	"actually should go to the dual projective space"
	^ RationalMap from: self to: self ambient representatives: ((1 to: F rank) collect: [:i| F ! (f derivativeIn: i)])
]

{ #category : #accessing }
ProjectiveHypersurface >> polynomial [
	^ self ideal generator
]
