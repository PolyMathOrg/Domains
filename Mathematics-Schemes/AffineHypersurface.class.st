"
Affine algebraic hypersurfaces, i.e. schemes of codimension 1 over an affine space. They can be defined by a single polynomial (the defining ideal is principal).
"
Class {
	#name : #AffineHypersurface,
	#superclass : #AffineVariety,
	#category : #'Mathematics-Schemes-Affine'
}

{ #category : #'instance creation' }
AffineHypersurface class >> polynomial: aPolynomial [
	^ self coordinateRing: aPolynomial parent / aPolynomial
]

{ #category : #accessing }
AffineHypersurface >> degree [
	"The degree of a hypersurface is the total degree of the defining polynomial."
	^ self polynomial degree
]

{ #category : #accessing }
AffineHypersurface >> dimension [
	^ self ambient dimension - 1
]

{ #category : #operations }
AffineHypersurface >> multiplicityAt: aTuple [
	self scalars isField ifFalse: [DomainError signal: 'not over a field'].
	^ (self - aTuple) polynomial order
]

{ #category : #morphic }
AffineHypersurface >> plot [
	(self scalars isField and: [self scalars isReal and: [self ambient dimension = 3]])
		ifFalse: [^ DomainError signal].
	^ ImplicitSurfacePlotMorph new polynomial: self polynomial
]

{ #category : #accessing }
AffineHypersurface >> polynomial [
	^ self ideal generator
]
