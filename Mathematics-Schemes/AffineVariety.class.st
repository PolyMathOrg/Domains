"
Closed subschemes of an affine space (see AffineSpace). Their coordinate rings are quotients of multivariate polynomial rings by an ideal (also called affine rings or affine algebras, see AffineRing). Their rational points are AffinePoints.

These are schemes, not classical algebraic varieties. Here the name 'variety' only means that they are defined by polynomial equations. The integral (reduced and irreducible) closed subschemes of affine space over an algebraically closed field correspond to the classical affine algebraic varieties.

"
Class {
	#name : #AffineVariety,
	#superclass : #AffineScheme,
	#category : #'Mathematics-Schemes-Affine'
}

{ #category : #examples }
AffineVariety class >> circle [
	"The unit circle in the rational affine plane:"

	| R x y I |
	R := QQ polynomialsIn: #(x y).
	x := R x.
	y := R y.
	I := R * ((x raisedTo:2) + (y raisedTo: 2) - 1).
	^ (R / I) spec
]

{ #category : #examples }
AffineVariety class >> clebschCubic [
	"The Clebsch cubic as affine scheme in Q^3.
	This is the unique cubic surface that has Sym(5) as symmetry group."
	| A x y z f |
	A := AffineSpace new: #(x y z) over: QQ.
	x := A coordinateRing x.
	y := A coordinateRing y.
	z := A coordinateRing z.
	'f := x^3 + (y^3) + (z^3) * 81
				+ (x^2*y + (x^2*z) + (x*(y^2)) + (x*(z^2)) + (y^2*z) + (y*(z^2)) * -189)
				+ (x*y*z * 54)
				+ (x*y + (x*z) + (y*z) * 126)
				+ (x^2 + (y^2) + (z^2) * -9)
				+ 1'.
	^ A subscheme: f
]

{ #category : #'instance creation' }
AffineVariety class >> coordinateRing: anAffineRing [
	self == AffineVariety ifFalse: [^ super coordinateRing: anAffineRing].
	(anAffineRing relators size = 1 and: [anAffineRing relators anyOne degree > 0]) ifTrue:
		[anAffineRing rank = 2 ifTrue: [^ AffinePlaneCurve coordinateRing: anAffineRing].
		^ AffineHypersurface coordinateRing: anAffineRing].
	^ super coordinateRing: anAffineRing
]

{ #category : #'instance creation' }
AffineVariety class >> newFrom: anObject [
	(anObject isKindOf: AffineVariety) ifTrue: [^ self coordinateRing: anObject coordinateRing].
	^ super newFrom: anObject
]

{ #category : #examples }
AffineVariety class >> romanSurface [
	"The Roman surface or Steiner surface.
	This is a self-intersecting mapping of the real projective plane into affine 3-space.
	It was discovered by Jakob Steiner when he was in Rome in 1844."
	
	| A r |
	A := AffineSpace new: #(x y z) over: QQ.
	r := 1.
	^ A
		subscheme:
			A coordinateRing
				! [ :x :y :z | 
					x * (y raisedTo: 2) + (y * z raisedTo: 2) + (z * x raisedTo: 2)
						- (x * y * z * r squared) ]
]

{ #category : #examples }
AffineVariety class >> twistedCubic [
	"This is the twisted cubic affine variety, parameterized by (x, x^2, x^3) in C^3."
	| A x y z |
	A := AffineSpace new: #(x y z) over: QQ algebraicClosure.
	x := A coordinateRing x.
	y := A coordinateRing y.
	z := A coordinateRing z.
	^ 'A subscheme: {y - (x^2). z - (x^3)}'
]

{ #category : #examples }
AffineVariety class >> whitneyUmbrella [
	"This is Whitney's umbrella in affine space Q^3."

	| A |
	A := AffineSpace new: #(x y z) over: QQ.
	^ A subscheme: A coordinateRing ! [:x :y :z| (x raisedTo:2)*y - (z raisedTo: 2)]
]

{ #category : #operations }
AffineVariety >> + aTuple [
	"Answer a new affine varieity that is the translation of the receiver by aTuple.
	The origin is mappet to aTuple (any point p on the receiver is mapped to p + aTuple)."
	| dx |
	dx := self ambient coordinateRing generators - aTuple.
	^ self ambient subscheme: (self ideal apply: [:f| f value: dx])
]

{ #category : #operations }
AffineVariety >> - aScheme [
	"Answer the difference of the receiver with the argument, whose associated ideal is the ideal (colon) quotient of the respective ideals.
	This is the closure of the result of removing from the receiver the points in the intersection with the argument, counted with multiplicity. (See also the 'complement' >>-)."
	aScheme isTuple ifTrue: [^ self + aScheme negated].
	self ambient = aScheme ambient ifFalse: [^ DomainError signal: 'ambients don''t match'].
	^ 'self ambient subscheme: self ideal ˜ aScheme ideal'
]

{ #category : #comparing }
AffineVariety >> = anObject [
	^ (anObject isKindOf: AffineVariety) and: [self ideal = anObject ideal]
]

{ #category : #operations }
AffineVariety >> \ aScheme [
	"Answer the (closure of the) complement of the argument in the receiver.
	This is the closure of the result of removing from the receiver *all* points in the intersection with the argument, irrespective of multiplicity. (See also the 'difference' >>\)."
	self ambient = aScheme ambient ifFalse: [^ DomainError signal: 'ambients don''t match'].
	^ self ambient subscheme: (self ideal saturation: aScheme ideal)
]

{ #category : #converting }
AffineVariety >> asCurve [
	^ self ambient isPlane
		ifTrue: [self as: AffinePlaneCurve]
		ifFalse: [self as: AffineCurve]
]

{ #category : #converting }
AffineVariety >> asHypersurface [
	^ self ambient isPlane
		ifTrue: [self as: AffinePlaneCurve]
		ifFalse: [self as: AffineHypersurface]
]

{ #category : #operations }
AffineVariety >> cartProd: anAffineVariety [ "◊ "
	"Answer the cartesian product of the receiver and the argument."
	self scalars = anAffineVariety scalars ifFalse: [self error: 'scalars don''t match'].
	(anAffineVariety isKindOf: AffineVariety) ifFalse: [self notYetImplemented].
	^ '(self coordinateRing í anAffineVariety coordinateRing) spec
			propertyAt: #ambient put: self ambient ◊ anAffineVariety ambient;
			yourself'
]

{ #category : #testing }
AffineVariety >> contains: anIdeal [
	"Answer true if the receiver contains the given point (a prime ideal)."
	^ self ideal >= anIdeal
]

{ #category : #operations }
AffineVariety >> decomposition [
	"Answer the irreducible components of the receiver."
	^ self ideal associatedPrimes collect: [:each| self subscheme: each]
]

{ #category : #comparing }
AffineVariety >> hash [
	^ self ideal hash
]

{ #category : #accessing }
AffineVariety >> ideal [
	"Answer the defining ideal of the receiver."
	^ self coordinateRing relations
]

{ #category : #testing }
AffineVariety >> isComplete [
	^ self isFinite
]

{ #category : #testing }
AffineVariety >> isEmpty [
	"Answer true if the receiver has no points over any algebraic closure of its base field.
	Ref. Algorithmic Algebra, B. Mishra, pag. 142-145."
	self ideal isTrivial ifTrue: [^ true].
"	(self scalars isField and: [self scalars isAlgebraicallyClosed])
		ifFalse: [self error: 'the ground field is not algebraically closed'].
"	^ false
]

{ #category : #testing }
AffineVariety >> isEquidimensional [
	"Answer true if the receiver is pure dimensional or equidimensional, i.e. if the dimension of the local ring at p is independent of p."
	^ self singular dimension < 0
]

{ #category : #testing }
AffineVariety >> isFinite [
	"This works for any Groebner basis, no matter the ordering."
	"Does this work for non integral schemes?"
	self ideal scalars indeterminates do: [:x|
		(self ideal groebnerBasis anySatisfy: [:f| | d m | m := f leadingMonomial. d := m degree. d > 0 and: [d = (m degreeIn: x)]])
			ifFalse: [^ false]].
	^ true
]

{ #category : #testing }
AffineVariety >> isLinear [
	^ self reduced ideal generators allSatisfy: [:each| each isLinear]
]

{ #category : #operations }
AffineVariety >> multiplicityAt: aTuple [
	"Answer the multiplicity at the given point."
	^ ((self - aTuple) ideal basisWithOrdering: #lglex) max: [:each| each order]
]

{ #category : #points }
AffineVariety >> pointAt: aTuple [
	^ AffinePoint on: self coordinates: aTuple
]

{ #category : #operations }
AffineVariety >> primaryComponents [
	"Answer the irredundant primary components of the receiver."
	^ self ideal primaryComponents collect: [:each| self subscheme: each]
]

{ #category : #operations }
AffineVariety >> primeComponents [
	"Answer the irredundant prime components of the receiver."
	^ self ideal primeComponents collect: [:each| self subscheme: each]
]

{ #category : #operations }
AffineVariety >> project: anIndeterminate [
	"Answer the projection of the receiver by eliminating the given indeterminate.
	This is the intersection of the receiver with a linear subspace {xi = 0}."
	^ self ambient subscheme: (self ideal eliminate: anIndeterminate)
]

{ #category : #operations }
AffineVariety >> projectiveClosure [
	"Answer the projective closure of the receiver. If the receiver is an affine patch of a projective scheme, answer the original projective scheme. Otherwise the projective closure will be a projective scheme over the projective closure of the ambient space of the receiver, and the receiver will be the last affine patch."
	^ self projectiveEmbedding codomain
]

{ #category : #morphisms }
AffineVariety >> projectiveEmbedding [
	"Answer the map that sends the receiver to its projective closure.
	If the receiver was originally constructed as an affine patch of a projective scheme, answer the map to the original projective scheme. Otherwise, the projective closure will be constructed as a projective scheme over the projective closure of the ambient space of the receiver, and the receiver will be its last affine patch."
	| P map patches |
	self propertyAt: #projectiveEmbedding ifPresent: [:aRationalMap| ^ aRationalMap].
	P := self ideal homogenized quotientRing proj.
	map := self to: P evaluating: [:x| x homogenizedIn: P ambient rank].
	patches := Array new: P ambient rank.
	patches at: patches size put: self.
	P propertyAt: #affinePatches put: patches.
	^ self propertyAt: #projectiveEmbedding put: map
]

{ #category : #operations }
AffineVariety >> projectivized [
	"Answer the projectivization of the receiver."
	^ self coordinateRing proj
]

{ #category : #operations }
AffineVariety >> reduced [
	"Answer the reduced subscheme of the receiver."
	^ self propertyAt: #reducedSubscheme ifAbsentPut: [self ambient subscheme: self ideal radical]
]

{ #category : #testing }
AffineVariety >> satisfies: aTuple [
	"Answer true if the defining equations of the receiver satisfy the argument, assuming it's the coordinates of a rational point in the ambient space."
	^ self ideal generators allSatisfy: [:each| (each value: aTuple) isZero]
]

{ #category : #operations }
AffineVariety >> singular [
	"Answer the subscheme defined by the appropriately sized minors of the jacobian matrix of the receiver.
	If the receiver is not equidimensional, its lower-dimensional components will be contained in this scheme whether they are singular or not.
	(See Eisenbud 'Commutative Algebra' Ch. 20, re Fitting ideal.)"
	^ self propertyAt: #singularSubscheme ifAbsentPut: [self subscheme: self ideal singular]
]

{ #category : #private }
AffineVariety >> species [
	^ AffineVariety
]

{ #category : #operations }
AffineVariety >> tangentConeAt: aTuple [
	"Answer the affine tangent cone at the given point."
	| R I |
	R := self ambient coordinateRing.
	I := (self - aTuple) ideal.
	^ (self ambient subscheme: ((I basisWithOrdering: #lglex) collect: [:each| R ! each leadingForm])) + aTuple
]

{ #category : #operations }
AffineVariety >> tangentSpaceAt: aTuple [
	"Answer the affine tangent space at the given point."
	| R I |
	R := self ambient coordinateRing.
	I := (self - aTuple) ideal.
	^ (self ambient subscheme: (I generators collect: [:f| (1 to: R rank) sum: [:i| (R x: i) * (f derivativeIn: i) independentCoefficient]])) + aTuple
]

{ #category : #morphisms }
AffineVariety >> to: aScheme evaluating: aBlock [
	^ RationalMap from: self to: aScheme evaluating: aBlock
]

{ #category : #morphisms }
AffineVariety >> to: aScheme representatives: anArrayOfRationalFunctions [
	^ RationalMap from: self to: aScheme representatives: anArrayOfRationalFunctions
]
