"
Projective closed subschemes of a projective space (see ProjectiveSpace). Their homogeneous coordinate rings are quotient rings of multivariate polynomial rings by a homogeneous ideal, i.e. graded affine algebras. Their rational points are ProjectivePoints.

These are schemes, and not classical algebraic varieties (they don't need to be reduced, irreducible nor over an algebraically closed field). Here the name 'variety' only means that they are defined by polynomial equations.
"
Class {
	#name : #ProjectiveVariety,
	#superclass : #Scheme,
	#category : #'Mathematics-Schemes-Projective'
}

{ #category : #examples }
ProjectiveVariety class >> cayleyCubic [
	"The Cayley cubic as projective surface.
	This is the unique cubic surface that has 4 ordinary nodes.
	It is a degeneration of the Clebsh cubic and has Sym(4) as its symmetry group."
	| P |
	P := ProjectiveSpace new: #(x y z w) over: QQ.
	^ P subscheme: P coordinateRing ! [:x :y :z :w| x*y*z + (x*y*w) + (x*z*w) + (y*z*w)]
]

{ #category : #'instance creation' }
ProjectiveVariety class >> coordinateRing: anAffineRing [
	self == ProjectiveVariety ifFalse: [^ self new coordinateRing: anAffineRing].
	anAffineRing relators size = 1 ifTrue:
		[| f |
		f := anAffineRing relators anyOne.
		f degree > 0 ifTrue:
			[anAffineRing rank = 3 ifTrue:
				[f degree = 1 ifTrue: [^ RationalCurve coordinateRing: anAffineRing].
				f degree = 2 ifTrue: [^ Conic coordinateRing: anAffineRing].
				f degree = 3 ifTrue: ["elliptic curve"].
				^ ProjectivePlaneCurve coordinateRing: anAffineRing].
			^ ProjectiveHypersurface coordinateRing: anAffineRing]].
	^ self new coordinateRing: anAffineRing
]

{ #category : #examples }
ProjectiveVariety class >> fermat4 [
	"The 4th Fermat curve."
	| P |
	P := ProjectiveSpace new: #(x y z) over: QQ.
	^ 'P subscheme: P coordinateRing ! [:x :y :z| x^4 + (y^4) - (z^4)]'
]

{ #category : #examples }
ProjectiveVariety class >> fermat: n [
	"The n-th Fermat curve."
	| P |
	P := ProjectiveSpace new: #(x y z) over: QQ.
	^ 'P subscheme: (P coordinateRing generate: [:x :y :z| x^n + (y^n) - (z^n)])'
]

{ #category : #examples }
ProjectiveVariety class >> kleinQuartic [
	"This is a projective variety, a curve in P^2(C)."
	| P x y z |
	P := ProjectiveSpace new: 2 over: QQ.
	x := P coordinateRing x.
	y := P coordinateRing y.
	z := P coordinateRing z.
	^ 'P subscheme: {x^3*y + (y^3*z) + (z^3*x)}'
]

{ #category : #'instance creation' }
ProjectiveVariety class >> newFrom: anObject [
	(anObject isKindOf: ProjectiveVariety) ifTrue: [^ self coordinateRing: anObject coordinateRing].
	^ super newFrom: anObject
]

{ #category : #comparing }
ProjectiveVariety >> = anObject [
	^ (anObject isKindOf: self species) and: [self saturated coordinateRing = anObject saturated coordinateRing]
]

{ #category : #accessing }
ProjectiveVariety >> affineCone [
	"If the receiver is defined by an homogeneous ideal I, the affine cone is the affine variety defined by I."
	^ self coordinateRing spec
]

{ #category : #accessing }
ProjectiveVariety >> ambient [
	^ self propertyAt: #ambient ifAbsent: [self coordinateRing base proj]
]

{ #category : #accessing }
ProjectiveVariety >> anyPatch [
	^ self patch: self ambient rank
]

{ #category : #accessing }
ProjectiveVariety >> arithmeticGenus [
	"Answer the arithmetic genus of the receiver."
	self ambient isOrdinaryProjectiveSpace ifFalse: [^ self error: 'not ordinary projective space'].
	self notYetImplemented
]

{ #category : #converting }
ProjectiveVariety >> asCurve [
	^ self ambient isPlane
		ifTrue: [self as: ProjectivePlaneCurve]
		ifFalse: [self as: ProjectiveCurve]
]

{ #category : #converting }
ProjectiveVariety >> asHypersurface [
	^ self ambient isPlane
		ifTrue: [self as: ProjectivePlaneCurve]
		ifFalse: [self as: ProjectiveHypersurface]
]

{ #category : #accessing }
ProjectiveVariety >> base [
	"Answer the base scheme of the receiver."
	^ self scalars spec
]

{ #category : #operations }
ProjectiveVariety >> cartProd: aProjectiveVariety [ "◊ "
	"Answer the cartesian product of the receiver and the argument."
	self scalars = aProjectiveVariety scalars ifFalse: [self error: 'scalars don''t match'].
	(aProjectiveVariety isKindOf: ProjectiveVariety) ifFalse: [self notYetImplemented].
	^ '(self coordinateRing í aProjectiveVariety coordinateRing) proj
			propertyAt: #ambient put: self ambient ◊ aProjectiveVariety ambient;
			yourself'
]

{ #category : #accessing }
ProjectiveVariety >> coordinateRing [
	"Answer the homogeneous coordinate ring."
	^ self propertyAt: #coordinateRing
]

{ #category : #'accessing-private' }
ProjectiveVariety >> coordinateRing: aCommutativeRing [
	self propertyAt: #coordinateRing put: aCommutativeRing
]

{ #category : #operations }
ProjectiveVariety >> decomposition [
	"Answer the irreducible components of the receiver."
	| primes |
	primes := self ideal associatedPrimes.
	"Since the scheme is projective, remove the primes containing the irrelevant ideal:"
	primes := primes reject: [:each| self ambient coordinateRing generators anySatisfy: [:xi| each includes: xi]].
	^ primes collect: [:each| self subscheme: each]
]

{ #category : #accessing }
ProjectiveVariety >> degree [
	| t H |
	t := QQ polynomials fractions x.
	H := self coordinateRing hilbertSeriesAt: t.
	^ '(1 - t) ^ (H orderAt: 1) negated * H value: 1'
]

{ #category : #accessing }
ProjectiveVariety >> degree2 [
	| t H |
	t := QQ polynomials fractions x.
	H := self coordinateRing hilbertSeriesAt: t.
	^ '(1 - t) ^ self coordinateRing dimension * H value: 1'
]

{ #category : #accessing }
ProjectiveVariety >> dimension [
	self flag: #fix. "is this right for projective schemes or should use the Hilbert series?"
	^ self coordinateRing dimension - 1
]

{ #category : #operations }
ProjectiveVariety >> dual [
	"Answer the projective dual of the receiver."
	self notYetImplemented
]

{ #category : #accessing }
ProjectiveVariety >> functionField [
	"If K(X) is the function field of the affine cone, the function field of the projective variety is the subfield of K(X) of homogeneous elements of degree 0 (the grading at degree 0), that is {f/g | f,g in K(X) and g not zero}.
	This is isomorphic to the function field of any affine patch."
	^ self anyPatch functionField
]

{ #category : #comparing }
ProjectiveVariety >> hash [
	^ self saturated coordinateRing hash
]

{ #category : #accessing }
ProjectiveVariety >> ideal [
	"Answer the homogeneous ideal defining the receiver."
	^ self coordinateRing relations
]

{ #category : #testing }
ProjectiveVariety >> isComplete [
	^ true
]

{ #category : #testing }
ProjectiveVariety >> isEmpty [
	"Answer true if the receiver has no points over any algebraic closure of its base field."
	^ self dimension = -1
]

{ #category : #testing }
ProjectiveVariety >> isIrreducible [
	self flag: #fix. "magma does it differently; duplicated in AffineSchema"
	^ self coordinateRing isIntegralDomain
]

{ #category : #testing }
ProjectiveVariety >> isProjective [
	^ true
]

{ #category : #testing }
ProjectiveVariety >> isReduced [
	^ self coordinateRing isReduced
]

{ #category : #private }
ProjectiveVariety >> newPatch: i [
	^ (self ambient patch: i) subscheme: (self ideal dehomogenizedIn: i)
]

{ #category : #converting }
ProjectiveVariety >> over: aRing [
	^ self class coordinateRing: (self coordinateRing over: aRing)
]

{ #category : #accessing }
ProjectiveVariety >> patch: i [
	"Answer the i-th affine patch of the receiver."
	| patches answer map |
	patches := self propertyAt: #affinePatches ifAbsentPut: [Array new: self ambient rank].
	(patches at: i) ifNotNil: [:anAffineVariety| ^ anAffineVariety].
	answer := self newPatch: i.
	map := answer to: self evaluating: [:x| x homogenizedIn: i].
	answer propertyAt: #projectiveEmbedding put: map.
	^ patches at: i put: answer
]

{ #category : #accessing }
ProjectiveVariety >> patches [
	"Answer all the standard affine patches of the receiver."
	^ (1 to: self ambient rank) collect: [:i| self patch: i]
]

{ #category : #points }
ProjectiveVariety >> pointAt: aTuple [
	^ ProjectivePoint on: self coordinates: aTuple
]

{ #category : #printing }
ProjectiveVariety >> printOn: aStream [
		aStream nextPutAll: 'Proj '; print: self coordinateRing
]

{ #category : #operations }
ProjectiveVariety >> reduced [
	"Answer the reduced subscheme of the receiver."
	^ self propertyAt: #reducedSubscheme ifAbsentPut: [self ambient subscheme: self ideal radical]
]

{ #category : #testing }
ProjectiveVariety >> satisfies: aTuple [
	"Answer true if the defining equations of the receiver satisfy the argument, assuming it's the coordinates of a rational point in the ambient space."
	^ self ideal generators allSatisfy: [:each| (each value: aTuple) isZero]
]

{ #category : #private }
ProjectiveVariety >> saturated [
	"Ensure the defining ideal of the receiver is saturated.
	This is important for some operations with projective schemes because projective schemes are not in correspondence with homogeneous ideals (like affine schemes), but they are in correspondence with saturated homogeneous ideals."
	(self propertyAt: #isSaturated ifAbsent: [false]) ifTrue: [^ self].
	self coordinateRing: self ambient coordinateRing / self ideal saturation.
	self propertyAt: #isSaturated put: true
]

{ #category : #accessing }
ProjectiveVariety >> scalars [
	"Answer the base ring of the receiver."
	^ self coordinateRing scalars
]

{ #category : #operations }
ProjectiveVariety >> singular [
	"Answer the subscheme defined by the appropriately sized minors of the jacobian matrix of the receiver.
	If the receiver is not equidimensional, its lower-dimensional components will be contained in this scheme whether they are singular or not.
	(See Eisenbud 'Commutative Algebra' Ch. 20, re Fitting ideal.)"
	^ self propertyAt: #singularSubscheme ifAbsentPut: [self subscheme: self ideal singular]
]

{ #category : #private }
ProjectiveVariety >> species [
	^ ProjectiveVariety
]

{ #category : #operations }
ProjectiveVariety >> tangentSpaceAt: aTuple [
	"Answer the projective tangent space of the receiver at the given point."
	| R |
	self flag: #fix. "this might be wrong, The Geometry of Schemes pag 105"
	R := self ambient coordinateRing.
	^ self ambient subscheme: (self ideal generators collect: [:f| (1 to: R rank) sum: [:i| (R x: i) * ((f derivativeIn: i) value: aTuple)]])
]

{ #category : #morphisms }
ProjectiveVariety >> to: aScheme evaluating: aBlock [
	^ RationalMap from: self to: aScheme evaluating: aBlock
]

{ #category : #morphisms }
ProjectiveVariety >> to: aScheme representatives: anArrayOfRationalFunctions [
	^ RationalMap from: self to: aScheme representatives: anArrayOfRationalFunctions
]

{ #category : #operations }
ProjectiveVariety >> ï [ aScheme
	"Answer the intersection of the receiver and the argument."
	self ambient = aScheme ambient ifFalse: [^ DomainError signal: 'ambients don''t match'].
	^ self ambient subscheme: self ideal + aScheme ideal
]

{ #category : #operations }
ProjectiveVariety >> ñ [ aScheme
	"Answer the union of the receiver and the argument."
	self ambient = aScheme ambient ifFalse: [^ DomainError signal: 'ambients don''t match'].
	^ self ambient subscheme: self ideal ï aScheme ideal

"alternatively:
	^ self class on: self ambient ideal: ideal * aScheme ideal
although the intersection is harder to compute, it behaves better with radicalization, because the intersection of two radical ideals is radical and we don't need to compute radicals again"
]
