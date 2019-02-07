"
Quotients of polynomial rings. They are called affine rings or affine algebras because they are finitely-generated (commutative) algebras and they are the coordinate rings of affine varieties (closed subschemes of affine space, see AffineVariety). They are also sometimes called the 'rings of regular functions' (on affine varieties). Their elements are RegularFunctions.

When the coefficients ring is a field K and the relations ideal I is maximal, the affine algebra K[X]/I is a field. In this way, affine algebras are multivariate generalizations of number fields and algebraic function fields.
"
Class {
	#name : #AffineRing,
	#superclass : #QuotientRing,
	#category : #'Mathematics-Schemes-Affine'
}

{ #category : #elements }
AffineRing >> ! anObject [
	(self scalars includes: anObject)
		ifTrue: [ ^ self project: (self base constant: anObject) ].
	^ super ! anObject
]

{ #category : #converting }
AffineRing >> asModule [
"	^ FreeModule
		basis: ((1 to: self degree) collect: [:i| self x ^ (i-1)])
		coordinates: [:aVector| self scalars tuple: self degree evaluating: [:i| aVector representative coefficientAtDegree: i-1]]
		over: self scalars
"
	self notYetImplemented
]

{ #category : #accessing }
AffineRing >> characteristic [
	^ self base characteristic
]

{ #category : #accessing }
AffineRing >> degree [
	^ self relations degree "conflicts with AlgebraicExtension>>degree?"
]

{ #category : #accessing }
AffineRing >> dimension [
	"Answer the Krull dimension of the receiver. Seen as a field extension, this is its transcendence degree."
	"Derksen, Kemper, 'Computational Invariant Theory', 2002, Algorithm 1.2.4 (Dimension of an ideal)."
	self relations isZero ifTrue: [^ self base dimension].
	self isTrivial ifTrue: [^ -1]. "i.e., the ideal is the whole polynomial ring"
	self scalars isField ifFalse: [self notYetImplemented].
	^ self relations maximallyIndependentIndeterminates size
]

{ #category : #private }
AffineRing >> elementClass [
	^ RegularFunction
]

{ #category : #morphisms }
AffineRing >> embed: anObject [
	"Answer the embedding of an element of the coefficients ring into the receiver."
	^ self project: (self base embed: anObject)
]

{ #category : #morphisms }
AffineRing >> embedding [
	"Answer the ring homomorphism that embeds the coefficients ring into the receiver."
	^ self propertyAt: #embedding ifAbsentPut: [(self scalars to: self evaluating: [:x| self embed: x]) name: 'i']
"	^ self projection î self base embedding"
]

{ #category : #morphisms }
AffineRing >> from: aDomain [
	aDomain = self scalars ifTrue: [^ self embedding].
	'aDomain  self scalars ifNotNil: [:aMorphism| ^ self embedding î aMorphism].'.
	^ super from: aDomain
]

{ #category : #operations }
AffineRing >> hilbertSeries [
	"Answer the Hilbert series of the receiver."
	^ self hilbertSeriesAt: (QQ polynomialsIn: #(t)) fractions x
]

{ #category : #operations }
AffineRing >> hilbertSeriesAt: t [
	"Answer the Hilbert series of the receiver."
	^ (self base hilbertSeriesAt: t) - (self relations hilbertSeriesAt: t)
]

{ #category : #accessing }
AffineRing >> indeterminates [
	^ self base indeterminates
]

{ #category : #testing }
AffineRing >> isGlobal [
	^ self base isGlobal
]

{ #category : #testing }
AffineRing >> isGraded [
	^ self base isGraded and: [self relations isHomogeneous]
]

{ #category : #testing }
AffineRing >> isMultivariate [
	^ self base isMultivariate
]

{ #category : #testing }
AffineRing >> isUnivariate [
	^ self base isUnivariate
]

{ #category : #operations }
AffineRing >> localization [
	"Answer the localization of the receiver at <x1,...,xn>. This is achieved by choosing a local ordering.
	Objects defined in this localization contain geometric information (usually only) about a Zariski neighbourhood of 0 in K^n, while objects in the global ring contain geometric information whish is valid in the whole affine space K^n."
	self isGlobal ifFalse: [DomainError signal: 'the ring is not global'].
	^ self orderedBy: #lglex
]

{ #category : #accessing }
AffineRing >> monomials [
	"Answer the monoid of monomials of the receiver."
	^ self base monomials
]

{ #category : #converting }
AffineRing >> orderedBy: aMonomialOrdering [
	^ self class mod: (self relations orderedBy: aMonomialOrdering)
]

{ #category : #accessing }
AffineRing >> ordering [
	^ self base ordering
]

{ #category : #operations }
AffineRing >> proj [
	"Answer the projective spectrum of the receiver, Proj(R)."
	self relations isHomogeneous ifFalse: [^ DomainError signal: 'not a quotient by a homogeneous ideal, not properly graded'].
	^ ProjectiveVariety coordinateRing: self
]

{ #category : #operations }
AffineRing >> raisedTo: n [

	(n isInteger and: [ self isMultivariate ])
		ifFalse: [ ^ super raisedTo: n ].
	^ MultivariateTupleModule new: n over: self
]

{ #category : #accessing }
AffineRing >> rank [
	"Answer the number of indeterminates in the receiver."
	^ self base rank
]

{ #category : #accessing }
AffineRing >> scalars [
	"Answer the coefficients ring of the receiver."
	^ self base scalars
]

{ #category : #operations }
AffineRing >> spec [
	"Answer the spectrum of the receiver, Spec(R/I) as subscheme of Spec(R)."
	^ AffineVariety coordinateRing: self
]

{ #category : #accessing }
AffineRing >> vectorSpaceDimension [
	"Answer the dimension of the receiver as vector space over the coefficients field."
	self relations isZeroDimensional ifFalse: [^ Infinity positive].
	self notYetImplemented
]

{ #category : #elements }
AffineRing >> x [
	^ self x: 1
]

{ #category : #elements }
AffineRing >> x: anInteger [
	^ self project: (self base x: anInteger)
]

{ #category : #elements }
AffineRing >> y [
	^ self x: 2
]

{ #category : #elements }
AffineRing >> z [
	^ self x: 3
]

{ #category : #operations }
AffineRing >> í [ aRing
	"Answer the tensor product of the receiver with the argument."
	| R relations |
	((aRing isKindOf: AffineRing) and: [aRing scalars = self scalars])
		ifFalse: [^ self notYetImplemented].
	R := self base í aRing base.
	relations := OrderedCollection new.
	self relations generators do: [:f| relations add: R ! f].
	aRing relations generators do: [:g| relations add: (R ! g substitute: [:i| i + self base rank])].
	^ R / relations
]
