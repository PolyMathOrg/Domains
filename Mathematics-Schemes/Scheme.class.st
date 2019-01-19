"
Abstract superclass for schemes. Subclasses implement particular types of schemes.

An important class of schemes are those defined by polynomial equations in some ambient space. See subclasses AffineVariety and ProjectiveVariety, which are closed subschemes of affine and projective space respectively. See also RationalPoint and subclasses.
"
Class {
	#name : #Scheme,
	#superclass : #Domain,
	#category : #'Mathematics-Schemes'
}

{ #category : #elements }
Scheme >> ! anObject [
	anObject isTuple ifTrue: [^ self pointAt: anObject].
	(anObject isKindOf: RationalPoint) ifTrue: [^ self pointAt: anObject coordinates].
	DomainError signal
]

{ #category : #operations }
Scheme >> apply: aMorphism [
	"Answer the image of aMorphism applied to the receiver, assuming the receiver is a subscheme of the domain of aMorphism."
	^ (aMorphism restrictedTo: self) image
]

{ #category : #accessing }
Scheme >> base [
	"Answer the base scheme of the receiver."
	^ self propertyAt: #base ifAbsent: [ZZ spec]
]

{ #category : #accessing }
Scheme >> codimension [
	^ self ambient dimension - self dimension
]

{ #category : #accessing }
Scheme >> dimension [
	^ self subclassResponsibility
]

{ #category : #operations }
Scheme >> divisors [
	"Answer the divisors class group of the receiver."
	^ DivisorsGroup on: self
]

{ #category : #operations }
Scheme >> divisorsOver: aRing [
	"Answer the divisors class group of the receiver."
	^ DivisorsGroup on: self over: aRing
]

{ #category : #morphisms }
Scheme >> embedding [
	"Answer the embedding morphism associated to the receiver.
	By default this is the canonical embedding into its ambient space.
	When the receiver was constructed as an affine patch or neighborhood at a point of another scheme, this is the embedding into the original scheme."
	^ self propertyAt: #embedding ifAbsent: [self inclusion]
]

{ #category : #accessing }
Scheme >> genus [
	"Answer the geometric genus of the receiver."
	^ self subclassResponsibility
]

{ #category : #testing }
Scheme >> isAffine [
	^ false
]

{ #category : #testing }
Scheme >> isCurve [
	^ self dimension = 1
]

{ #category : #testing }
Scheme >> isHypersurface [
	^ self codimension = 1
]

{ #category : #testing }
Scheme >> isInitial [
	^ false
]

{ #category : #testing }
Scheme >> isIntegral [
	^ self isReduced and: [self isIrreducible]
]

{ #category : #testing }
Scheme >> isPlanar [
	^ self ambient dimension = 2
]

{ #category : #testing }
Scheme >> isProjective [
	^ false
]

{ #category : #testing }
Scheme >> isSingular [
	"Answer true if the receiver has s singular point or fails to be equidimensional over an algebraic closure of its base field."
	^ self isSmooth not
]

{ #category : #testing }
Scheme >> isSmooth [
	"Answer true if the receiver is nonsingular."
	^ self propertyAt: #isSmooth ifAbsentPut: [self singular dimension < 0]
]

{ #category : #testing }
Scheme >> isSmoothAt: aTuple [
	self propertyAt: #isSmooth ifPresent: [:aBoolean| aBoolean ifTrue: [^ true]].
	(self satisfies: aTuple) ifFalse: [DomainError signal: 'point not in this scheme'].
	^ (self singular satisfies: aTuple) not
]

{ #category : #testing }
Scheme >> isSurface [
	^ self dimension = 2
]

{ #category : #testing }
Scheme >> isTerminal [
	^ false
]

{ #category : #points }
Scheme >> points [
	"Answer the rational points of the receiver."
	^ self pointsOver: self ambient scalars
]

{ #category : #points }
Scheme >> pointsCount [
	^ self pointsCountOver: self scalars
]

{ #category : #points }
Scheme >> pointsCount: n [
	"If the receiver is defined over a finite field GF(q), answer the number of rational points over GF(q^k) for all k in 1..n."
	^ (1 to: n) collect: [:k| self pointsCountOver: (self scalars extensionDegree: k)]
]

{ #category : #points }
Scheme >> pointsCountOver: aRing [
	"Naive count of rational points on the receiver."
	| answer |
	answer := 0.
	self pointsOver: aRing do: [:each| answer := answer + 1].
	^ answer
]

{ #category : #points }
Scheme >> pointsOver: aRing [
	"Answer the K-rational points on the receiver, where K is aRing."
	^ PointSet from: aRing spec to: self
]

{ #category : #points }
Scheme >> pointsOver: aRing do: aBlock [
	"Naive enumeration of rational points on the receiver."
	self ambient pointsOver: aRing do: [:each| (self satisfies: each coordinates) ifTrue: [aBlock value: (self pointAt: each coordinates)]]
]

{ #category : #operations }
Scheme >> subscheme: anObject [
	"Answer the subscheme defined by anObject, as subscheme of the ambient space.
	This makes sense, for example, for closed subschemes of affine or projective space, and anObject can be an element or an ideal of the coordinate ring."
	^ 'self ï (self ambient subscheme: anObject)'
]
