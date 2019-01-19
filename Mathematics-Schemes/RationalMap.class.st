"
Rational maps between varieties (closed subschemes of affine or projective space). They are defined by a tuple of rational functions.

Rational maps are partial functions defined in a dense open subset of the domain. The scheme where the a rational map is undefined is called its base scheme (see >>base).

A rational map is called 'regular' if it defines a morphism of varieties (i.e., for affine varieties it is defined by polynomials, and in case of projective varieties it is constant.) A regular map is called 'dominant' if its image is dense in its codomain.

The category of affine varieties or projective varieties with dominant rational maps and the category of function fields are contravariantly equivalent.
"
Class {
	#name : #RationalMap,
	#superclass : #Function,
	#category : #'Mathematics-Schemes'
}

{ #category : #examples }
RationalMap class >> example1TwistedCubicTangentParametrization [
	"Example from Cox's 'Ideals, Varieties and Algorithms' pag. 234.
	Parametrization of the tangent surface of the twisted cubic."
	| A2 A3 |
	A2 := AffineSpace new: #(t u) over: QQ.
	A3 := AffineSpace new: 3 over: QQ.
	^ 'A2 to: A3 evaluatingWithArguments: [:t :u| {t + u. t^2 + (t*u*2). t^3 + (t^2*u*3)}]'
]

{ #category : #examples }
RationalMap class >> example2TwistedCubicTangent [
	"The tangent surface of the twisted cubic."
	^ self example1TwistedCubicTangentParametrization image
]

{ #category : #'instance creation' }
RationalMap class >> from: aDomain to: aCodomain evaluating: anExpression [
	| F |
	F := aDomain ambient functionField.
	^ self from: aDomain to: aCodomain representatives: (anExpression value: (F tuple: aDomain ambient rank evaluating: [:i| F x: i]))
]

{ #category : #'instance creation' }
RationalMap class >> from: aDomain to: aCodomain polynomials: anArrayOfPolynomials [
	| F |
	F := aDomain ambient functionField.
	^ self from: aDomain to: aCodomain representatives: (anArrayOfPolynomials collect: [:each| F embed: each])
]

{ #category : #'instance creation' }
RationalMap class >> from: aDomain to: aCodomain representatives: anArrayOfRationalFunctions [
	((aDomain isProjective or: [aCodomain isProjective]) and: [anArrayOfRationalFunctions anySatisfy: [:any| any isHomogeneous not]])
		ifTrue: [^ self error: 'not homogeneous'].
	^ self new domain: aDomain; codomain: aCodomain; representatives: anArrayOfRationalFunctions
]

{ #category : #arithmetic }
RationalMap >> * anObject [
	^ self species from: self domain to: self codomain representatives: self representatives * anObject
]

{ #category : #arithmetic }
RationalMap >> + aRationalMap [
	aRationalMap isTuple
		ifTrue: [^ self species from: self domain to: self codomain representatives: self representatives + aRationalMap].
	(self domain = aRationalMap domain and: [self codomain = aRationalMap codomain])
		ifFalse: [^ DomainError signal].
	^ self species from: self domain to: self codomain representatives: self representatives + aRationalMap representatives
]

{ #category : #comparing }
RationalMap >> = aRationalMap [
	| I |
	(aRationalMap isKindOf: RationalMap) ifFalse: [^ super = aRationalMap].
	(self domain = aRationalMap domain and: [self codomain = aRationalMap codomain])
		ifFalse: [^ false].
	I := self domain ideal.
	1 to: self size do: [:i| | f g |
		f := self at: i.
		g := aRationalMap at: i.
		(I includes: f numerator * g denominator - (f denominator * g numerator))
			ifFalse: [^ false]].
	^ true
]

{ #category : #converting }
RationalMap >> asRingHomomorphism [
	"Answer the induced ring homomorphism between the coordinate rings.
	This is the adjoint of the Spec functor."
	self isPolynomial ifFalse: [DomainError signal: 'not a polynomial map'].
	^ self codomain coordinateRing to: self domain coordinateRing evaluating: [:f| f value: self representatives]
]

{ #category : #accessing }
RationalMap >> at: anInteger [
	"Answer the anInteger-th component of the receiver (a rational function, an element of the function field of the domain)."
	^ self representatives at: anInteger
]

{ #category : #accessing }
RationalMap >> base [
	"Answer the subscheme of the domain where the receiver is indetermined (because some denominator vanishes)."
	self notYetImplemented.
"this is wrong:"
	^ self domain subscheme: (self representatives collect: [:each| each denominator])
]

{ #category : #operations }
RationalMap >> graph [
	^ 'self domain ◊ self image'
]

{ #category : #operations }
RationalMap >> image [
	"Answer (the Zeriski closure of) the image of the receiver. This is a subscheme of the codomain.
	Performs ideal elimination (a Groebner basis computation with the lexicographical order).
	See PolynomialRingMap>>kernel."
	| A B m n P t embedding generators g I |
	A := self domain ambient coordinateRing.
	B := self codomain ambient coordinateRing.
	m := A rank.
	n := B rank.
	P := self domain scalars polynomialsIn: n + m + 1.
	"the embedding mapping the i-th indeterminate to the (i+n)-th indeterminate in the bigger ring:"
	embedding := A to: P evaluating: [:f| P ! f substitute: [:i| i+n]].
	t := P x: P rank.
	generators := OrderedCollection new.
	g := P one.
	1 to: n do: [:i| | numerator denominator |
		numerator := embedding value: (self representatives at: i) numerator.
		denominator := embedding value: (self representatives at: i) denominator.
		generators add: denominator * (P x: i) - numerator.
		g := g * denominator].
	self domain ideal generators do: [:each| generators add: (embedding value: each)].
	generators add: P one - (g * t).
	I := P * generators eliminateAll: (n+1 to: P rank).
	^ self codomain subscheme: (I generators collect: [:f| B ! f])
]

{ #category : #testing }
RationalMap >> isAffineLinear [
	"Answer true if the receiver is an affine linear map (defined by polynomials of degree 1)."
	^ self representatives allSatisfy: [:each| each isAffineLinear]
]

{ #category : #testing }
RationalMap >> isConstant [
	^ self representatives allSatisfy: [:each| each isConstant]
]

{ #category : #testing }
RationalMap >> isDominant [
	"Answer true if the closure of the image of the receiver is the whole codomain."
	^ self image = self codomain
]

{ #category : #testing }
RationalMap >> isLinear [
	"Answer true if the receiver is a homogeneous linear map (defined by homogeneous linear polynomials, with independent coefficient zero)."
	^ self representatives allSatisfy: [:each| each isLinear]
]

{ #category : #testing }
RationalMap >> isPolynomial [
	"Answer true if the receiver is a polynomial map."
	^ self representatives allSatisfy: [:each| each denominator isConstant]
]

{ #category : #testing }
RationalMap >> isRegular [
	"Answer true if the receiver is defined at all points of its domain."
	(self domain ambient isKindOf: AffineSpace) ifTrue: [^ self isPolynomial].
	(self domain ambient isKindOf: ProjectiveSpace) ifTrue: [^ self isConstant].
	^ DomainError signal
]

{ #category : #operations }
RationalMap >> jacobian [
	"Answer the Jacobian matrix of the receiver."
	^ self domain ambient coordinateRing
		matrix: self codomain ambient rank @ self domain ambient rank
		evaluating: [:i :j| (self representatives at: i) derivativeIn: j]
]

{ #category : #arithmetic }
RationalMap >> negated [
	^ self species from: self domain to: self codomain representatives: self representatives negated
]

{ #category : #printing }
RationalMap >> printOn: aStream [ 
	self codomain isProjective
		ifTrue:
			[aStream nextPut: $[.
			self representatives do: [:each| aStream print: each] separatedBy: [aStream nextPut: $:].
			aStream nextPut: $]]
		ifFalse:
			[aStream nextPut: $(.
			self representatives do: [:each| aStream print: each] separatedBy: [aStream nextPutAll: ', '].
			aStream nextPut: $)]
]

{ #category : #operations }
RationalMap >> projectiveClosure [
	^ self class
		from: self domain projectiveClosure
		to: self codomain projectiveClosure
		representatives: (self representatives collect: [:each| each homogenized])
]

{ #category : #operations }
RationalMap >> pullback: aScheme [
	"Answer the preimage of aScheme. The argument is a subscheme of the codomain, and the answer is a subscheme of the domain."
	^ self domain subscheme: (aScheme ideal apply: self asRingHomomorphism)
]

{ #category : #accessing }
RationalMap >> representatives [
	"Answer the array of representatives of the components of the receiver, i.e. formal fractions of polynomials or polynomials."
	^ self propertyAt: #representatives
]

{ #category : #'accessing-private' }
RationalMap >> representatives: anArray [ 
	self propertyAt: #representatives put: anArray asArray
]

{ #category : #accessing }
RationalMap >> size [
	"Answer the number of components of the receiver."
	^ self codomain ambient rank
]

{ #category : #private }
RationalMap >> species [
	^ RationalMap
]

{ #category : #operations }
RationalMap >> value: aPoint [
	| x value |
	(aPoint isKindOf: Ideal)
		ifTrue: [^ self asRingHomomorphism preimage: aPoint].
	x := aPoint asTuple.
	value := aPoint scalars tuple: (self representatives collect: [:each| each value: x]).
	(aPoint isKindOf: RationalPoint)
		ifTrue: [^ self codomain pointAt: value].
	^ value
]

{ #category : #arithmetic }
RationalMap >> î [ aRationalMap
	self domain >= aRationalMap codomain ifFalse: [DomainError signal: 'domains don''t match'].
	^ self species from: aRationalMap domain to: self codomain representatives: (self representatives collect: [:each| each value: aRationalMap representatives])
]
