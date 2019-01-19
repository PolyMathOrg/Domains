"
Ideals of polynomials. See PolynomialRing.
"
Class {
	#name : #PolynomialIdeal,
	#superclass : #Ideal,
	#category : #'Mathematics-Polynomials'
}

{ #category : #examples }
PolynomialIdeal class >> cyclic3 [
	"The ideal of cyclic 3-roots."
	^ (QQ polynomialsIn: #(x y z)) cyclicIdeal
]

{ #category : #examples }
PolynomialIdeal class >> katsura3 [
	"The Katsura ideal in 3 variables with rational coefficients."
	^ (QQ polynomialsIn: #(a b c)) katsuraIdeal
]

{ #category : #accessing }
PolynomialIdeal >> basis [
	"Answer a standard basis of the receiver."
	^ self propertyAt: #basis ifAbsentPut: [(Buchberger on: self) basis]
]

{ #category : #accessing }
PolynomialIdeal >> basisWithOrdering: aMonomialOrdering [
	^ (self orderedBy: aMonomialOrdering) basis
]

{ #category : #testing }
PolynomialIdeal >> contains: aPolynomial [ 
	"(Ideal Membership Problem)
	Answer true if the receiver includes aPolynomial.
	This works on any Groebner basis or standard basis (any monomial ordering)."
	^ (self reduce: aPolynomial) isZero
]

{ #category : #accessing }
PolynomialIdeal >> degree [
	"Answer the degree of the ideal, i.e. the number of monomials that are not multiple of any leading monomial in the Groebner basis."
	| G count leadingMonomials |
	leadingMonomials := Set new.
	G := self basis minimal.
	G do: [:each| leadingMonomials add: each leadingMonomial].
	count := 0.
	G do: [:each|
		each monomialsDo: [:monomial|
			(leadingMonomials noneSatisfy: [:lm| lm | monomial])
					ifTrue: [count := count + 1]]].
	^ count
]

{ #category : #operations }
PolynomialIdeal >> dehomogenizedIn: anIndeterminate [
	"Answer the dehomogenization of the receiver removing the given indeterminate."
	| R S |
	R := self scalars.
	S := R copyWithout: anIndeterminate.
	^ S * (self generators collect: [:each| S ! (each dehomogenizedIn: anIndeterminate)])
]

{ #category : #accessing }
PolynomialIdeal >> depth [
	^ self notYetImplemented
]

{ #category : #operations }
PolynomialIdeal >> dot: anIdeal [ "ï "
	"To compute the intersection we introduce a new variable t, then eliminate it from the ideal I*t + J*(1-t)."
	| R S t |
	self isZero ifTrue: [^ self].
	anIdeal isZero ifTrue: [^ anIdeal].
	R := self scalars.
	S := R scalars polynomialsIn: R rank + 1.
	t := S x: S rank.
	^ R ! (S ! self * t + (S ! anIdeal * (t - S one)) eliminate: S rank)
]

{ #category : #operations }
PolynomialIdeal >> eliminate: anIndeterminate [
	"Answer the elimination ideal computed by eliminating anIndeterminate."
	^ self eliminateAll: {anIndeterminate}

"Alternative algorithm to compute eliminants:
input: ideal I in K[x1..xn] and indet xi
output: univariate eliminant g(xi) or there's no eliminant
1. compute groebner basis G of I in any monomial ordering
2. if no initial term of any element of G is a pure power of xi, then halt, no eliminant
3. compute the sequence 1 mod G, xi mod G, xi^2 mod G, ... until a linear dependence is found
  anxi^n+...+a1xi+a0 mod G = 0
where n is minimal, then output eliminant g(xi) = sum akxi^k
"
]

{ #category : #operations }
PolynomialIdeal >> eliminateAll: aCollection [
	"Answer the elimination ideal for the indeterminates in aCollection = {xi}, i.e. the subideal of polynomials without indeterminates {xi}."
	| freeIndeterminates ordering G newGenerators |
	freeIndeterminates := self ordering indeterminates reject: [:each| aCollection includes: each].
	self ordering isGlobal ifFalse: [self notYetImplemented].
	ordering := (MonomialOrdering lex: aCollection), (MonomialOrdering grevlex: freeIndeterminates). "if the ideal is homogeneous, should we use use tlex?"
	G := (self groebnerBasisWithOrdering: ordering) minimal.
	newGenerators := G asArray select: [:each| (aCollection noneSatisfy: [:none| each has: none])].
	^ self scalars * (newGenerators collect: [:each| self scalars ! each])
]

{ #category : #operations }
PolynomialIdeal >> eliminateAllBut: anIndeterminate [
	"Answer the subideal of polynomials with only the given indeterminate."
	^ self eliminateAll: (self scalars indeterminates select: [:each| each ~= anIndeterminate])
]

{ #category : #'accessing-private' }
PolynomialIdeal >> generators: aCollection [
	| generators |
	generators := aCollection.
	(aCollection isKindOf: StandardBasis)
		ifTrue: [self propertyAt: #basis put: aCollection].
	"we normalize polynomial over Z in order to have consistent pseudo-division, but how about polynomials over other rings?"
	(aCollection isEmpty not and: [aCollection anyOne parent scalars isKindOf: RationalIntegerRing])
		ifTrue: [generators := generators collect: [:each| each * each sign]].
	super generators: generators
]

{ #category : #accessing }
PolynomialIdeal >> groebnerBasis [
	"Answer a Groebner basis of the receiver."
	self ordering isGlobal ifFalse: [^ self error: 'monomial ordering is not global'].
	^ self basis
]

{ #category : #accessing }
PolynomialIdeal >> groebnerBasisWithOrdering: aMonomialOrdering [
	^ (self orderedBy: aMonomialOrdering) groebnerBasis
]

{ #category : #operations }
PolynomialIdeal >> highestCorner [
	"Answer the highest corner of the receiver I.
	This is the unique monomial m such that:
		1) m is not in the leading ideal of I;
		2) if m' < m, then m' is in the leading ideal of I."
	self ordering isGlobal
		ifTrue: [^ self isProper ifTrue: [self scalars monomials identity]].
	"TODO: compute it combinatorially from a standard basis"
	self notYetImplemented
]

{ #category : #operations }
PolynomialIdeal >> hilbertSeries [
	"Answer the Hilbert series of the receiver."
	^ self hilbertSeriesAt: (QQ polynomialsIn: #(t)) fractions x
]

{ #category : #operations }
PolynomialIdeal >> hilbertSeriesAt: t [
	"Answer the Hilbert series of the receiver."
	self isHomogeneous ifFalse: [^ self notYetImplemented].
	^ self leadingIdeal hilbertSeriesAt: t
]

{ #category : #operations }
PolynomialIdeal >> homogenized [
	"Answer the homogenization of the receiver introducing a new indeterminate."
	| R S G ordering |
	R := self scalars.
	S := R scalars polynomialsIn: R rank + 1.
	"Must use a graded monomial ordering such as glex or grevlex:"
	ordering := MonomialOrdering grevlex: R rank.
	G := self groebnerBasisWithOrdering: ordering.
	^ S * (G collect: [:each| S ! each homogenizedIn: S rank])
]

{ #category : #'operations-elements' }
PolynomialIdeal >> inverseOf: aPolynomial [
	aPolynomial = self scalars one ifTrue: [^ aPolynomial].
	^ super inverseOf: aPolynomial
]

{ #category : #testing }
PolynomialIdeal >> isHomogeneous [
	^ self generators allSatisfy: [:each| each isHomogeneous]
]

{ #category : #testing }
PolynomialIdeal >> isPrime [
	self isZero ifTrue: [^ true].
	(self isPrincipal and: [self scalars isUFD]) ifTrue: [^ self generator isIrreducible].
	^ self notYetImplemented
]

{ #category : #testing }
PolynomialIdeal >> isPrincipal [
	"Answer true if the receiver is generated by a single polynomial."
	^ self scalars isPID or: [self generators size = 1 or: [self basis reduced size <= 1]]
]

{ #category : #testing }
PolynomialIdeal >> isTrivial [
	"Answer true if the receiver is <1>.
	Ref. Algorithmic Algebra, B. Mishra, pag. 142-145."
	(self generators anySatisfy: [:g| g isConstant]) ifTrue: [^ true].
	^ self groebnerBasis anySatisfy: [:g| g isConstant]
]

{ #category : #testing }
PolynomialIdeal >> isUnivariate [
	^ self scalars isUnivariate
]

{ #category : #testing }
PolynomialIdeal >> isZeroDimensional [
	"Answer true if the receiver is zero-dimensional. Being zero-dimensional means that the quotient ring has non-zero finite dimension as vector space over the coefficients field."
	^ self dimension = 0
]

{ #category : #testing }
PolynomialIdeal >> isZeroDimensionalRadical [
	"Answer true if the receiver is radical, assuming it is zero-dimensional.
	Becker, Weispfenning, 'Groebner Bases', Table 8.2, Algorithm ZRADICALTEST."
	self dimension = 0 ifFalse: [self error: 'not zero-dimensional'].
	self scalars indeterminates do: [:i| | f |
		f := (self eliminateAllBut: i) generator.
		(f gcd: (f derivativeIn: i)) isConstant ifFalse: [^ false]].
	^ true
]

{ #category : #operations }
PolynomialIdeal >> leadingIdeal [
	"Answer the initial ideal. This is the ideal of all leading monomials of the receiver."
	^ self scalars * self basis leadingTerms
]

{ #category : #operations }
PolynomialIdeal >> localization [
	"Answer the localization of the receiver at <x1,...,xn>. This is achieved by choosing a local ordering.
	Objects defined in this localization contain geometric information (usually only) about a Zariski neighbourhood of 0 in K^n, while objects in the global ring contain geometric information whish is valid in the whole affine space K^n."
	self scalars isGlobal ifFalse: [DomainError signal: 'the ring is not global'].
	^ self orderedBy: #lglex
]

{ #category : #accessing }
PolynomialIdeal >> maximallyIndependentIndeterminates [
	"Answer a maximimally independent set of indeterminates, or nil if the receiver is the full polynomial ring.
	The size of a maximally independent set is defined to be the dimension of the ideal, and it is the Krull dimension of the quotient ring defined by the ideal. Seeing the quotient ring as a field extension, the Krull dimension is its transcendence degree."
	"Derksen, Kemper, 'Computational Invariant Theory', 2002, Algorithm 1.2.4 (Dimension of an ideal)."
	| G leadingMonomials indeterminates |
	self isZero ifTrue: [^ #()].
	G := self ordering isGraded
		ifTrue: [self groebnerBasis] "what about local orderings?"
		ifFalse: [self groebnerBasisWithOrdering: #grevlex].
	G := G minimal. "is this necesary?"
	(G anySatisfy: [:any| any isConstant and: [any isZero not]])
		ifTrue: [^ self error: 'not a proper ideal'].

	leadingMonomials := Set new.
	G do: [:each| leadingMonomials add: each leadingMonomial].
	indeterminates := self scalars indeterminates.
	1 to: indeterminates size do: [:k|
		indeterminates combinations: k atATimeDo: [:combination|
			(leadingMonomials allSatisfy: [:monomial| combination includesAnyOf: monomial indeterminates])
				ifTrue: [^ indeterminates reject: [:any| combination includes: any]]]].
	self error: 'this shouldn''t be reached'
]

{ #category : #converting }
PolynomialIdeal >> orderedBy: aMonomialOrdering [
	^ (self scalars orderedBy: aMonomialOrdering) ! self
]

{ #category : #accessing }
PolynomialIdeal >> ordering [
	^ self scalars ordering
]

{ #category : #operations }
PolynomialIdeal >> predecomposition [
	"Becker, Weispfenning, 'Groebner Bases', Table 8.1. Algorithm PREDEC."
	| R answer |
	R := self scalars.
	answer := Set with: self.
	R indeterminates do: [:i| | previous |
		previous := answer.
		answer := Set new.
		(self eliminateAllBut: i) generator monic factorizationDo: [:p :s|
			previous do: [:G| | H | (H := G + (p raiseTo: s)) isProper ifTrue: [answer add: H]]]].
	^ answer
]

{ #category : #operations }
PolynomialIdeal >> quot: anIdeal [
	"Answer the colon quotient I:J of the receiver I with the argument J.
	This is defined as I:J := {r in R | rJ <= I}."
	"Cox IVA 205p"
	"Derksen, Kemper, 'Computational Invariant Theory', 16p."
	| R answer |
	R := self scalars.
	R isIntegralDomain ifFalse: [^ self error: 'not over an integral domain'].
	answer := R asIdeal. "<1>"
	'anIdeal generators do: [:g|
			answer := answer ï (R * ((R * g dot: self) basis apply: [:h| h /// g]))]'.
	^ answer
]

{ #category : #operations }
PolynomialIdeal >> quotientRing [
	"Answer the quotient ring of the base ring by the receiver."
	^ AffineRing mod: self
]

{ #category : #operations }
PolynomialIdeal >> radical [
	self flag: #fix. "this is not right, maybe only works for Q[x1..xn] and monomial ideals"
	^ self squareFree
]

{ #category : #testing }
PolynomialIdeal >> radicalContains: aPolynomial [
	"(Radical Membership Problem)
	Answer true if the radical of the receiver includes aPolynomial.
	Use Rabinowich's trick introducing a new indeterminate."
	| R S t X |
	R := self scalars.
	S := R scalars polynomialsIn: R rank + 1.
	t := S x: R rank + 1.
	X := OrderedCollection new.
	self generators do: [:g| X add: S ! g].
	X add: S ! aPolynomial * t - S one.
	^ (S * X) isTrivial
]

{ #category : #'operations-elements' }
PolynomialIdeal >> reduce: aPolynomial [
	"Answer the normal form of anElement with respect to the receiver."
	| f |
	f := aPolynomial.
	f parent == self scalars ifFalse: [f := self scalars ! f].
	(f isZero or: [self isZero]) ifTrue: [^ f].
	self isUnivariate ifTrue: [^ f \\ self generator].
	^ self basis reduce: f
]

{ #category : #random }
PolynomialIdeal >> remainderAtRandom: aRandom [
	self isPrincipal ifFalse: [^ self error: 'not yet implemented'].
	self scalars isUnivariate ifFalse: [^ self error: 'not yet implemented'].
	^ self scalars coefficients: ((0 to: self generator degree - 1) collect: [:i| self scalars scalars atRandom: aRandom])
]

{ #category : #operations }
PolynomialIdeal >> saturation: anIdeal [
	"Answer the saturation ideal I:J^infinity of the receiver I with the argument J."
	"Cox IVA 205p
	Derksen, Kemper, 'Computational Invariant Theory', pag. 16."
	| P t J |
	P := self scalars scalars polynomialsIn: self scalars rank + 1.
	t := P x: P rank.
	J := P ! self.
	(P ! anIdeal asIdeal) generators do: [:each|
		J := J + (P * (t * each - P one)).
		J := J eliminate: P rank].
	^ self scalars ! J
]

{ #category : #operations }
PolynomialIdeal >> singular [
	"Answer the singular locus of the receiver (or more precisely of the quotient by the receiver). The singular locus is defined as:
		Sing(A) := {P in Spec(A) | the localization of A at P is not regular}.
	If the receiver is not equidimensional, its lower-dimensional components will be contained in the answer whether they are singular or not.
	(See Eisenbud 'Commutative Algebra' Ch. 20, re Fitting ideal.)"
	| R generators n d jacobian J |
	self flag: #fix. "TODO: implement singular locus in general, from 'A Singular Introduction to Commutative Algebra', Algorithm 5.7.8"
	R := self scalars.
	generators :=  self generators asArray.
	n := R rank.
	d := self dimension.
	jacobian := R matrix: n @ generators size evaluating: [:i :j| (generators at: j) derivativeIn: i].
	J := self scalars * (jacobian minors: n - d).
	^ self + J
"before I did:
	J := R matrix: n @ generators size evaluating: [:i :j| (generators at: j) derivativeIn: i].
	^ self scalars * ((J minors: n - d) collect: [:each| self reduce: each])
but that seems to be wrong"
]

{ #category : #accessing }
PolynomialIdeal >> univariateExponent [
	"Answer the univariate exponent of the receiver.
	Becker, Weispfenning, 'Groebner Bases', Definition 8.24."
	| answer |
	answer := 1.
	self scalars indeterminates do: [:i| | f mu |
		f := (self eliminateAllBut: i) generator.
		mu := 1.
		f factorizationDo: [:p :s| mu := mu max: s].
		answer := answer + (mu - 1)].
	^ answer
]

{ #category : #accessing }
PolynomialIdeal >> variety [
	"Answer the algebraic variety that is the set of zeroes of all polynomials in the receiver."
	^ self isHomogeneous ifTrue: [(self scalars / self radical) proj] ifFalse: [(self scalars / self radical) spec]
]

{ #category : #operations }
PolynomialIdeal >> zeroDimensionalRadical [
	"Answer the radical of the receiver, assuming it is zero-dimensional.
	Becker, Weispfenning, 'Groebner Bases', Table 8.3, Algorithm ZRADICAL."
	self dimension = 0 ifFalse: [self error: 'not zero-dimensional'].
	^ self scalars * (self scalars indeterminates collect: [:i| (self eliminateAllBut: i) generator squareFree])
]
