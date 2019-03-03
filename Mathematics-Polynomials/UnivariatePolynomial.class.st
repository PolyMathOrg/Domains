"
Univariate polynomials, represented in dense form.

They are stored as a Tuple indexed by degree (the first element of the coefficients tuple corresponds to the independent coefficient of the polynomial).
"
Class {
	#name : #UnivariatePolynomial,
	#superclass : #Polynomial,
	#instVars : [
		'coefficients'
	],
	#category : #'Mathematics-Polynomials'
}

{ #category : #'instance creation' }
UnivariatePolynomial class >> coefficients: aTuple [
	^ self basicNew coefficients: aTuple 
]

{ #category : #arithmetic }
UnivariatePolynomial >> % anInteger [
	^ (self parent over: self scalars % anInteger) coefficients: self coefficients % anInteger
]

{ #category : #arithmetic }
UnivariatePolynomial >> + anObject [
	(self parent includes: anObject)
		ifTrue: [^ self parent coefficients: self coefficients + anObject coefficients].
	((self scalars includes: anObject) or: [anObject isInteger])
		ifTrue: [^ self + (self one * anObject)].
	(anObject isKindOf: RationalFunction)
		ifTrue: [^ anObject + self].
	^ DomainError signal
]

{ #category : #arithmetic }
UnivariatePolynomial >> - anObject [
	(self parent includes: anObject)
		ifTrue: [^ self parent coefficients: self coefficients - anObject coefficients].
	^ super - anObject
]

{ #category : #arithmetic }
UnivariatePolynomial >> // anObject [
	"Answer the quotient of the division of the receiver by the argument."

	(self scalars includes: anObject)
		ifTrue: [^ self parent coefficients: self coefficients // anObject].
	^ (self divisionBy: anObject) quotient
]

{ #category : #arithmetic }
UnivariatePolynomial >> /// anObject [
	"Answer the exact quotient of the division of the receiver by the argument."
	(anObject isKindOf: Monomial)
		ifTrue: [^ self dividedByMonomial: anObject].
	(self scalars includes: anObject)
		ifTrue: [^ self parent coefficients: self coefficients /// anObject].
	^ self exactlyDividedBy: anObject
]

{ #category : #operations }
UnivariatePolynomial >> << anInteger [
	^ self shift: anInteger
]

{ #category : #comparing }
UnivariatePolynomial >> = anObject [
	(anObject isKindOf: UnivariatePolynomial) ifFalse: [^ false].
	^ self coefficients = anObject coefficients
"	self degree = anObject degree ifFalse: [^ false].
	0 to: self degree do: [:i| (self coefficientAtDegree: i) = (anObject coefficientAtDegree: i) ifFalse: [^ false]].
	^ true"
]

{ #category : #operations }
UnivariatePolynomial >> >> anInteger [
	^ self << anInteger negated
]

{ #category : #arithmetic }
UnivariatePolynomial >> \\ anObject [
	"Answer the remainder of the division of the receiver by the argument."

	(self scalars includes: anObject)
		ifTrue: [^ self parent coefficients: self coefficients \\ anObject].
	^ self parent coefficients: (self coefficients polynomialDivisionBy: anObject coefficients) last
	"^ (self divisionBy: anObject) remainder"
]

{ #category : #'roots-private' }
UnivariatePolynomial >> allComplexRoots [
	| answer |
	answer := Bag new.
	self integerPrimitive factors
		withOccurrencesDo: [ :f :e | 
			f degree = 1
				ifTrue: [ answer
						add: f independentCoefficient negated / f leadingCoefficient
						withOccurrences: e ]
				ifFalse: [ (ComplexRootIsolator on: f) roots
						do: [ :each | 
							answer
								add:
									(ComplexAlgebraicNumber
										minimalPolynomial: f
										approximation: each center
										radius: each radius)
								withOccurrences: e ] ] ].
	^ answer
]

{ #category : #'roots-private' }
UnivariatePolynomial >> allRationalRoots [
	"Answer the (real) rational roots of the polynomial."

	| roots f n k tau visited fourier |
	roots := Bag new.
	f := self integerPrimitive.
	n := f degree.
	(k := f order) > 0
		ifTrue: [ roots add: 0 withOccurrences: k.
			f := f shift: k negated ].
	f isConstant
		ifTrue: [ ^ roots ].
	visited := Set new.
	fourier := OrderedCollection with: f.
	f independentCoefficient
		divisorsDo: [ :each | 
			f leadingCoefficient
				divisorsDo: [ :one | 
					tau := each / one.
					visited
						add: tau
						ifAbsent: [ (f value: tau) isZero
								ifTrue: [ roots
										add: tau
										withOccurrences: (self multiplicityAt: tau fourier: fourier).
									roots size = n
										ifTrue: [ ^ roots ] ].
							tau := tau negated.
							(f value: tau) isZero
								ifTrue: [ roots
										add: tau
										withOccurrences: (self multiplicityAt: tau fourier: fourier).
									roots size = n
										ifTrue: [ ^ roots ] ] ] ] ].
	^ roots
]

{ #category : #'roots-private' }
UnivariatePolynomial >> allRealRoots [
	| answer |
	answer := Bag new.
	self integerPrimitive factors withOccurrencesDo: [:f :e|
		f degree = 1
			ifTrue:
				[answer add: (f independentCoefficient negated / f leadingCoefficient) withOccurrences: e]
			ifFalse:
				[(RealRootIsolator on: f) roots do: [:each|
	 				answer add: (RealAlgebraicNumber minimalPolynomial: f bounds: each) withOccurrences: e]]].
	^ answer
]

{ #category : #roots }
UnivariatePolynomial >> allRoots [
	"Answer the roots (counted with multiplicity) in the coefficients ring or field."

	^ self allRootsIn: self scalars
]

{ #category : #roots }
UnivariatePolynomial >> allRootsIn: aRing [
	"Answer the roots (counted with multiplicity) in the given domain."
	| answer |
	(aRing isKindOf: RealField)
		ifTrue: [^ self allRealRoots].
	(aRing isKindOf: ComplexField)
		ifTrue: [^ self allComplexRoots].
	answer := Bag new.
	(self over: aRing) factors withOccurrencesDo: [:f :e|
		f degree = 1 ifTrue: [answer add: (f independentCoefficient negated / f leadingCoefficient) withOccurrences: e]].
	^ answer
]

{ #category : #roots }
UnivariatePolynomial >> anyRoot [
	^ self anyRootIn: self scalars
]

{ #category : #roots }
UnivariatePolynomial >> anyRootIn: aRing [
	^ (self rootsIn: aRing) anyOne
]

{ #category : #operations }
UnivariatePolynomial >> apply: aMorphism [
	"Answer a new polynomial with coefficients obtainted by applying aMorphism to the coefficients of the receiver. This morphism is a ring homomorphism from the scalars ring.
	If aMorphism is a block we assume the parent doesn't change, i.e. the block must evaluate to values within the scalars ring of the receiver."

	aMorphism isBlock
		ifTrue: [^ self parent coefficients: (self coefficients collect: aMorphism)].
	^ (self parent over: aMorphism codomain) coefficients: (self coefficients apply: aMorphism)
]

{ #category : #'accessing coefficients' }
UnivariatePolynomial >> at: aMonomial [
	^ self atDegree: aMonomial degree
]

{ #category : #'accessing coefficients' }
UnivariatePolynomial >> atDegree: i [
	^ coefficients at: i + 1 ifAbsent: [ self scalars zero ]
]

{ #category : #accessing }
UnivariatePolynomial >> bitSize [
	^ self coefficients bitSize
]

{ #category : #roots }
UnivariatePolynomial >> cauchyRootBound [
	| max a0 an |
	max := 0.
	self coefficients do: [:each| max := max max: each abs].
	a0 := self independentCoefficient abs.
	an := self leadingCoefficient abs.
	^ Array with: a0 / (a0 + max) with: an + max / an
]

{ #category : #deprecated }
UnivariatePolynomial >> coefficientAt: aMonomial [
	^ self coefficientAtDegree: aMonomial degree
]

{ #category : #deprecated }
UnivariatePolynomial >> coefficientAt: aMonomial put: value [
	coefficients at: aMonomial degree + 1 put: value.
	(value isZero and: [aMonomial degree + 1 = coefficients size])
		ifTrue: [self normalize].
	^ value
]

{ #category : #deprecated }
UnivariatePolynomial >> coefficientAtDegree: i [
	^ coefficients at: i+1 ifAbsent: [self scalars zero]
]

{ #category : #accessing }
UnivariatePolynomial >> coefficients [
	^ coefficients
]

{ #category : #'accessing-private' }
UnivariatePolynomial >> coefficients: aTuple [
	coefficients := aTuple.
	self normalize
]

{ #category : #enumerating }
UnivariatePolynomial >> coefficientsDo: aBlock [
	self coefficients do: aBlock
]

{ #category : #operations }
UnivariatePolynomial >> companion [
	"Answer the Frobenius companion matrix of the receiver.
	The companion matrix of a polynomial f in R[x] is the matrix of the 'multiplication by x' map on the R-algebra R[x]/<f>. This is a matrix that has f as both the characteristic and minimal polynomial.
	Also, given a linear recursive sequence with characteristic polynomial f, the transpose companion matrix of f generates the sequence."
	| n one zero |
	self isMonic ifFalse: [^ DomainError signal: 'Undefined for non-monic polynomials'].
	n := self degree.
	zero := self scalars zero.
	one := self scalars one.
	^ self scalars matrix: n@n evaluating: [:i :j| i-1 = j ifTrue: [one] ifFalse: [j < n ifTrue: [zero] ifFalse: [(self coefficientAtDegree: i-1) negated]]]
]

{ #category : #copying }
UnivariatePolynomial >> copy [
	^ self parent coefficients: self coefficients copy
]

{ #category : #'accessing coefficients' }
UnivariatePolynomial >> degree [
	coefficients isEmpty ifTrue: [^ Infinity negative].
	^ coefficients size - 1
]

{ #category : #operations }
UnivariatePolynomial >> derivative [
	| newCoefficients |
	self isZero ifTrue: [^ self].
	newCoefficients := Array new: self degree.
	1 to: self degree do: [ :i | newCoefficients at: i put: (self coefficientAtDegree: i) * i ].
	^ self parent coefficients: newCoefficients
]

{ #category : #operations }
UnivariatePolynomial >> derivativeIn: anIndeterminate [
	^ (self has: anIndeterminate) ifTrue: [self derivative] ifFalse: [self zero]
]

{ #category : #operations }
UnivariatePolynomial >> discriminant [
	"Answer the (standard) discriminant of the receiver."

	| n |
	n := self degree.
	^( (-1)  raisedTo:  (n*(n-1)/2)) / self leadingCoefficient * (self resultant: self derivative)
]

{ #category : #operations }
UnivariatePolynomial >> discriminant0 [
	"Answer the (normalized) discriminant of the receiver."

	| n |
	n := self degree.
	^ ((-1)  raisedTo: (n*(n-1)/2)) / ((self leadingCoefficient)  raisedTo: (2*n-1)) * (self resultant: self derivative)
]

{ #category : #factorization }
UnivariatePolynomial >> distinctDegreeFactorization [
	"Answer the distinct-degree factorization of a monic square-free polynomial over a finite field.
	The factorizations is a Dictionary d -> g, where g is the product of all irreducible factors of degree d."
	| answer i f f2 one q x R h |
	answer := Dictionary new.
	f := self.
	R := f parent.
	x := R x.
	one := R one.
	q := R scalars size.
	i := 1.
	f2 := f.
	h := x.
	[f2 degree >= (2*i)]
		whileTrue:
			[ | g | g := f2 gcd: (h := h raisedTo: q modulo: f2) - x.
			g ~= one ifTrue: [answer at: i put: g. f2 := f2 // g].
			i := i + 1].
	f2 ~= one ifTrue: [answer at: f2 degree put: f2].
	answer isEmpty ifTrue: [answer at: 1 put: f].
	^ answer
]

{ #category : #arithmetic }
UnivariatePolynomial >> dividedByMonomial: aMonomial [
	^ self shift: aMonomial degree negated
]

{ #category : #arithmetic }
UnivariatePolynomial >> dividedByScalar: aNumber [
	^ self parent coefficients: self coefficients / aNumber
]

{ #category : #'factorization-private' }
UnivariatePolynomial >> equalDegreeFactorization2: d [
	"Cantor-Zassenhaus algorithm. Answer the equal-degree factorization of a monic squarefree univariate polynomial which has r>=2 pairwise distinct irreducible factors each of degree d."
	| f r h g one factors c |
	f := self.
"	q := f parent scalars size.
	q even ifFalse: [^ self error: 'order not even']."
	r := f degree / d.
	one := f parent one.
	factors := OrderedCollection with: f.
	h := f parent x.
	[factors size < r]
		whileTrue:
			[g := h.
			d - 1 timesRepeat: [g := h + g squared \\ f].
			factors do: [:u|
				u degree > d
					ifTrue:
						[c := g gcd: u.
						(c ~= one and: [c ~= u])
							ifTrue:
								[factors := factors copyWithout: u.
								factors add: c; add: u // c]]].
			h := h << 2].
	^ factors
]

{ #category : #factorization }
UnivariatePolynomial >> equalDegreeFactorization: d [
	"Cantor-Zassenhaus algorithm. Answer the equal-degree factorization of a monic squarefree univariate polynomial which has r>=2 pairwise distinct irreducible factors each of degree d."

	| f r q h g one factors c |
	f := self.
	q := f scalars size.
	q odd
		ifFalse: [ ^ self equalDegreeFactorization2: d ].
	r := f degree / d.
	one := f parent one.
	factors := OrderedCollection with: f.
	[ factors size < r ]
		whileTrue:
			[ h := (f parent atRandomMaxDegree: 2 * d - 1) monic.	"should be monic? should: d <= deg(h) <= 2d-1"
			h := h monic.
			g := (h raisedTo: ((q raisedTo: d) - 1) / 2 modulo: f) - one.	"<- most time is spent here"
			factors
				do: [ :u | 
					u degree > d
						ifTrue: [ c := g gcd: u.
							(c ~= one and: [ c ~= u ])
								ifTrue: [ "found non-trivial common factor c"
									factors := factors copyWithout: u.
									factors
										add: c;
										add: u // c ] ] ] ].
	^ factors
]

{ #category : #operations }
UnivariatePolynomial >> even [
	"Decompose the receiver in the form f(x^2)x + g(x^2) and answer g(x)."
	^ self parent coefficients: ((1 to: self coefficients size by: 2) collect: [:each| coefficients at: each])
]

{ #category : #arithmetic }
UnivariatePolynomial >> exactlyDividedBy2: aPolynomial [
	"Answer the exact division of the receiver by the argument.
	Apply the Schonhage-Jabelean algorithm, for polynomials of degree at most 2n and n with coefficients in a field. When necesary conditions don't hold, do the ordinary division.
	Ref: 'Algorithms With Exact Divisions Made Faster', Arnold Schonhage,
	INRIA Research Report Nro. 2381, Algorithms Seminar 1993-1994, p. 51."

	| shift f g m n h l k cg q |
	self flag: #fix. "this has some bug"
	self isZero
		ifTrue: [^ self].
	aPolynomial isConstant
		ifTrue: [^ self / aPolynomial leadingCoefficient].
	(self isUnivariate and: [aPolynomial isUnivariate])
		ifFalse: [^ (MultivariatePolynomialDivision divide: self by: {aPolynomial}) exactQuotient].
	self scalars isField
		ifFalse: [^ (PolynomialPseudoDivision divide: self by: aPolynomial) exactQuotient].
	(shift := aPolynomial order negated) < 0 ifTrue: [^ (self shift: shift) exactlyDividedBy: (aPolynomial shift: shift)].
	f := self coefficients.
	g := aPolynomial coefficients.
	m := f size.
	n := g size.
	m = n ifTrue: [^ self parent constant: f last / g last].
 	n * 2 > m ifFalse: [^ (self divisionBy: aPolynomial) exactQuotient].

	h := f size // 2.
	l := h // 2.
	k := h - l.

	q := Array new: m-n+1.
	
	"Jebelean division for the lowest half:"
	cg := g first reciprocal. "reciprocal of the independent coefficient"
	0 to: l do: [:i|
		| qi |
		qi := q at: i+1 put: (f at: i+1) * cg.
		1 to: l-i do: [:j|
			f at: i+j+1 put: (f at: i+j+1) - (qi*(g at: j+1))]]. "optimize negated"
	
	"Schonhage division for the other half:"
	cg := g last reciprocal. "reciprocal of the leading coefficient"
	m-n to: m-n-k+1 by: -1 do: [:i|
		| qi |
		qi := q at: i+1 put: (f at: i+n) * cg.
		n-2 to: m-k-i by: -1 do: [:j|
			f at: i+j+1 put: (f at: i+j+1) - (qi*(g at: j+1))]].

	^ self parent coefficients: q
]

{ #category : #arithmetic }
UnivariatePolynomial >> exactlyDividedBy: aPolynomial [
	"Answer the exact division of the receiver by the argument."

	self isZero ifTrue: [^ self].
	aPolynomial isConstant ifTrue: [^ self dividedByScalar: aPolynomial leadingCoefficient].
	(aPolynomial isMonic or: [self scalars isField])
		ifFalse: [^ (PolynomialPseudoDivision divide: self by: aPolynomial) exactQuotient].
	^ (PolynomialDivision divide: self by: aPolynomial) exactQuotient
]

{ #category : #'factorization-private' }
UnivariatePolynomial >> factorizationFiniteField [
	| answer |
	answer := Bag new.
	self squareFreeFactorizationFiniteField withOccurrencesDo: [:f :r|
		f distinctDegreeFactorization keysAndValuesDo: [:d :g|
			(g equalDegreeFactorization: d) do: [:each| answer add: each withOccurrences: r]]].
	^ answer
]

{ #category : #'factorization-private' }
UnivariatePolynomial >> factorizationIntegers [
	| answer content |
	answer := Bag new.
	(content := self content) factorizationDo: [:p :e| answer add: (self parent constant: p) withOccurrences: e].
	(self / (content * self sign)) squareFreeFactorization withOccurrencesDo: [:f :r|
		f factorizationZassenhauss do: [:each| answer add: each withOccurrences: r]].
	^ answer
]

{ #category : #'factorization-private' }
UnivariatePolynomial >> factorizationIntegers2 [
	| answer f g |
	answer := Bag new.
	self content factorizationDo: [:p :e| answer add: (self parent constant: p) withOccurrences: e].
	g := self gcd: self derivative.
	f := self /// g.
	"TODO: if the receiver is not square-free, we're missing powers of factors"
	(f / (f content * f sign)) factorizationZassenhauss
		withOccurrencesDo: [:each :k|
			answer add: each withOccurrences: k].
	^ answer
]

{ #category : #'factorization-private' }
UnivariatePolynomial >> factorizationZassenhauss [
	"Zassenhauss algorithm. Answer the irreducible factors of a square-free primitive polynomial with integer coefficients."

	| f n A b B C gamma df p fp dfp k factors r answer |
	f := self.
	n := f degree.
	n = 1
		ifTrue: [ ^ {f} ].
	A := f normMax.
	b := f leadingCoefficient.
	B := (n + 1) sqrt * (1 << n) * A * b.	"float will fail"
	C := ((n+1) raisedTo:(2*n))*(A raisedTo:(2*n-1)).
	"	gamma := (2 * (C log: 2)) ceiling."
	gamma := 2 * C highBit.	"+1?"
	df := f derivative.
	[ [ p := (2 * gamma * gamma ln) asInteger atRandom nextPrime.
	p | b ] whileTrue.
	fp := f % p.
	dfp := df % p.
	(fp gcd: dfp) isConstant ] whileFalse.
	"modular factorization"
	factors := fp monic factors.
	r := factors size.	"should repeat this 5 times and choose smallest r"
	r = 1
		ifTrue: [ ^ {f} ].	"if irreducible mod p, also irreducible over Z"
	self assert: (self % p - (factors product * b)) isZero.
	
	"hensel lifting"
	k := (2 * B + 1 log: p) abs ceiling.	"p^k > 2B"
	factors := f henselLift: factors asArray to: k.	"lift to p^k"	"<- about 20% of time is spent here"
	1 to: k do: [ :i | 
		self
			assert:
				((self - ((factors product: [ :fi | fi lift ]) * b)) % (p raisedTo: i))
					isZero ].
	"recombination"
	answer := Bag new.
	1 to: r do: [ :j | 
		(factors combinations: j)
			do: [ :each | 
				| g division |
				"<- about 50% of time is spent in this recombination step"
				g := (each product * b) lift primitive.
				division := f divisionBy: g.
				division remainder isZero
					ifTrue: [ answer add: g.
						f := division quotient.
						f isConstant
							ifTrue: [ ^ answer ] ] ] ].
	^ answer
		add: f;
		yourself
]

{ #category : #'factorization-private' }
UnivariatePolynomial >> factorizationZassenhauss2 [
	"ZassenHauss algorithm. Answer the irreducible factors of a square-free polynomial with integer coefficients."
	| answer f df p fp dfp factors r B e g |
	answer := Bag new.
	f := self integerPrimitive.
	"remove x factor"
"	f leadingCoefficient abs > f independentCoefficient abs ifTrue: [f := f reversed]."
	df := f derivative.
	B := f landauMignotteBound.
	"1. Choose a prime p such that gcd(f,df) = 1 mod p:"
	[p := 1000 atRandom nextPrime.
	fp := f % p.
	dfp := df % p.
	(fp gcd: dfp) = fp one] whileFalse.
	"2. Modular factorization: factor f mod p."
	factors := fp factors.
	r := factors size. "should repeat this 5 times and choose smallest r"
	r = 1 ifTrue: [^ {f}]. "if irreducible mod p, also irreducible over Z"
	"3. Compute Landau-Mignotte bound and p^a with enough precision for Hensel lifting:"
	e := (B*2*f leadingCoefficient log: p) ceiling.
	"4. Hensel lift to precision p^a:"
		"..."
	"5. Recombination: try all combinations of factors and find divisors of f:"
	1 to: r do: [:k|
		(factors combinations: k) do: [:each|
			g := each product.
			g | f ifTrue: [answer add: g]]].
	^ answer
]

{ #category : #factorization }
UnivariatePolynomial >> factors [
	self scalars isGaloisField
		ifTrue: [^ self factorizationFiniteField].
	(self scalars isKindOf: RationalIntegerRing)
		ifTrue: [^ self factorizationIntegers].
	(self scalars isKindOf: RationalField)
		ifTrue: [^ (self integerPrimitive over: ZZ) factorizationIntegers apply: [:each| self parent ! each]].
	^ self notYetImplemented
]

{ #category : #testing }
UnivariatePolynomial >> has: anIndeterminate [
	^ self degree > 0 and: [self parent has: anIndeterminate]
]

{ #category : #comparing }
UnivariatePolynomial >> hash [
	| answer |
	self isZero ifTrue: [^ 0].
	answer := self degree.
	0 to: self degree do: [:i| answer := answer + (self coefficientAtDegree: i) hash].
	^ answer
]

{ #category : #'factorization-private' }
UnivariatePolynomial >> henselLift: factors to: k [
	| p r mid g h s t m bezout gFactors hFactors |
	p := factors anyOne scalars characteristic.
	r := factors size.
	r = 1 ifTrue: "can be optimized, compute inverse modulo p using extended euclid, then lift to p^k with newton iteration algorithm 9.10 (modern computer algebra)"
		[^ {(self % (p raisedTo: k) / self leadingCoefficient)}].
	mid := r//2.
	gFactors := factors copyFrom: 1 to: mid.
	hFactors := factors copyFrom: mid+1 to: r.
	g := gFactors product * self leadingCoefficient.
	h := hFactors product.
	bezout := (ExtendedEuclid on: {g. h}) bezout.
	s := bezout first.
	t := bezout second.
	m := p.
	k highBit timesRepeat: "Hensel step:"
		[| e division c d b |
		self assert: (self % m - (g*h)) isZero.
		self assert: (s*g + (t*h) - 1) isZero.
		m := m squared.
		g := g lift % m. h := h lift % m. s := s lift % m. t := t lift % m.
		e := self % m - (g*h).
		division := s*e divisionBy: h.
		c := division quotient.
		d := division remainder.
		g := g + (t*e) + (c*g).
		h := h + d.
		b := s*g + (t*h) - 1.
		division := s*b divisionBy: h.
		c := division quotient.
		d := division remainder.
		s := s - d.
		t := t - (t*b) - (c*g).
		self assert: (self % m - (g*h)) isZero.
		self assert: (s*g + (t*h) - 1) isZero].
	^ (g lift henselLift: gFactors to: k), (h lift henselLift: hFactors to: k)
]

{ #category : #'accessing coefficients' }
UnivariatePolynomial >> independentCoefficient [
	^ self coefficientAtDegree: 0
]

{ #category : #testing }
UnivariatePolynomial >> isIrreducible [
	| R |
	self isConstant ifTrue: [^ false]. "constant polynomials are not reducible nor irreducible"
	self degree = 1 ifTrue: [^ true].
	R := self scalars.
	((R isKindOf: RealField) and: [self degree > 2])
		ifTrue: [^ false].
	(R isKindOf: ComplexField)
		ifTrue: [^ self degree = 1].
	R isGaloisField
		ifTrue: [^ self isIrreducibleRabin].
"	(R isKindOf: RationalField)
		ifTrue: [^ self isIrreducibleHeuristic: ...]."
	^ self factors size = 1
]

{ #category : #testing }
UnivariatePolynomial >> isIrreducibleBenOr [
	"Ben-Or Irreducibility Test algorithm for polynomials in field of characteristic q."
	| q x one |
	q := self scalars characteristic.
	x := self parent x.
	one := self one.
	1 to: self degree // 2 do: [:i|
			(self gcd: (x raisedTo: (q raisedTo: i)) - x \\ self) = one ifTrue: [^ false]].
	^ true
]

{ #category : #testing }
UnivariatePolynomial >> isIrreducibleHeuristic2: anInteger [
	"Answer an Integer or nil. If the answer is an Integer, the
	receiver is irreducible iff that integer is prime, and in fact the
	integer will be prime with a very high probability (a probabilistic
	test is used here). If the answer is nil, the heuristic test has failed,
	and nothing can be said about the irreducibility of the receiver."

	"This is a probabilistic test for irreudcibility of rational univariate
	polynomials. It works looking for a prime evaluation of the polynomial.
	If it finds such a prime, then it's returned, and nil otherwise. The
	argument anInteger is the upper bound for the looking for primes."

	"Reference: 'A Heuristic Polynomial Irreducibility Test', Michael
	Monagan, J. Symbolic Comp., (1992) Vol. 13, No. 1, pp 47-57."

	| f g bg bound val try gcd |
	f := self integerPrimitive.
	g := f reversed.
	(bg := g norm1 / g leadingCoefficient abs + 1) <
	(bound := f norm1 / f leadingCoefficient abs + 1)
		ifTrue: [f := g. bound := bg].
	bound to: anInteger - 1 / 2 do: [ :each |
		val := (f value: each) abs.
		gcd := val gcd: 355929487585205167172661547995662840887819680000.
		(gcd <= (each - bound) squared and: [(try := val / gcd) isPrime])
			ifTrue: [^ try].
		val := (f value: each negated) abs.
		gcd := val gcd: 355929487585205167172661547995662840887819680000.
		(gcd <= (each - bound) squared and: [(try := val / gcd) isPrime])
			ifTrue: [^ try]
	].
	^ nil
]

{ #category : #testing }
UnivariatePolynomial >> isIrreducibleHeuristic: anInteger [
	"Answer an Integer or nil. If the answer is an Integer, the
	receiver is irreducible iff that integer is prime, and in fact the
	integer will be prime with a very high probability (a probabilistic
	test is used here). If the answer is nil, the heuristic test has failed,
	and nothing can be said about the irreducibility of the receiver."

	"This is a probabilistic test for irreudcibility of rational univariate
	polynomials. It works looking for a prime evaluation of the polynomial.
	If it finds such a prime, then it's returned, and nil otherwise. The
	argument anInteger is the upper bound for the looking for primes."

	| f val bound interval |
	f := self integerPrimitive.
	bound := self cauchyRootBound first floor abs.
	bound even ifTrue: [bound := 0 max: bound - 1].
	interval := f independentCoefficient odd
		ifTrue: [bound to: bound + (anInteger // 2)]
		ifFalse: [bound to: bound + anInteger by: 2].
	interval do: [ :each |
		val := (f value: each) abs.
		val isPrime ifTrue: [^ val].
		val := (f value: each negated) abs.
		val isPrime ifTrue: [^ val]
	].
	^ nil
]

{ #category : #testing }
UnivariatePolynomial >> isIrreducibleRabin [
	| Fx x one f n h g q |
	(self independentCoefficient isZero and: [ self degree > 1 ])
		ifTrue: [ ^ false ].
	"Rabin's algorithm:"
	f := self.
	Fx := f parent.
	q := Fx scalars size.
	x := Fx x.
	one := Fx one.
	n := f degree.
	n factors asSet
		do: [ :p | 
			h := (x raisedTo: (q raisedTo: n / p) modulo: f - x) \\ f.
			g := f gcd: h.
			g ~= one
				ifTrue: [ ^ false ] ].
	g := (x raisedTo: (q raisedTo: n) modulo: f) - x \\ f.
	g isZero
		ifFalse: [ ^ false ].
	^ true
]

{ #category : #testing }
UnivariatePolynomial >> isUnivariate [
	^ true
]

{ #category : #testing }
UnivariatePolynomial >> isZero [
	^ coefficients isZero
]

{ #category : #'factorization-private' }
UnivariatePolynomial >> landauMignotteBound [
	"Answer the Landau-Mignotte bounds for the receiver.
	This is an upper bound for the absolute value of the coefficients of any nontrivial factor of a polynomial with integer coefficients. The bound depends on both the degree and the size of the coefficients of the receiver."
	| d h |
	d := self degree // 2.
	h := d // 2.
	^ (d - 1 choose: h) * self norm2 + (d - 1 choose: h - 1)
]

{ #category : #'accessing coefficients' }
UnivariatePolynomial >> leadingCoefficient [
	^ self coefficientAtDegree: self degree
]

{ #category : #'accessing monomials' }
UnivariatePolynomial >> leadingMonomial [
	| answer |
	self monomialsDo: [:each| (answer isNil or: [each > answer]) ifTrue: [answer := each]].
	^ answer

"this could be faster, but it fails with local orderings for example:
	^ self isZero ifFalse: [self parent monomials x: self parent indeterminate to: self degree]
"
]

{ #category : #accessing }
UnivariatePolynomial >> lift [
	"If the coefficients ring is a quotient R/I, nswer a representative of the receiver over R. See >>%."
	^ (parent over: parent scalars base) coefficients: coefficients lift
]

{ #category : #enumerating }
UnivariatePolynomial >> monomialsApply: aBlock [
	| x monomials n newCoefficients |
	x := self parent indeterminate.
	monomials := (1 to: coefficients size)
		collect: [ :i | 
			(aBlock value: (self parent monomials x: x to: i - 1))
				-> (coefficients at: i) ].
	n := monomials max: [ :each | each key degree ].
	newCoefficients := (Array new: n+1) atAllPut: self scalars zero.
		monomials
		do: [ :each | newCoefficients at: each key degree + 1 add: each value ].
	^ self parent coefficients: newCoefficients
]

{ #category : #enumerating }
UnivariatePolynomial >> monomialsDo: aBlock [
	"Iterate over the support of the receiver, i.e. the monomials with non-zero coefficient."
	| x |
	x := self parent indeterminate.
	1 to: coefficients size do: [:i|
		(coefficients at: i) isZero
			ifFalse: [aBlock value: (self parent monomials x: x to: i-1)]]
]

{ #category : #roots }
UnivariatePolynomial >> multiplicityAt: aPoint [
	"Answer the multiplicity of aPoint as zero of the receiver."
	| answer f |
	self isZero ifTrue: [^ Infinity positive].
	answer := 0.
	f := self.
	[(f value: aPoint) isZero]
		whileTrue:
			[answer := answer + 1.
			f := f derivative].
	^ answer
]

{ #category : #'roots-private' }
UnivariatePolynomial >> multiplicityAt: aRoot fourier: fourier [
	| count |
	count := 0.
	fourier do: [:each| (each value: aRoot) isZero ifFalse: [^ count]. count := count + 1].
	[fourier last isConstant]
		whileFalse:
			[((fourier add: fourier last derivative) value: aRoot) isZero ifFalse: [^ count]. count := count + 1].
	^ count
]

{ #category : #arithmetic }
UnivariatePolynomial >> multipliedByMonomial: aMonomial [
	^ self shift: aMonomial degree
]

{ #category : #arithmetic }
UnivariatePolynomial >> multipliedByPolynomial: aPolynomial [
	^ self parent coefficients: (self coefficients convolution: aPolynomial coefficients)
]

{ #category : #arithmetic }
UnivariatePolynomial >> multipliedByScalar: aNumber [
	^ self parent coefficients: self coefficients * aNumber
]

{ #category : #arithmetic }
UnivariatePolynomial >> negated [
	"Answer the additive inverse of the receiver."
	^ self parent coefficients: self coefficients negated
]

{ #category : #'accessing-private' }
UnivariatePolynomial >> normalize [
	| n |
	(n := coefficients lastNonZero) < coefficients size
		ifTrue: [coefficients := coefficients copyFrom: 1 to: n]
]

{ #category : #operations }
UnivariatePolynomial >> odd [
	"Decompose the receiver in the form f(x^2)x + g(x^2) and answer f(x)."
	^ self parent coefficients: ((2 to: self coefficients size by: 2) collect: [:each| coefficients at: each])
]

{ #category : #roots }
UnivariatePolynomial >> orderAt: aPoint [
	^ self multiplicityAt: aPoint
]

{ #category : #converting }
UnivariatePolynomial >> over: aRing [
	^ (self parent over: aRing) coefficients: (self coefficients over: aRing)
]

{ #category : #enumerating }
UnivariatePolynomial >> partsDo: aBlock [
	| x |
	x := self parent indeterminate.
	coefficients withIndexDo: [:value :index| value isZero ifFalse: [aBlock value: (self parent monomials x: x to: index-1) -> value]]
]

{ #category : #operations }
UnivariatePolynomial >> psc2: anInteger with: aPolynomial [
	"Answer the anInteger-th principal subresultant coefficient of the receiver with aPolynomial."

	| f g n m t rows tuple |
	f := self.
	g := aPolynomial.
	m := f degree.
	n := g degree.
	t := m + n - anInteger - anInteger.
	t <= 0 ifTrue: [^ self scalars one].
	rows := OrderedCollection new: t.
	tuple := self scalars tuple: t evaluating: [:i| f coefficientAtDegree: m - i + 1].
	n - anInteger timesRepeat: [rows add: tuple. tuple := tuple shift: 1].
	tuple := self scalars tuple: t evaluating: [:i| g coefficientAtDegree: n - i + 1].
	m - anInteger timesRepeat: [rows add: tuple. tuple := tuple shift: 1].
	^ (Matrix rows: rows) determinant
]

{ #category : #operations }
UnivariatePolynomial >> psc3: i with: aPolynomial [
	"Answer the anInteger-th principal subresultant coefficient of the receiver with aPolynomial."
	self flag: #fix. "use version 2, more efficient, but must test"
	^ (self subresultant: i with: aPolynomial) leadingCoefficient "WTF, sometimes subresultant returns nil, SemialgebraicSet circle"
]

{ #category : #operations }
UnivariatePolynomial >> psc: anInteger with: aPolynomial [
	"Answer the anInteger-th principal subresultant coefficient of the receiver with aPolynomial."

	| f g n m t rows tuple |
	f := self.
	g := aPolynomial.
	m := f degree.
	n := g degree.
	t := m + n - anInteger - anInteger.
	t <= 0 ifTrue: [^ self scalars one].
	rows := OrderedCollection new: t.
	tuple := self scalars tuple: t evaluating: [:i| f coefficientAtDegree: m - i + 1].
	n - anInteger timesRepeat: [rows add: tuple. tuple := tuple shift: 1].
	tuple := self scalars tuple: t evaluating: [:i| g coefficientAtDegree: n - i + 1].
	m - anInteger timesRepeat: [rows add: tuple. tuple := tuple shift: 1].
	^ (Matrix rows: rows) determinant
]

{ #category : #accessing }
UnivariatePolynomial >> representative [
	"If the coefficients ring is a quotient R/I, nswer a representative of the receiver over R. See >>%."
	^ (parent over: parent scalars base) coefficients: coefficients representative
]

{ #category : #operations }
UnivariatePolynomial >> resultant2: aPolynomial [
	"Answer the resultant of the receiver with the argument."
	| f g mult |
	self degree <= aPolynomial degree
		ifTrue: [f := self. g := aPolynomial]
		ifFalse: [f := aPolynomial. g := self].
	f isConstant ifTrue: [^ (f raiseTo: (g degree))].
	f isMonic
		ifTrue:
			[mult := f leadingCoefficient]
		ifFalse:
			[mult := 'f leadingCoefficient ^ g degree'.
			f := f / f leadingCoefficient].
	^ (g value: f companion) determinant * mult
]

{ #category : #operations }
UnivariatePolynomial >> resultant3: aPolynomial [
	"Answer the resultant of the receiver with the argument."

	| f g answer negate |
	self degree > aPolynomial degree
		ifTrue: [f := aPolynomial. g := self. negate := true]
		ifFalse: [f := self. g := aPolynomial. negate := false].
	'answer := f isConstant
			ifTrue: [f ^ g degree]
			ifFalse:
				[(f resultant3: g \\ f) * (f leadingCoefficient ^ (g degree - f degree + 1))]'.
	^ negate ifTrue: [answer negated] ifFalse: [answer]
]

{ #category : #operations }
UnivariatePolynomial >> resultant: aPolynomial [
	"Answer the resultant of the receiver with aPolynomial."
	self degree = 0
		ifTrue: [^ aPolynomial raiseTo:( self degree)].
	'aPolynomial degree = 0
			ifTrue:
				[^ (self degree even or: [aPolynomial degree even])
						ifTrue: [(self ^ aPolynomial degree)]
						ifFalse: [(self ^ aPolynomial degree) negated]]'.
	^ (self sylvester: aPolynomial) determinant
]

{ #category : #operations }
UnivariatePolynomial >> reversed [
	"Answer the reverse of the receiver."

	^ self parent coefficients: coefficients reversed
]

{ #category : #roots }
UnivariatePolynomial >> roots [
	"Answer the set of distinct roots in the coefficients ring or field."
	^ self rootsIn: self scalars
]

{ #category : #roots }
UnivariatePolynomial >> rootsIn: aRing [
	"Answer the distinct roots (not counted with multiplicity) in the given domain."
	^ (self allRootsIn: aRing) asSet
]

{ #category : #operations }
UnivariatePolynomial >> shift: anInteger [
	| n |
	self isZero ifTrue: [^ self].
	n := self degree + anInteger.
	n >= 0 ifFalse: [^ self zero].
	^ self parent coefficients: coefficients >>> anInteger
]

{ #category : #roots }
UnivariatePolynomial >> signature [
	"Answer the signature (r1,r2) of the receiver, where r1 is the number of real roots and 2*r2 is the number of non-real roots. Assume the receiver's coefficients are integers. Throw an error if the receiver is not square-free.
	Ref: COHEN Algorithm 4.1.11 (Sturm)."

	| A B g h s n t r1 d R |
	self isZero
		ifTrue: [ ^ #(0 0) ].
	A := self primitive.
	B := self derivative primitive.
	g := 1.
	h := 1.
	s := A sign.
	n := A degree.
	t := n even
		ifTrue: [ s negated ]
		ifFalse: [ s ].
	r1 := 1.
	[ d := A degree - B degree.
	R := A pseudoRem: B.
	R isZero
		ifTrue: [ ^ self error: 'polynomial is not square-free' ].
	(d odd or: [ B leadingCoefficient > 0 ])
		ifTrue: [ R := R negated ].
	"Use Sturm:"
	R sign ~= s
		ifTrue: [ s := s negated.
			r1 := r1 - 1 ].
	R sign ~= ((-1 raisedTo: R) degree * t)
		ifTrue: [ t := t negated.
			r1 := r1 + 1 ].
	"Finished?"
	R isConstant ]
		whileFalse: [ A := B.
			B := R / ((h raisedTo: d) * g).
			g := A leadingCoefficient abs.
			h := (h raisedTo: 1 - d) * (g raisedTo: d) ].
	^ {r1.
	((n - r1) / 2)}
]

{ #category : #factorization }
UnivariatePolynomial >> squareFreeFactorization [
	"Answer a square-free factorization of the receiver."
	self scalars isGaloisField
		ifTrue: [^ self squareFreeFactorizationFiniteField].
	self scalars characteristic > 0 "finite ring"
		ifTrue: [^ self notYetImplemented].
	self scalars isField
		ifTrue: [^ self squareFreeFactorizationYun].
	self scalars isUFD
		ifFalse: [^ self notYetImplemented].
	^ (self primitive over: self scalars fractions) squareFreeFactorizationYun apply: [:each| self parent ! each primitive]
]

{ #category : #'factorization-private' }
UnivariatePolynomial >> squareFreeFactorizationFiniteField [
	"Answer the square-free decomposition of a monic polynomial."
	"NOTE: this only works on prime fields. For non-prime fields, after substituting x^p by x we must also apply the inverse of the Frobenius automorphism to the coefficients."
	| answer f one p i g c w y z |
	answer := Bag new.
	f := self.
	one := f one.
	p := f scalars characteristic.
	(g := f derivative) isZero
		ifTrue:
			[f := f monomialsApply: [:m| m root: p]. "not enough if the field is non-prime"
			f squareFreeFactorizationFiniteField
				do: [:each| answer add: each withOccurrences: p].
			^ answer].
	c := f gcd: g.
	w := f // c.
	i := 1.
	[w = one]
		whileFalse:
			[y := w gcd: c. z := w // y.
			(z raisedTo: i) = one ifFalse: [answer add: z withOccurrences: i].
			i := i + 1.
			w := y. c := c // y].
	c = one
		ifFalse:
			[c := c monomialsApply: [:m| m root: p]. "not enough if the field is non-prime"
			c squareFreeFactorizationFiniteField
				do: [:each| answer add: each withOccurrences: p]].
	^ answer
]

{ #category : #'factorization-private' }
UnivariatePolynomial >> squareFreeFactorizationYun [
	"Answer a square-free decomposition of the receiver.
	Use Yun's algorithm. Assume the coefficients are in a unique
	factorization domain or in a field of characteristic 0.
	Yun's algorithm on an input polynomial of degree n uses O(M(n)log(n)) operations in the base field F, where M(n) is the number of operations in F required to multiply two polynomias of degree n in F[x]."

	| p q gcd count answer |
	answer := Bag new.
	count := 1.
"	lc := self leadingCoefficient.
	lc = self scalars one
		ifFalse: [answer add: (self parent constant: lc)].
	p := self / lc."
	p := self monic.
	q := p derivative.
	gcd := p gcd: q.
	gcd degree > 0
		ifTrue:
			[p := p // gcd.
			q := q // gcd - p derivative.
			[q isZero]
				whileFalse:
					[gcd := p gcd: q.
					gcd degree > 0 ifTrue: [answer add: gcd withOccurrences: count].
					count := count + 1.
					p := p // gcd.
					q := q // gcd - p derivative]].
	^ answer add: p withOccurrences: count; yourself
]

{ #category : #operations }
UnivariatePolynomial >> subresultant: i with: aPolynomial [
	"Answer the i-th subresultant of the receiver with aPolynomial."
	| lambda mu n m c rows matrix tuple |
	m := self degree.
	n := aPolynomial degree.
	lambda := m min: n.
	mu := (m max: n) - 1.
	'i = lambda
			ifTrue:
				[m + 1 < n
					ifTrue: [c := self]
					ifFalse:
						[n + 1 < m
							ifTrue: [c := aPolynomial] ifFalse: [^ nil]].
				^ c * (c leadingCoefficient ^ ((m - n) abs - 1))]'.
	(i between: lambda and: mu) ifTrue: [^ self zero].
	(i between: 0 and: lambda - 1) ifFalse: [self error: 'index out of range'].
	rows := OrderedCollection new.
	tuple := self scalars tuple: m + n - (2*i) evaluating: [:k| self parent constant: (self coefficientAtDegree: m - k + 1)].
	n - i timesRepeat: [rows add: tuple. tuple := tuple shift: 1].
	tuple := self scalars tuple: m + n - (2*i) evaluating: [:k| self parent constant: (aPolynomial coefficientAtDegree: n - k + 1)].
	m - i timesRepeat: [rows add: tuple. tuple := tuple shift: 1].
	matrix := Matrix rows: rows.
	1 to: n - i do: [:k|
		matrix at: k @ (m + n - (2*i)) put: (self shift: n - i - k)].
	1 to: m - i do: [:k|
		matrix at: n - i + k @ (m + n - (2*i)) put: (aPolynomial shift: m - i - k)].
	^ matrix determinant
]

{ #category : #operations }
UnivariatePolynomial >> subresultantChain: aPolynomial [
	"Answer the Subresultant Chain of the receiver with the argument."
	| n answer |
	n := self degree > aPolynomial degree ifTrue: [self degree - 1] ifFalse: [aPolynomial degree].
	answer := OrderedCollection new: n + 2.
	answer add: self; add: aPolynomial.
	n - 1 to: 0 by: -1 do: [:i|
		answer add: (self subresultant: i with: aPolynomial)].
	^ answer
]

{ #category : #operations }
UnivariatePolynomial >> sylvester: aPolynomial [
	"Answer the Sylvester matrix of the receiver with the argument.
	If p,q polynomials of degrees m and n:
		det S(p,q) = res (p,q)
		deg (gcd(p,q)) = m - n + rank (S(p,q))
	Also the kernel of the transposed Sylvester matrix gives all solutions of the Bezout equation:
		f*p + g*q = 0
	"
	| m n rows tuple |
	m := self degree.
	n := aPolynomial degree.
	rows := OrderedCollection new: m+n.
	tuple := self scalars tuple: m+n evaluating: [:i| self coefficientAtDegree: m-i+1].
	n timesRepeat: [rows add: tuple. tuple := tuple shift: 1].
	tuple := self scalars tuple: m+n evaluating: [:i| aPolynomial coefficientAtDegree: n-i+1].
	m timesRepeat: [rows add: tuple. tuple := tuple shift: 1].
	^ Matrix rows: rows
]

{ #category : #operations }
UnivariatePolynomial >> value: anObject [
	"Evaluate the receiver at the given argument using Horner's method."
	| x |
	x := (anObject isTuple or: [anObject isArray])
		ifTrue: [anObject at: 1] ifFalse: [anObject].
	^ coefficients polynomialValue: x
]

{ #category : #roots }
UnivariatePolynomial >> zeroAddition: aPolynomial [
	"Answer a polynomial whose zeros are the addition of the receiver zeros with the zeros of the argument."
	| f g R S y X Y C |
	self degree <= aPolynomial degree
		ifTrue: [f := self. g := aPolynomial]
		ifFalse: [g := self. f := aPolynomial].
	R := self parent.
	y := R rank + 1.
	S := self scalars polynomialsIn: R rank + 1.
	X := S x: R indeterminate.
	Y := S x: y.
	f isMonic ifFalse: [f := f monic]. "otherwise the companion matrix is undefined"
	C := f companion apply: R embedding.
	^ (((g value: X - Y) asUnivariateIn: y) value: C) determinant
]

{ #category : #roots }
UnivariatePolynomial >> zeroNegation [
	"Answer a polynomial whose zeros are the receiver zeros negated."
	^ self parent coefficients:
		(self degree odd "this distinction is made to keep the leading coefficient positive, as a minimal polynomial"
			ifTrue: [self coefficients withIndexCollect: [:each :i| i odd ifTrue: [each negated] ifFalse: [each]]]
			ifFalse: [self coefficients withIndexCollect: [:each :i| i even ifTrue: [each negated] ifFalse: [each]]])
]

{ #category : #roots }
UnivariatePolynomial >> zeroProduct: aPolynomial [
	"Answer a polynomial whose zeros are the product of the receiver zeros by the zeros of the argument."
	| f g C |
	self degree <= aPolynomial degree
		ifTrue: [f := self. g := aPolynomial]
		ifFalse: [g := self. f := aPolynomial].
	f isMonic ifFalse: [f := f monic]. "otherwise the companion matrix is undefined"
	C := f companion apply: self parent embedding.
	^ (g homogenized asUnivariate value: C) determinant
]

{ #category : #roots }
UnivariatePolynomial >> zeroRaisedTo: anInteger [
	"Answer a polynomial whose zeros are the zeros of the receiver raised to anInteger."
	self notYetImplemented
]

{ #category : #roots }
UnivariatePolynomial >> zeroReciprocal [
	"Answer a polynomial whose zeros are the reciprocals of the receiver's zeros."

	^ self reversed
]

{ #category : #roots }
UnivariatePolynomial >> zeroSquareRoot [
	^ self value: self parent x squared
]
