Class {
	#name : #PolynomialTest,
	#superclass : #TestCase,
	#category : #MathematicsTests
}

{ #category : #tests }
PolynomialTest >> testAllMonomialsOfDegree [
	| d n |
	n := 5 atRandom.
	d := 5 atRandom.
	'self assert: (ZZ polynomialsIn: n :: allMonomialsOfDegree: d) size = (n+d-1 choose: d)'
]

{ #category : #tests }
PolynomialTest >> testArithmeticOver: R [
	| x f g |
'	x := R polynomials x.
	f := x^2 + (x*2) - 1.
	g := x^2 - (x*2) + 1.
	self assert: f+g = (x^2 * 2).
	self assert: f-g = (x*4 - 2).
	self assert: f*g = (x^4 - (x^2 * 4) + (x*4) - 1).
	self assert: f*g // g = f.
	self assert: (f*g \\ g) isZero.
	self assert: (f*g + (x - 1) \\ g) = (x - 1)'

]

{ #category : #tests }
PolynomialTest >> testArithmeticQQ [
	self testArithmeticOver: QQ
]

{ #category : #tests }
PolynomialTest >> testArithmeticZ2 [
	self testArithmeticOver: ZZ / 2
]

{ #category : #tests }
PolynomialTest >> testArithmeticZ3 [
	self testArithmeticOver: ZZ / 3
]

{ #category : #tests }
PolynomialTest >> testArithmeticZm [
	self testArithmeticOver: ZZ / (2 + 100 atRandom)
]

{ #category : #tests }
PolynomialTest >> testCRT [
	| x f1 f2 f3 crt r1 r2 r3 h |
	x := QQ polynomials x.
	f1 := (x raisedTo: 5) + 1.
	f2 := (x raisedTo: 2) + 1.
	f3 := x - 1.
	crt := CRT
		mod:
			{f1.
			f2.
			f3}.
	r1 := x - 1.
	r2 := x + 1.
	r3 := x - x.	"zero"
	h := crt
		solve:
			{r1.
			r2.
			r3}.
	self assert: h \\ f1 equals: r1.
	self assert: h \\ f2 equals: r2.
	self assert: h \\ f3 equals: r3
]

{ #category : #tests }
PolynomialTest >> testCompanionMatrix [
	| x p |
	x := QQ polynomials x.
	p := (x raisedTo: 2) + (x * 2) - 1.
	self assert: p companion characteristicPolynomial equals: p.
	self assert: p companion minimalPolynomial equals: p
]

{ #category : #tests }
PolynomialTest >> testContentAndPrimitive [
	| Zx Zxy x y f |
	Zx := ZZ polynomialsIn: #(x).
	Zxy := Zx polynomialsIn: #(y).
	x := Zx x.
	y := Zxy x.
	f := 2 * x * y + (2 * (x raisedTo: 2)).
	self assert: f primitive * f content equals: f
]

{ #category : #tests }
PolynomialTest >> testContentAndPrimitiveAtRandom [
	| Zx f |
	Zx := ZZ polynomials.
	f := Zx atRandomBits: 100 maxDegree: (1 to: 10) atRandom.
	self assert: f primitive * f content equals: f
]

{ #category : #tests }
PolynomialTest >> testDiscriminant [
	| Zx x f g |
	Zx := ZZ polynomials.
	x := Zx x.
	f := (x raisedTo: 2) + x + 1.
	g := (x raisedTo: 3) + 1.
	self
		assert: (f * g) discriminant
		equals: f discriminant * g discriminant * (f resultant: g) squared
]

{ #category : #tests }
PolynomialTest >> testDiscriminant2 [
	| Zx x f |
	Zx := ZZ polynomials.
	x := Zx x.
	f := (x raisedTo: 2) - x - 36042.
	self assert: f discriminant = 144169	"this is a prime, although looks like a square :)"
]

{ #category : #tests }
PolynomialTest >> testDivision: F [
	| Fx f g |
	Fx := F polynomials.
	f := Fx atRandomBits: 100 maxDegree: 10 atRandom.
	[g := Fx atRandomBits: 100 maxDegree: 10 atRandom. g isZero] whileTrue.
	self assert: (f // g) * g + (f \\ g) = f
]

{ #category : #tests }
PolynomialTest >> testDivisionQ [
	self testDivision: QQ
]

{ #category : #tests }
PolynomialTest >> testDivisionZ2 [
	self testDivision: (PrimeField new: 2)
]

{ #category : #tests }
PolynomialTest >> testDivisionZ65535 [
	self testDivision: (PrimeField new: (2 raisedTo: 17) - 1)
]

{ #category : #tests }
PolynomialTest >> testDomainError [
	| f g |
	f := ZZ polynomials atRandomBits: 10.
	self should: [f / 2] raise: DomainError.
	g := QQ polynomials atRandomBits: 100 maxDegree: 5. "will have denominators"
	self should: [f + g] raise: DomainError.
	self should: [f * g] raise: DomainError
]

{ #category : #tests }
PolynomialTest >> testEPRS [
	"Example from Zippel."
	| a b eprs |
	a := ZZ polynomials coefficients: #(1 0 1 0 -3 -3 8 2 -5) reversed.
		b := ZZ polynomials coefficients: #(3 0 5 0 -4 -9 21) reversed.
		eprs := ((a eprs: b ) collect: [:each| each coefficients reversed asArray]) asArray.
	self assert: eprs = #((1 0 1 0 -3 -3 8 2 -5)
		(3 0 5 0 -4 -9 21)
		(-15 0 3 0 -9) 
		(15795 30375 -59535) 
		(1254542875143750 -1654608338437500) (12593338795500743100931141992187500))
]

{ #category : #tests }
PolynomialTest >> testEvaluationHomomorphism [
	| Zx f g a |
	Zx := ZZ polynomials.
	f := Zx atRandomBits: 1000 maxDegree: 10.
	g := Zx atRandomBits: 1000 maxDegree: 10.
	a := ZZ atRandomBits: 100.
	self assert: (f + g value: a) equals: (f value: a) + (g value: a).
	self assert: (f - g value: a) equals: (f value: a) - (g value: a).
	self assert: (f * g value: a) equals: (f value: a) * (g value: a).
	self
		assert: ((f raisedTo: 3) value: a)
		equals: ((f value: a) raisedTo: 3)
]

{ #category : #tests }
PolynomialTest >> testEvaluationHomomorphism: F [
	| Fx f g a |
	Fx := F polynomials.
	f := Fx atRandomDegree: 10 atRandom.
	g := Fx atRandomDegree: 10 atRandom.
	a := F atRandom.
	self assert: (f + g value: a) equals: (f value: a) + (g value: a).
	self assert: (f - g value: a) equals: (f value: a) - (g value: a).
	self assert: (f * g value: a) equals: (f value: a) * (g value: a).
	self
		assert: ((f raisedTo: 3) value: a)
		equals: ((f value: a) raisedTo: 3)
]

{ #category : #tests }
PolynomialTest >> testEvaluationHomomorphismMultivariate [
	| Zxyz f g a |
	Zxyz := ZZ polynomialsIn: #(x y z).
	f := Zxyz atRandomBits: 1000 maxDegree: 10.
	g := Zxyz atRandomBits: 1000 maxDegree: 10.
	a := (ZZ raisedTo: 3) atRandomBits: 100.
	self assert: (f + g value: a) equals: (f value: a) + (g value: a).
	self assert: (f - g value: a) equals: (f value: a) - (g value: a).
	self assert: (f * g value: a) equals: (f value: a) * (g value: a).
	self
		assert: ((f raisedTo: 3) value: a)
		equals: ((f value: a) raisedTo: 3)
]

{ #category : #tests }
PolynomialTest >> testEvaluationHomomorphismZ2 [
	self testEvaluationHomomorphism: (PrimeField new: 2) 
]

{ #category : #tests }
PolynomialTest >> testEvaluationHomomorphismZm [
	self testEvaluationHomomorphism: ZZ / (2 + 100 atRandom).
	self testEvaluationHomomorphism: ZZ / ((2 raisedTo: 13) - 2).
	self testEvaluationHomomorphism: ZZ / ((2 raisedTo: 31) - 2) 
]

{ #category : #tests }
PolynomialTest >> testEvaluationHomomorphismZp [
	self testEvaluationHomomorphism: (PrimeField new: 3).
	self testEvaluationHomomorphism: (PrimeField new: 5).
	self
		testEvaluationHomomorphism: (PrimeField new: (2 raisedTo: 13) - 1).
	self
		testEvaluationHomomorphism: (PrimeField new: (2 raisedTo: 31) - 1) 
]

{ #category : #tests }
PolynomialTest >> testEvaluationMultivariate [
	| Zxyz f a x y z |
	Zxyz := ZZ polynomialsIn: #(x y z).
	x := Zxyz x. y := Zxyz y. z := Zxyz z.
	'f := x^2 * y - z.
		a := ZZ ^ 3 atRandomBits: 100.
		self assert: (f value: a) = ((a at: 1)^2 * (a at: 2) - (a at: 3))'
]

{ #category : #tests }
PolynomialTest >> testExactDivisionBug [
	| Zx x f |
	Zx := ZZ polynomials.
	x := Zx x.
	f := x*2.
	self assert: f /// f = Zx one
]

{ #category : #tests }
PolynomialTest >> testExactDivisionMultivariate [
	| Qxy x y f g |
	Qxy := QQ polynomialsIn: #(x y).
	x := Qxy x.
	y := Qxy y.
	f := x-y.
	g := x+y.
	self assert: f * g /// g = f.
	self assert: f * g /// f = g
]

{ #category : #tests }
PolynomialTest >> testExactDivisionMultivariate2 [
	| Qxy x y f g |
	Qxy := QQ polynomialsIn: #(x y).
	x := Qxy x.
	y := Qxy y.
	f := x-y.
	g := x+y.
	self assert: (f * g divisionBy: g) quotient = f.
	self assert: (f * g divisionBy: f) quotient = g
]

{ #category : #tests }
PolynomialTest >> testExactDivisionOverQ [
	| x f g |
	x := QQ polynomials x.
	f := (x raisedTo: 2) + x + 1.
	g := 1 - x.
	self assert: f * g /// g equals: f.
	self assert: f * g /// f equals: g
]

{ #category : #tests }
PolynomialTest >> testExactDivisionOverQRandom [
	| Qx f g |
	Qx := QQ polynomials.
	f := Qx atRandomBits: 100 maxDegree: (1 to: 10) atRandom.
	g := Qx atRandomBits: 100 maxDegree: (1 to: 10) atRandom.
	self assert: f * g /// g equals: f.
	self assert: f * g /// f equals: g
]

{ #category : #tests }
PolynomialTest >> testExactDivisionOverZ [
	| x f g |
	x := ZZ polynomials x.
	f := (x raisedTo: 2) + x + 1.
	g := 1 - x.
	self assert: f * g /// g equals: f.
	self assert: f * g /// f equals: g
]

{ #category : #tests }
PolynomialTest >> testExtendedEuclidBug [
	| x f1 f2 |
	x := QQ polynomials x.
	f1 := (x raisedTo: 2) + 1.
	f2 := x - 1.
	self
		assert:
			(ExtendedEuclid
				on:
					{f1.
					f2}) gcd
		equals: (f1 gcd: f2)
]

{ #category : #tests }
PolynomialTest >> testFiniteFieldFactorization [
	| F Fx x one f factors |
	F := ZZ / 3.
	Fx := F polynomials.
	x := Fx x.
	one := Fx one.
	f := (x raisedTo: 11) + ((x raisedTo: 9) * 2) + ((x raisedTo: 8) * 2) + (x raisedTo: 6) + (x raisedTo: 5) + ((x raisedTo: 3) * 2) + ((x raisedTo: 2) * 2) + one.
	factors := f factors.
	self assert: factors size equals: 8.
	self assert: (factors occurrencesOf: x + (one * 2)) equals: 4.
	self assert: (factors occurrencesOf: (x raisedTo: 2) + one) equals: 3.
	self assert: (factors occurrencesOf: x + one) equals: 1.
	self
		assert: (factors inject: Fx one into: [ :a :b | a * b ])
		equals: f
]

{ #category : #tests }
PolynomialTest >> testFiniteFieldFactorization2 [
	| Z3 x f factors |
	Z3 := ZZ / 3.
	x := Z3 polynomials x.
	f := (x - 1 raisedTo: 2) * (x - 2).
	factors := f factors.
	self assert: factors size equals: 3.
	self assert: (factors occurrencesOf: x - 1) equals: 2.
	self assert: (factors occurrencesOf: x - 2) equals: 1
]

{ #category : #tests }
PolynomialTest >> testFiniteFieldFactorization3 [
	| F9 x f factors |
	F9 := GaloisField new: (3 raisedTo: 2).
	x := F9 polynomials x.
	f := (x - 1 raisedTo: 2) * (x - 2).
	factors := f factors.
	self assert: factors size equals: 3.
	self assert: (factors occurrencesOf: x - 1) equals: 2.
	self assert: (factors occurrencesOf: x - 2) equals: 1
]

{ #category : #tests }
PolynomialTest >> testFiniteFieldFactorization4 [
	| R x f factors |
	R := ZZ / 2.
	x := R polynomials x.
	f := (x raisedTo: 24) - 1.
	factors := f factors.
	self assert: factors size equals: 16.
	self assert: (factors occurrencesOf: x + 1) equals: 8.
	self
		assert: (factors occurrencesOf: (x raisedTo: 2) + x + 1)
		equals: 8
]

{ #category : #tests }
PolynomialTest >> testFiniteFieldFactorization5 [
	| R x |
	R := ZZ / 2.
	x := R polynomials x.
	self
		assert: ((x raisedTo: 15) - 1) factors
		equals:
			{(x + 1).
			((x raisedTo: 2) + x + 1).
			((x raisedTo: 4) + (x raisedTo: 3) + (x raisedTo: 2) + x + 1).
			((x raisedTo: 4) + x + 1).
			((x raisedTo: 4) + (x raisedTo: 3) + 1)} asBag
]

{ #category : #tests }
PolynomialTest >> testFiniteFieldIrreduciblePolynomials [
	"Z/<3>[x] has 8 irreducible monic polynomials of degree 3, out of 27 monic polynomials of degree 3."

	| F Fx f count |
	F := ZZ / 3.
	Fx := F polynomials.
	count := 0.
	(F raisedTo: 3)
		do: [ :each | 
			f := Fx coefficients: each , F one.
			f isIrreducible
				ifTrue: [ count := count + 1.
					self assert: f factors size equals: 1 ]
				ifFalse: [ self assert: f factors size > 1 ] ].
	self assert: count equals: 8
]

{ #category : #tests }
PolynomialTest >> testFiniteFieldIsIrreducible [
	| F Fx x f |
	F := ZZ / 3.
	Fx := F polynomials.
	x := Fx x.
	f := (x raisedTo: 3) + (x * 2) + 1.
	self assert: f factors size equals: 1.
	self assert: f isIrreducible
]

{ #category : #tests }
PolynomialTest >> testFiniteFieldRoots [
	| Z3 x f roots |
	Z3 := ZZ / 3.
	x := Z3 polynomials x.
	f := (x - 1 raisedTo: 2) * (x - 2).
	roots := f allRoots.
	self assert: roots size equals: 3.
	self assert: (roots occurrencesOf: (Z3 project: 1)) equals: 2.
	self assert: (roots occurrencesOf: (Z3 project: 2)) equals: 1
]

{ #category : #tests }
PolynomialTest >> testFiniteFieldSFF [
	| F Fx x one f factors |
	F := ZZ / 3.
	Fx := F polynomials.
	x := Fx x.
	one := Fx one.
	f := (x raisedTo: 11) + ((x raisedTo: 9) * 2) + ((x raisedTo: 8) * 2)
		+ (x raisedTo: 6) + (x raisedTo: 5) + ((x raisedTo: 3) * 2)
		+ ((x raisedTo: 2) * 2) + one.
	factors := f squareFreeFactorization.
	self assert: factors size equals: 8.
	self assert: (factors occurrencesOf: x + (one * 2)) equals: 4.
	self assert: (factors occurrencesOf: (x raisedTo: 2) + one) equals: 3.
	self assert: (factors occurrencesOf: x + one) equals: 1
]

{ #category : #tests }
PolynomialTest >> testGCD [
	| P x f g |
	P := QQ polynomials.
	x := P x.
	f := (x raisedTo: 4) - 1.
	g := (x raisedTo: 6) - 1.
	self assert: (f gcd: g) equals: (x raisedTo: 2) - 1
]

{ #category : #tests }
PolynomialTest >> testGCDMultivariate [
	| Zxy x y f g |
	Zxy := ZZ polynomialsIn: #(x y).
	x := Zxy x.
	y := Zxy y.
	f := (x + y) * (y - x).
	g := y - x raisedTo: 2.
	self assert: (f gcd: g) equals: y - x
]

{ #category : #tests }
PolynomialTest >> testGCDMultivariate2 [
	"Example from Sage documentation."
	| R x y f g |
	R := QQ polynomialsIn: #(x y).
	x := R x. y := R y.
	'f := x^2*y*(x+y)*3.
		g := x*(y^2 - (x^2))*9'.
	self assert: '(f gcd: g) = (x^2 + (x*y))'
]

{ #category : #tests }
PolynomialTest >> testGCDMultivariateOverQ [
	| R x y f g |
	R := QQ polynomialsIn: #(x y).
	x := R x. y := R y.
	'f := x^2*y*6.
		g := x*(y^2)*15 + (x^3*(y^2)*21)'.
	self assert: (f gcd: g) = (x*y)
]

{ #category : #tests }
PolynomialTest >> testGCDMultivariateOverZ [
	| R x y f g |
	R := ZZ polynomialsIn: #(x y).
	x := R x. y := R y.
'	f := x^2*y*6.
	g := x*(y^2)*15 + (x^3*(y^2)*21)'.
	self assert: (f gcd: g) = (x*y*3)
]

{ #category : #tests }
PolynomialTest >> testGCDOverRationalFunctions [
	| R x y f g |
	R := 'QQ polynomialsIn: #(y) :: fractions polynomials'.
	x := R x. y := R scalars x.
'	f := x^2*y*6.
	g := x*(y^2)*15 + (x^3*(y^2)*21)'.
	self assert: (f gcd: g) = x
]

{ #category : #tests }
PolynomialTest >> testGCDOverZ [
	| x f g |
	x := ZZ polynomials x.
	'f := (x^4 - 1)*6.
		g := (x^6 - 1)*9.
		self assert: (f gcd: g) = ((x^2 - 1)*3)'
]

{ #category : #tests }
PolynomialTest >> testGCDOverZ2 [
	| x f g h |
	x := 'ZZ/2 :: polynomials x'.
	'h := x^3 - x + 1.
		f := h * (x + 1) * x.
		g := h * (x + 1) * (x^2 + 1)'.
	self assert: (f gcd: g) = (h * (x + 1))
]

{ #category : #tests }
PolynomialTest >> testGaussLemma [
	"Lemma (Gauss): The product of two primitive polynomials is primitive."

	| Zx f g |
	Zx := ZZ polynomials.
	f := Zx atRandomBits: 100 maxDegree: (5 to: 10) atRandom.
	g := Zx atRandomBits: 100 maxDegree: (5 to: 10) atRandom.
	self assert: (f primitive * g primitive) isPrimitive
]

{ #category : #tests }
PolynomialTest >> testHeight [
	| x |
	x := QQ polynomials x.
	self assert: (x * 2 - 5) height equals: 5.
	self assert: (x * 5 - 2) height equals: 5
]

{ #category : #tests }
PolynomialTest >> testIntegerFactorization [
	| x f factors |
	x := ZZ polynomials x.
	f := (x * 2 - 1 raisedTo: 2) * (x - 2) * ((x raisedTo: 2) + 1)
		* ((x raisedTo: 2) - 2) * 18.
	factors := f factors.
	self assert: factors size equals: 8.
	self assert: factors asSet size equals: 6.
	self assert: factors product equals: f
]

{ #category : #tests }
PolynomialTest >> testInterpolation [
	| Qx f |
	Qx := QQ polynomials.
	f := Qx interpolate: {1 -> 2. 2 -> 3. 4 -> 5}.
	self assert: (f value: 1) = 2.
	self assert: (f value: 2) = 3.
	self assert: (f value: 4) = 5
]

{ #category : #tests }
PolynomialTest >> testInterpolation2 [
	| Qx f |
	Qx := QQ polynomials.
	f := Qx interpolate: {1 -> 2. 2 -> 4. 3 -> 9}.
	self assert: (f value: 1) = 2.
	self assert: (f value: 2) = 4.
	self assert: (f value: 3) = 9
]

{ #category : #tests }
PolynomialTest >> testIsIrreducible [
	"The polynomial x^4 + 1 is irreducible in Z[x] and Q[x], and it is reducible Z/p[x] for all prime numbers p."
	| p |
	'self assert: (ZZ polynomials ! [:x| x^4 + 1] :: isIrreducible).
		self assert: (QQ polynomials ! [:x| x^4 + 1] :: isIrreducible)'.
	p := 1000 atRandom nextPrime.
	'self deny: (ZZ/p :: polynomials ! [:x| x^4 + 1] :: isIrreducible)'
]

{ #category : #tests }
PolynomialTest >> testIsIrreducibleOverQ [
	| x f |
	x := QQ polynomials x.
	f := (x raisedTo: 4) + 1.
	self assert: f isIrreducible.
	self assert: f negated isIrreducible.
	self assert: (f * 2) isIrreducible.
	self assert: (f * (x + 1)) isIrreducible not
]

{ #category : #tests }
PolynomialTest >> testIsIrreducibleOverZ [
	| x f |
	x := ZZ polynomials x.
	f := (x raisedTo: 4) + 1.
	self assert: f isIrreducible.
	self assert: f negated isIrreducible.
	self assert: (f * 2) isIrreducible not.
	self assert: (f * (x + 1)) isIrreducible not
]

{ #category : #tests }
PolynomialTest >> testIsSeparableNot [
	"A tipical example of a polynomial that is NOT separable."
	| p F x Fy y f |
	p := 5. "any prime p"
	F := 'ZZ/p :: polynomials fractions'.
	x := F x.
	Fy := F polynomialsIn: #(y).
	y := Fy x.
	f := 'y^p - x'.
	self assert: f isSeparable not
]

{ #category : #tests }
PolynomialTest >> testMultivariateDivision [
	"Example from Cox IVA 62 p."
	| Zxy x y f f1 f2 division |
	Zxy := ZZ polynomialsIn: #(x y) ordering: (MonomialOrdering lex: #(2 1)).
	x := Zxy x.
	y := Zxy y.
	'f := x*(y^2)+1'.
	f1 := x*y+1.
	f2 := y+1.
	division := f divisionBy: {f1. f2}.
	self assert: division quotients = {y. y one negated}.
	self assert: division remainder = (y one * 2).
	self assert: division verify
]

{ #category : #tests }
PolynomialTest >> testMultivariateDivision2 [
	"Example from Cox IVA 63 p."
	| Zxy x y f f1 f2 division |
	Zxy := ZZ polynomialsIn: #(x y) ordering: (MonomialOrdering lex: #(2 1)).
	x := Zxy x.
	y := Zxy y.
'	f := x^2*y + (x*(y^2)) + (y^2).
	f1 := x*y-1.
	f2 := y^2-1'.
	division := f divisionBy: {f1. f2}.
	self assert: division quotients = {x+y. y one}.
	self assert: division remainder = (x+y+1).
	self assert: division verify
]

{ #category : #tests }
PolynomialTest >> testMultivariateDivision3 [
	"Example from Cox IVA 67 p."
	| Zxy x y f f1 f2 division |
	Zxy := ZZ polynomialsIn: #(x y) ordering: (MonomialOrdering lex: #(2 1)).
	x := Zxy x.
	y := Zxy y.
	'f := x^2*y + (x*(y^2)) + (y^2).
		f1 := x*y-1.
		f2 := y^2-1'.
	division := f divisionBy: {f2. f1}.
	self assert: division quotients = {x+1. x}.
	self assert: division remainder = (x*2+1).
	self assert: division verify
]

{ #category : #tests }
PolynomialTest >> testMultivariateGCDBug [
	| x |
	x := 'QQ polynomialsIn: 3 :: x'.
	self assert: ((x raisedTo: 2) gcd: x) equals: x
]

{ #category : #tests }
PolynomialTest >> testPPRS [
	"Example from Zippel."
	| a b pprs |
	a := ZZ polynomials coefficients: #(1 0 1 0 -3 -3 8 2 -5) reversed.
	b := ZZ polynomials coefficients: #(3 0 5 0 -4 -9 21) reversed.
	pprs := ((a pprs: b) collect: [:each| each coefficients reversed asArray]) asArray.
	self assert: pprs = #((1 0 1 0 -3 -3 8 2 -5) 
		(3 0 5 0 -4 -9 21)
		(-5 0 1 0 -3)
		(13 25 -49)
		(4663 -6150)
		(1))
]

{ #category : #tests }
PolynomialTest >> testPseudoDivision1 [
	| Zxy x y division |
	Zxy := ZZ polynomialsIn: #(x y).
	x := Zxy x.
	y := Zxy y.
	division := (x raisedTo: 2) + (y raisedTo: 2)
		pseudoDivisionBy: y - x
		in: 2.
	self assert: division quotient asMultivariate equals: x + y.
	self
		assert: division remainder asMultivariate
		equals: (x raisedTo: 2) * 2.
	self assert: division verify
]

{ #category : #tests }
PolynomialTest >> testPseudoDivision2 [
	| Zxy x y division |
	Zxy := QQ polynomialsIn: #(x y).
	x := Zxy x.
	y := Zxy y.
	division := (x raisedTo: 2) + (y raisedTo: 2)
		pseudoDivisionBy: (y - x) * 2
		in: 2.
	self assert: division quotient asMultivariate equals: (x + y) * 2.
	self
		assert: division remainder asMultivariate
		equals: (x raisedTo: 2) * 8.
	self assert: division verify
]

{ #category : #tests }
PolynomialTest >> testPseudoDivision3 [
	| Zxy x y division |
	Zxy := ZZ polynomialsIn: #(x y).
	x := Zxy x.
	y := Zxy y.
	division := (x raisedTo: 2) + (y raisedTo: 2)
		pseudoDivisionBy: y - x
		in: 2.
	self assert: division quotient asMultivariate equals: x + y.
	self
		assert: division remainder asMultivariate
		equals: (x raisedTo: 2) * 2.
	self assert: division verify.
	division := (x raisedTo: 2) + (y raisedTo: 2)
		pseudoDivisionBy: x - y
		in: 2.
	self assert: division quotient asMultivariate equals: (x + y) negated.
	self
		assert: division remainder asMultivariate
		equals: (x raisedTo: 2) * 2.
	self assert: division verify
]

{ #category : #tests }
PolynomialTest >> testPseudoDivision: R [
	| Rx f g div |
	Rx := R polynomials.
	f := Rx atRandomBits: 100 maxDegree: 10 atRandom.
	[ g := Rx atRandomBits: 100 maxDegree: 10 atRandom.
	g isZero ] whileTrue.
	div := f pseudoDivisionBy: g.
	self assert: div verify
]

{ #category : #tests }
PolynomialTest >> testPseudoDivisionUnivariate [
	| zx x division |
	zx := ZZ polynomials.
	x := zx x.
	division := (x raisedTo: 3) + x + 1
		pseudoDivisionBy: (x raisedTo: 2) * 3 + x + 1.
	self assert: division quotient equals: x * 3 - 1.
	self assert: division remainder equals: x * 7 + 10.
	self assert: division delta equals: 2.
	self assert: division verify
]

{ #category : #tests }
PolynomialTest >> testPseudoDivisionUnivariate2 [
	"Example from Zippel book"

	| Zx a b |
	Zx := ZZ polynomials.
	a := Zx coefficients: #(1 0 1 0 -3 -3 8 2 -5) reversed.
	b := Zx coefficients: #(3 0 5 0 -4 -9 21) reversed.
	^ self assert: (a pseudoDivisionBy: b) verify
]

{ #category : #tests }
PolynomialTest >> testPseudoDivisionZ [
	self testPseudoDivision: ZZ
]

{ #category : #tests }
PolynomialTest >> testPseudoDivisionZ6 [
	self testPseudoDivision: ZZ / 6
]

{ #category : #tests }
PolynomialTest >> testPseudoRemainder [
	| Zx x a b r |
	Zx := ZZ polynomials.
	x := Zx x.
	a := (x raisedTo: 8) + (x raisedTo: 6) - (3 * (x raisedTo: 4))
		- (3 * (x raisedTo: 3)) + (8 * (x raisedTo: 2)) + (2 * x) - 5.
	b := 3 * (x raisedTo: 6) + (5 * (x raisedTo: 4))
		- (4 * (x raisedTo: 2)) - (9 * x) + 21.
	r := Zx coefficients: #(-9 0 3 0 -15).
	self assert: (a pseudoRem: b) equals: r.
	self assert: (a pseudoDivisionBy: b) remainder equals: r
]

{ #category : #tests }
PolynomialTest >> testQuotientRingBug [
	"This is fixed by making ideals of Z[x] have generators with positive leading coefficient. But it could be still a problem for polynomials over other rings."

	| R f Q pi a b |
	R := ZZ polynomials.
	f := R ! [ :x | (x raisedTo: 2) *(-1) - 1 ].
	Q := R / f.
	pi := Q projection.
	a := R x - 1.
	b := (R x raisedTo: 2) + 1.
	self assert: (pi value: a) + (pi value: b) equals: (pi value: a + b)
]

{ #category : #tests }
PolynomialTest >> testRationalFactorization [
	| x f factors |
	x := QQ polynomials x.
	f := (x - (1 / 2) raisedTo: 2) * (x - 2) * ((x raisedTo: 2) + 1)
		* ((x raisedTo: 2) - 2).
	factors := f factors.
	self assert: factors size equals: 5.
	self assert: factors asSet size equals: 4.
	self assert: factors product monic equals: f monic	"up to a unit"
]

{ #category : #tests }
PolynomialTest >> testRationalRoots [
	| x f roots |
	x := QQ polynomials x.
	f := (x - (1 / 2) raisedTo: 2) * (x - 2) * ((x raisedTo: 2) + 1)
		* ((x raisedTo: 2) - 2).
	roots := f allRoots.
	self assert: roots size equals: 3.
	self assert: (roots occurrencesOf: 1 / 2) equals: 2.
	self assert: (roots occurrencesOf: 2) equals: 1
]

{ #category : #tests }
PolynomialTest >> testRationalRootsBug [
	| x f roots |
	x := QQ polynomials x.
	f := (x raisedTo: 3) * -1 + (3 * x) + 2.
	roots := f allRoots.
	self assert: roots size equals: 3.
	self assert: (roots occurrencesOf: -1) equals: 2.
	self assert: (roots occurrencesOf: 2) equals: 1
]

{ #category : #tests }
PolynomialTest >> testRealRoots [
	| x f roots |
	x := QQ polynomials x.
	f := (x - (1 / 2) raisedTo: 2) * (x - 2) * ((x raisedTo: 2) + 1)
		* ((x raisedTo: 2) - 2).
	roots := f allRootsIn: RR.
	self assert: roots size equals: 5.
	self assert: roots asSet size equals: 4.
	self assert: (roots occurrencesOf: 1 / 2) equals: 2.
	self assert: (roots occurrencesOf: 2) equals: 1
]

{ #category : #tests }
PolynomialTest >> testRemainderInconsistency [
	"In Sage these two give the same result."

	| X x |
	X := ZZ polynomials x.
	x := QQ polynomials x.
	self
		assert: (x \\ (1 - x)) leadingCoefficient
		equals: (X \\ (1 - X)) leadingCoefficient
]

{ #category : #tests }
PolynomialTest >> testResultant [
	| Zx x f g f2 g2 h |
	Zx := ZZ polynomials.
	x := Zx x.
	f := (x raisedTo: 2) + x + 1.
	f2 := f * (x + 2).
	g := (x raisedTo: 3) + 1.
	g2 := g * (x + 2).
	h := (x raisedTo: 4) + 1.
	self assert: (f resultant: g) isZero not.	"not 0 because f and g have no common roots"
	self assert: (f2 resultant: g2) isZero.	"res(f2,g2) = 0 because f2 and g2 have a common root -2."
	self
		assert: (-1 raisedTo: f degree * g degree) * (f resultant: g)
		equals: (g resultant: f).
	self
		assert: (f * g resultant: h)
		equals: (f resultant: h) * (g resultant: h)
]

{ #category : #tests }
PolynomialTest >> testResultant2 [
	| Zx x f g |
	Zx := ZZ polynomials.
	x := Zx x.
	f := 2 * (x - 5) * (x - 11).
	g := 3 * (x - 7).
	self
		assert: (f resultant: g)
		equals: (2 raisedTo: 1) * (3 raisedTo: 2) * (5 - 7) * (11 - 7)
]

{ #category : #tests }
PolynomialTest >> testSPRS [
	"Example from Zippel."
	| a b sprs |
	a := ZZ polynomials coefficients: #(1 0 1 0 -3 -3 8 2 -5) reversed.
	b := ZZ polynomials coefficients: #(3 0 5 0 -4 -9 21) reversed.
	sprs :=( (a sprs: b) collect: [:each| each coefficients reversed asArray]) asArray.
	self assert: sprs = #((1 0 1 0 -3 -3 8 2 -5)
		#(3 0 5 0 -4 -9 21)
		#(15 0 -3 0 9)
		#(65 125 -245)
		#(9326 -12300)
		#(260708))

]

{ #category : #tests }
PolynomialTest >> testShift [
	| Zx x f |
	Zx := ZZ polynomials.
	x := Zx x.
	f := Zx atRandomBits: 10.
	self assert: (f shift: 10) degree equals: f degree + 10.
	self assert: ((f shift: 10) shift: -10) equals: f.
	self assert: f * (x raisedTo: 3) equals: (f shift: 3).
	self assert: (f * (x raisedTo: 3) shift: -3) equals: f
]

{ #category : #tests }
PolynomialTest >> testSquareFree [
	| P x f1 f2 f3 f |
	P := QQ polynomials.
	x := P x.
	f1 := (x raisedTo: 2) + x + 1.
	f2 := 1 - x.
	f3 := x - 2.
	f := f1 * f1 * f2 * f3 * f3 * f3.
	self assert: f squareFree equals: f1 * f2 * f3
]

{ #category : #tests }
PolynomialTest >> testSquareFreeMultivariate [
	| P x y f1 f2 f |
	P := QQ polynomialsIn: #(x y).
	x := P x.
	y := P y.
	f1 := x + 1.
	f2 := y + 1.
	f := f1 * f1 * f2 * f2.
	self assert: f squareFree equals: f1 * f2
]

{ #category : #tests }
PolynomialTest >> testSubresultant [
	"deg(gcd(f,g)) = d iff subresultant(f,g,k) = 0 for all k < d and subresultant(f,g,d) ~= 0, and the d-th subresultant coefficient is in fact a gcd of f and g."

	| x f g |
	x := ZZ polynomials x.
	f := ((x raisedTo: 4) - 1) * 6.
	g := ((x raisedTo: 6) - 1) * 9.
	"self assert: (f gcd: g) = ((x^2 - 1)*3)"
	self assert: (f subresultant: 0 with: g) isZero.
	self assert: (f subresultant: 1 with: g) isZero.
	self assert: (f subresultant: 2 with: g) isZero not.
	self
		assert: (f subresultant: 2 with: g) primitive
		equals: (x raisedTo: 2) - 1
]

{ #category : #tests }
PolynomialTest >> testSubresultant0 [
	| Zx x f g |
	Zx := ZZ polynomials.
	x := Zx x.
	f := 2 * (x - 5) * (x - 11).
	g := 3 * (x - 7).
	self
		assert: (f resultant: g)
		equals: (f subresultant: 0 with: g) asScalar
]

{ #category : #tests }
PolynomialTest >> testUnivariateMultivariateConversion [
	| Qx x y f |
	Qx := QQ polynomialsIn: #(x y).
	x := Qx x.
	y := Qx y.
	f := (x raisedTo: 2) * y.
	self assert: f asUnivariate asMultivariate equals: f.
	'self assert: (f asUnivariateIn: 2 :: asMultivariate) = f'
]

{ #category : #tests }
PolynomialTest >> testUnivariateMultivariateConversion2 [
	| Qx x y f f2 x0 y0 |
	Qx := QQ polynomialsIn: #(x y).
	x := Qx x.
	y := Qx y.
	f := Qx zero.
	10
		timesRepeat: [ f := f
				+
					((10 atRandom - 5)
						* (x raisedTo: (3 atRandom - 1) * (y raisedTo: 3 atRandom - 1))) ].
	f2 := f asUnivariate.
	self assert: f2 asMultivariate equals: f.
	x0 := (-100 to: 100) atRandom.
	y0 := (-100 to: 100) atRandom.
	self
		assert: ((f2 value: y0) value: x0)
		equals:
			(f
				value:
					{x0.
					y0})
]

{ #category : #tests }
PolynomialTest >> testZeroCoefficientBug [
	| Qx |
	Qx := QQ polynomials.
	self assert: (Qx one * 0) isZero
]
