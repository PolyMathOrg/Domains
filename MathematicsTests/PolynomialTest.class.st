Class {
	#name : #PolynomialTest,
	#superclass : #TestCase,
	#category : #MathematicsTests
}

{ #category : #'as yet unclassified' }
PolynomialTest >> testAllMonomialsOfDegree [
	| d n |
	n := 5 atRandom.
	d := 5 atRandom.
	'self assert: (ZZ polynomialsIn: n :: allMonomialsOfDegree: d) size = (n+d-1 choose: d)'
]

{ #category : #'as yet unclassified' }
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

{ #category : #'as yet unclassified' }
PolynomialTest >> testArithmeticQQ [
	self testArithmeticOver: QQ
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testArithmeticZ2 [
	self testArithmeticOver: ZZ/2
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testArithmeticZ3 [
	self testArithmeticOver: ZZ/3
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testArithmeticZm [
	self testArithmeticOver: ZZ/(2 + 100 atRandom)
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testCRT [
	| x f1 f2 f3 crt r1 r2 r3 h |
	'x := QQ polynomials x.
		f1 := x^5 + 1.
		f2 := x^2 + 1.
		f3 := x - 1.
		crt := CRT mod: {f1. f2. f3}.
		r1 := x-1.
		r2 := x+1.
		r3 := x-x. "zero"
		h := crt solve: {r1. r2. r3}'.
	self assert: h \\ f1 = r1.
	self assert: h \\ f2 = r2.
	self assert: h \\ f3 = r3
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testCompanionMatrix [
	| x p |
	x := QQ polynomials x.
	p := 'x^2 + (x*2) - 1'.
	self assert: p companion characteristicPolynomial = p.
	self assert: p companion minimalPolynomial = p
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testContentAndPrimitive [
	| Zx Zxy x y f |
	Zx := ZZ polynomialsIn: #(x).
	Zxy := Zx polynomialsIn: #(y).
	x := Zx x.
	y := Zxy x.
'	f := 2*x*y + (2*(x^2))'.
	self assert: f primitive * f content = f
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testContentAndPrimitiveAtRandom [
	| Zx f |
	Zx := ZZ polynomials.
	f := Zx atRandomBits: 100 maxDegree: (1 to: 10) atRandom.
	self assert: f primitive * f content = f
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testDiscriminant [
	| Zx x f g |
	Zx := ZZ polynomials.
	x := Zx x.
'	f := x^2 + x + 1.
	g := x^3 + 1'.
	self assert: (f*g) discriminant = (f discriminant * g discriminant * (f resultant: g) squared)
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testDiscriminant2 [
	| Zx x f |
	Zx := ZZ polynomials.
	x := Zx x.
'	f := x^2 - x - 36042'.
	self assert: f discriminant = 144169 "this is a prime, although looks like a square :)"
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testDivision: F [
	| Fx f g |
	Fx := F polynomials.
	f := Fx atRandomBits: 100 maxDegree: 10 atRandom.
	[g := Fx atRandomBits: 100 maxDegree: 10 atRandom. g isZero] whileTrue.
	self assert: (f // g) * g + (f \\ g) = f
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testDivisionQ [
	self testDivision: QQ
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testDivisionZ2 [
	self testDivision: (PrimeField new: 2)
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testDivisionZ65535 [
	self testDivision: (PrimeField new: (2 raiseTo: 17) - 1)
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testDomainError [
	| f g |
	f := ZZ polynomials atRandomBits: 10.
	self should: [f / 2] raise: DomainError.
	g := QQ polynomials atRandomBits: 100 maxDegree: 5. "will have denominators"
	self should: [f + g] raise: DomainError.
	self should: [f * g] raise: DomainError
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testEPRS [
	"Example from Zippel."
	| a b eprs |
	'a := ZZ polynomials coefficients: #(1 0 1 0 -3 -3 8 2 -5) reversed.
		b := ZZ polynomials coefficients: #(3 0 5 0 -4 -9 21) reversed.
		eprs := a eprs: b :: collect: [:each| each coefficients reversed asArray] :: asArray'.
	self assert: eprs = #((1 0 1 0 -3 -3 8 2 -5)
		(3 0 5 0 -4 -9 21)
		(-15 0 3 0 -9) 
		(15795 30375 -59535) 
		(1254542875143750 -1654608338437500) (12593338795500743100931141992187500))
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testEvaluationHomomorphism [
	| Zx f g a |
	Zx := ZZ polynomials.
	f := Zx atRandomBits: 1000 maxDegree: 10.
	g := Zx atRandomBits: 1000 maxDegree: 10.
	a := ZZ atRandomBits: 100.
	self assert: (f+g value: a) = ((f value: a) + (g value: a)).
	self assert: (f-g value: a) = ((f value: a) - (g value: a)).
	self assert: (f*g value: a) = ((f value: a) * (g value: a)).
	self assert: '(f^3 value: a) = ((f value: a)^3)'
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testEvaluationHomomorphism: F [
	| Fx f g a |
	Fx := F polynomials.
	f := Fx atRandomDegree: 10 atRandom.
	g := Fx atRandomDegree: 10 atRandom.
	a := F atRandom.
	self assert: (f+g value: a) = ((f value: a) + (g value: a)).
	self assert: (f-g value: a) = ((f value: a) - (g value: a)).
	self assert: (f*g value: a) = ((f value: a) * (g value: a)).
	self assert: '(f^3 value: a) = ((f value: a)^3)'
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testEvaluationHomomorphismMultivariate [
	| Zxyz f g a |
	Zxyz := ZZ polynomialsIn: #(x y z).
	f := Zxyz atRandomBits: 1000 maxDegree: 10.
	g := Zxyz atRandomBits: 1000 maxDegree: 10.
	a := 'ZZ ^ 3' atRandomBits: 100.
	self assert: (f+g value: a) = ((f value: a) + (g value: a)).
	self assert: (f-g value: a) = ((f value: a) - (g value: a)).
	self assert: (f*g value: a) = ((f value: a) * (g value: a)).
	self assert: '(f^3 value: a) = ((f value: a)^3)'
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testEvaluationHomomorphismZ2 [
	self testEvaluationHomomorphism: (PrimeField new: 2)
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testEvaluationHomomorphismZm [
	'self testEvaluationHomomorphism: ZZ / (2 + 100 atRandom).
		self testEvaluationHomomorphism: ZZ / (2^13 - 2).
		self testEvaluationHomomorphism: ZZ / (2^31 - 2)'
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testEvaluationHomomorphismZp [
	self testEvaluationHomomorphism: (PrimeField new: 3).
	self testEvaluationHomomorphism: (PrimeField new: 5).
	'self testEvaluationHomomorphism: (PrimeField new: 2^13 - 1).
		self testEvaluationHomomorphism: (PrimeField new: 2^31 - 1)'
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testEvaluationMultivariate [
	| Zxyz f a x y z |
	Zxyz := ZZ polynomialsIn: #(x y z).
	x := Zxyz x. y := Zxyz y. z := Zxyz z.
	'f := x^2 * y - z.
		a := ZZ ^ 3 atRandomBits: 100.
		self assert: (f value: a) = ((a at: 1)^2 * (a at: 2) - (a at: 3))'
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testExactDivisionBug [
	| Zx x f |
	Zx := ZZ polynomials.
	x := Zx x.
	f := x*2.
	self assert: f /// f = Zx one
]

{ #category : #'as yet unclassified' }
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

{ #category : #'as yet unclassified' }
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

{ #category : #'as yet unclassified' }
PolynomialTest >> testExactDivisionOverQ [
	| x f g |
	x := QQ polynomials x.
	f := 'x^2 + x + 1'.
	g := 1 - x.
	self assert: f * g /// g = f.
	self assert: f * g /// f = g
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testExactDivisionOverQRandom [
	| Qx f g |
	Qx := QQ polynomials.
	f := Qx atRandomBits: 100 maxDegree: (1 to: 10) atRandom.
	g := Qx atRandomBits: 100 maxDegree: (1 to: 10) atRandom.
	self assert: f * g /// g = f.
	self assert: f * g /// f = g
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testExactDivisionOverZ [
	| x f g |
	x := ZZ polynomials x.
	f := 'x^2 + x + 1'.
	g := 1 - x.
	self assert: f * g /// g = f.
	self assert: f * g /// f = g
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testExtendedEuclidBug [
	| x f1 f2 |
	x := QQ polynomials x.
	f1 := 'x^2 + 1'.
	f2 := x - 1.
	self assert: (ExtendedEuclid on: {f1. f2}) gcd = (f1 gcd: f2)
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testFiniteFieldFactorization [
	| F Fx x one f factors |
	F := ZZ / 3.
	Fx := F polynomials.
	x := Fx x.
	one := Fx one.
	'f := x^11 + (x^9 * 2) + (x^8 * 2) + (x^6) + (x^5) + (x^3 * 2) + (x^2 * 2) + one'.
	factors := f factors.
	self assert: factors size = 8.
	self assert: (factors occurrencesOf: x + (one*2)) = 4.
	self assert: '(factors occurrencesOf: x^2 + one) = 3'.
	self assert: (factors occurrencesOf: x + one) = 1.
	self assert: (factors inject: Fx one into: [:a :b| a*b]) = f
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testFiniteFieldFactorization2 [
	| Z3 x f factors |
	Z3 := ZZ / 3.
	x := Z3 polynomials x.
	'f := (x-1)^2*(x-2)'.
	factors := f factors.
	self assert: factors size = 3.
	self assert: (factors occurrencesOf: x-1) = 2.
	self assert: (factors occurrencesOf: x-2) = 1
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testFiniteFieldFactorization3 [
	| F9 x f factors |
	F9 := GaloisField new: (3 raiseTo: 2).
	x := F9 polynomials x.
	f := '(x-1)^2*(x-2)'.
	factors := f factors.
	self assert: factors size = 3.
	self assert: (factors occurrencesOf: x-1) = 2.
	self assert: (factors occurrencesOf: x-2) = 1
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testFiniteFieldFactorization4 [
	| R x f factors |
	R := ZZ / 2.
	x := R polynomials x.
	f := 'x^24 - 1'.
	factors := f factors.
	self assert: factors size = 16.
	'self assert: (factors occurrencesOf: x+1) = 8.
		self assert: (factors occurrencesOf: x^2+x+1) = 8'
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testFiniteFieldFactorization5 [
	| R x |
	R := ZZ / 2.
	x := R polynomials x.
'	self assert: (x^15 - 1) factors = {x + 1. x^2 + x + 1. x^4 + (x^3) + (x^2) + x + 1. x^4 + x + 1. x^4 + (x^3) + 1} asBag'
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testFiniteFieldIrreduciblePolynomials [
	"Z/<3>[x] has 8 irreducible monic polynomials of degree 3, out of 27 monic polynomials of degree 3."
	| F Fx f count |
	F := ZZ / 3.
	Fx := F polynomials.
	count := 0.
	('F ^ 3') do: [:each|
		f := (Fx coefficients: each, F one).
		f isIrreducible
			ifTrue:
				[count := count + 1.
				self assert: f factors size = 1]
			ifFalse:
				[self assert: f factors size > 1]].
	self assert: count = 8
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testFiniteFieldIsIrreducible [
	| F Fx x f |
	F := ZZ / 3.
	Fx := F polynomials.
	x := Fx x.
'	f := x^3 + (x*2) + 1'.
	self assert: f factors size = 1.
	self assert: f isIrreducible
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testFiniteFieldRoots [
	| Z3 x f roots |
	Z3 := ZZ / 3.
	x := Z3 polynomials x.
	f := '(x-1)^2*(x-2)'.
	roots := f allRoots.
	self assert: roots size = 3.
	self assert: (roots occurrencesOf: (Z3 project: 1)) = 2.
	self assert: (roots occurrencesOf: (Z3 project: 2)) = 1
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testFiniteFieldSFF [
	| F Fx x one f factors |
	F := ZZ / 3.
	Fx := F polynomials.
	x := Fx x.
	one := Fx one.
'	f := x^11 + (x^9 * 2) + (x^8 * 2) + (x^6) + (x^5) + (x^3 * 2) + (x^2 * 2) + one'.
	factors := f squareFreeFactorization.
	self assert: factors size = 8.
	self assert: (factors occurrencesOf: x + (one*2)) = 4.
'	self assert: (factors occurrencesOf: x^2 + one) = 3'.
	self assert: (factors occurrencesOf: x + one) = 1
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testGCD [
	| P x f g |
	P := QQ polynomials.
	x := P x.
	'f := x^4 - 1.
		g := x^6 - 1.
		self assert: (f gcd: g) = (x^2 - 1)'
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testGCDMultivariate [
	| Zxy x y f g |
	Zxy := ZZ polynomialsIn: #(x y).
	x := Zxy x.
	y := Zxy y.
	f := (x+y)*(y-x).
	g := '(y-x)^2'.
	self assert: (f gcd: g) = (y-x)
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testGCDMultivariate2 [
	"Example from Sage documentation."
	| R x y f g |
	R := QQ polynomialsIn: #(x y).
	x := R x. y := R y.
	'f := x^2*y*(x+y)*3.
		g := x*(y^2 - (x^2))*9'.
	self assert: '(f gcd: g) = (x^2 + (x*y))'
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testGCDMultivariateOverQ [
	| R x y f g |
	R := QQ polynomialsIn: #(x y).
	x := R x. y := R y.
	'f := x^2*y*6.
		g := x*(y^2)*15 + (x^3*(y^2)*21)'.
	self assert: (f gcd: g) = (x*y)
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testGCDMultivariateOverZ [
	| R x y f g |
	R := ZZ polynomialsIn: #(x y).
	x := R x. y := R y.
'	f := x^2*y*6.
	g := x*(y^2)*15 + (x^3*(y^2)*21)'.
	self assert: (f gcd: g) = (x*y*3)
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testGCDOverRationalFunctions [
	| R x y f g |
	R := 'QQ polynomialsIn: #(y) :: fractions polynomials'.
	x := R x. y := R scalars x.
'	f := x^2*y*6.
	g := x*(y^2)*15 + (x^3*(y^2)*21)'.
	self assert: (f gcd: g) = x
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testGCDOverZ [
	| x f g |
	x := ZZ polynomials x.
	'f := (x^4 - 1)*6.
		g := (x^6 - 1)*9.
		self assert: (f gcd: g) = ((x^2 - 1)*3)'
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testGCDOverZ2 [
	| x f g h |
	x := 'ZZ/2 :: polynomials x'.
	'h := x^3 - x + 1.
		f := h * (x + 1) * x.
		g := h * (x + 1) * (x^2 + 1)'.
	self assert: (f gcd: g) = (h * (x + 1))
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testGaussLemma [
	"Lemma (Gauss): The product of two primitive polynomials is primitive."
	| Zx f g |
	Zx := ZZ polynomials.
	f := Zx atRandomBits: 100 maxDegree: (5 to: 10) atRandom.
	g := Zx atRandomBits: 100 maxDegree: (5 to: 10) atRandom.
	self assert: (f primitive * g primitive) isPrimitive
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testHeight [
	| x |
	x := QQ polynomials x.
	self assert: (x * 2 - 5) height =  5.
	self assert: (x * 5 - 2) height =  5
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testIntegerFactorization [
	| x f factors |
	x := ZZ polynomials x.
	'f := (x*2-1)^2*(x-2)*(x^2 + 1)*(x^2-2)*18'.
	factors := f factors.
	self assert: factors size = 8.
	self assert: factors asSet size = 6.
	self assert: factors product = f
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testInterpolation [
	| Qx f |
	Qx := QQ polynomials.
	f := Qx interpolate: {1 -> 2. 2 -> 3. 4 -> 5}.
	self assert: (f value: 1) = 2.
	self assert: (f value: 2) = 3.
	self assert: (f value: 4) = 5
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testInterpolation2 [
	| Qx f |
	Qx := QQ polynomials.
	f := Qx interpolate: {1 -> 2. 2 -> 4. 3 -> 9}.
	self assert: (f value: 1) = 2.
	self assert: (f value: 2) = 4.
	self assert: (f value: 3) = 9
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testIsIrreducible [
	"The polynomial x^4 + 1 is irreducible in Z[x] and Q[x], and it is reducible Z/p[x] for all prime numbers p."
	| p |
	'self assert: (ZZ polynomials ! [:x| x^4 + 1] :: isIrreducible).
		self assert: (QQ polynomials ! [:x| x^4 + 1] :: isIrreducible)'.
	p := 1000 atRandom nextPrime.
	'self deny: (ZZ/p :: polynomials ! [:x| x^4 + 1] :: isIrreducible)'
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testIsIrreducibleOverQ [
	| x f |
	x := QQ polynomials x.
	f := 'x^4 + 1'.
	self assert: f isIrreducible.
	self assert: f negated isIrreducible.
	self assert: (f*2) isIrreducible.
	self assert: (f*(x+1)) isIrreducible not
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testIsIrreducibleOverZ [
	| x f |
	x := ZZ polynomials x.
	f := 'x^4 + 1'.
	self assert: f isIrreducible.
	self assert: f negated isIrreducible.
	self assert: (f*2) isIrreducible not.
	self assert: (f*(x+1)) isIrreducible not.

]

{ #category : #'as yet unclassified' }
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

{ #category : #'as yet unclassified' }
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

{ #category : #'as yet unclassified' }
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

{ #category : #'as yet unclassified' }
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

{ #category : #'as yet unclassified' }
PolynomialTest >> testMultivariateGCDBug [
	| x |
	x := 'QQ polynomialsIn: 3 :: x'.
	self assert: '(x^2 gcd: x)' = x
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testPPRS [
	"Example from Zippel."
	| a b pprs |
	a := ZZ polynomials coefficients: #(1 0 1 0 -3 -3 8 2 -5) reversed.
	b := ZZ polynomials coefficients: #(3 0 5 0 -4 -9 21) reversed.
	pprs := 'a pprs: b :: collect: [:each| each coefficients reversed asArray] :: asArray'.
	self assert: pprs = #((1 0 1 0 -3 -3 8 2 -5) 
		(3 0 5 0 -4 -9 21)
		(-5 0 1 0 -3)
		(13 25 -49)
		(4663 -6150)
		(1))
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testPseudoDivision1 [
	| Zxy x y division |
	Zxy := ZZ polynomialsIn: #(x y).
	x := Zxy x.
	y := Zxy y.
	'division := x^2 + (y^2) pseudoDivisionBy: y - x in: 2.
		self assert: division quotient asMultivariate = (x + y).
		self assert: division remainder asMultivariate = (x^2 * 2)'.
	self assert: division verify
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testPseudoDivision2 [
	| Zxy x y division |
	Zxy := QQ polynomialsIn: #(x y).
	x := Zxy x.
	y := Zxy y.
	'division := x^2 + (y^2) pseudoDivisionBy: (y-x)*2 in: 2.
		self assert: division quotient asMultivariate = ((x+y) * 2).
		self assert: division remainder asMultivariate = (x^2 * 8)'.
	self assert: division verify
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testPseudoDivision3 [
	| Zxy x y division |
	Zxy := ZZ polynomialsIn: #(x y).
	x := Zxy x.
	y := Zxy y.
	'division := x^2 + (y^2) pseudoDivisionBy: y - x in: 2.
		self assert: division quotient asMultivariate = (x + y).
		self assert: division remainder asMultivariate = (x^2 * 2)'.
	self assert: division verify.

'	division := x^2 + (y^2) pseudoDivisionBy: x - y in: 2.
	self assert: division quotient asMultivariate = (x + y) negated.
	self assert: division remainder asMultivariate = (x^2 * 2)'.
	self assert: division verify
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testPseudoDivision: R [
	| Rx f g div |
	Rx := R polynomials.
	f := Rx atRandomBits: 100 maxDegree: 10 atRandom.
	[g := Rx atRandomBits: 100 maxDegree: 10 atRandom. g isZero] whileTrue.
	div := f pseudoDivisionBy: g.
	self assert: div verify
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testPseudoDivisionUnivariate [
	| Zx x division |
	Zx := ZZ polynomials.
	x := Zx x.
'	division := x^3 + x + 1 pseudoDivisionBy: (x^2 * 3) + x + 1'.
	self assert: division quotient = (x*3 - 1).
	self assert: division remainder = (x*7 + 10).
	self assert: division delta = 2.
	self assert: division verify
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testPseudoDivisionUnivariate2 [
	"Example from Zippel book"
	| Zx a b |
	Zx := ZZ polynomials.
	a := Zx coefficients: #(1 0 1 0 -3 -3 8 2 -5) reversed.
	b := Zx coefficients: #(3 0 5 0 -4 -9 21) reversed.
	^ self assert: (a pseudoDivisionBy: b) verify
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testPseudoDivisionZ [
	self testPseudoDivision: ZZ
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testPseudoDivisionZ6 [
	self testPseudoDivision: ZZ / 6
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testPseudoRemainder [
	| Zx x a b r |
	Zx := ZZ polynomials.
	x := Zx x.
'	a := x^8 + (x^6) - (3*(x^4)) - (3*(x^3)) + (8*(x^2)) + (2*x) - 5.
	b := 3*(x^6) + (5*(x^4)) - (4*(x^2)) - (9*x) + 21'.
	r := Zx coefficients: #(-9 0 3 0 -15).
	self assert: (a pseudoRem: b) = r.
	self assert: (a pseudoDivisionBy: b) remainder = r
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testQuotientRingBug [
	"This is fixed by making ideals of Z[x] have generators with positive leading coefficient. But it could be still a problem for polynomials over other rings."
	| R f Q pi a b |
	R := ZZ polynomials.
	'f := R ! [:x| x^2*-1 - 1]'.
	Q := R/f.
	pi := Q projection.
	a := R x - 1.
	b := 'R x^2 + 1'.
	self assert: (pi value: a) + (pi value: b) = (pi value: a+b)
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testRationalFactorization [
	| x f factors |
	x := QQ polynomials x.
	f := '(x-(1/2))^2*(x-2)*(x^2 + 1)*(x^2-2)'.
	factors := f factors.
	self assert: factors size = 5.
	self assert: factors asSet size = 4.
	self assert: factors product monic = f monic "up to a unit"
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testRationalRoots [
	| x f roots |
	x := QQ polynomials x.
	f := '(x-(1/2))^2*(x-2)*(x^2 + 1)*(x^2-2)'.
	roots := f allRoots.
	self assert: roots size = 3.
	self assert: (roots occurrencesOf: 1/2) = 2.
	self assert: (roots occurrencesOf: 2) = 1
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testRationalRootsBug [
	| x f roots |
	x := QQ polynomials x.
	f := 'x^3*-1 + (3*x) + 2'.
	roots := f allRoots.
	self assert: roots size = 3.
	self assert: (roots occurrencesOf: -1) = 2.
	self assert: (roots occurrencesOf: 2) = 1
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testRealRoots [
	| x f roots |
	x := QQ polynomials x.
	f := '(x-(1/2))^2*(x-2)*(x^2 + 1)*(x^2-2)'.
	roots := f allRootsIn: RR.
	self assert: roots size = 5.
	self assert: roots asSet size = 4.
	self assert: (roots occurrencesOf: 1/2) = 2.
	self assert: (roots occurrencesOf: 2) = 1
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testRemainderInconsistency [
	"In Sage these two give the same result."
	| X x |
	X := ZZ polynomials x.
	x := QQ polynomials x.
	self assert: (x \\ (1 - x)) leadingCoefficient = (X \\ (1 - X)) leadingCoefficient
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testResultant [
	| Zx x f g f2 g2 h |
	Zx := ZZ polynomials.
	x := Zx x.
	'f := x^2 + x + 1.
		f2 := f * (x + 2).
		g := x^3 + 1.
		g2 := g * (x + 2).
		h := x^4 + 1'.
	self assert: (f resultant: g) isZero not. "not 0 because f and g have no common roots"
	self assert: (f2 resultant: g2) isZero. "res(f2,g2) = 0 because f2 and g2 have a common root -2."
	self assert: '(-1)^(f degree * g degree) * (f resultant: g) = (g resultant: f)'.
	self assert: (f * g resultant: h) = ((f resultant: h) * (g resultant: h))
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testResultant2 [
	| Zx x f g |
	Zx := ZZ polynomials.
	x := Zx x.
	f := 2 * (x - 5) * (x - 11).
	g := 3 * (x - 7).
	self assert: (f resultant: g) = '((2 ^ 1) * (3^2) * (5 - 7) * (11 - 7))'
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testSPRS [
	"Example from Zippel."
	| a b sprs |
	a := ZZ polynomials coefficients: #(1 0 1 0 -3 -3 8 2 -5) reversed.
	b := ZZ polynomials coefficients: #(3 0 5 0 -4 -9 21) reversed.
	'sprs := a sprs: b :: collect: [:each| each coefficients reversed asArray] :: asArray'.
	self assert: sprs = #((1 0 1 0 -3 -3 8 2 -5)
		#(3 0 5 0 -4 -9 21)
		#(15 0 -3 0 9)
		#(65 125 -245)
		#(9326 -12300)
		#(260708))

]

{ #category : #'as yet unclassified' }
PolynomialTest >> testShift [
	| Zx x f |
	Zx := ZZ polynomials.
	x := Zx x.
	f := Zx atRandomBits: 10.
	self assert: (f shift: 10) degree = (f degree + 10).
	self assert: ((f shift: 10) shift: -10) = f.
	'self assert: f * (x^3) = (f shift: 3).
		self assert: (f * (x^3) shift: -3) = f'
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testSquareFree [
	| P x f1 f2 f3 f |
	P := QQ polynomials.
	x := P x.
'	f1 := x^2 + x + 1'.
	f2 := 1 - x.
	f3 := x - 2.
	f := f1*f1*f2*f3*f3*f3.
	self assert: f squareFree = (f1 * f2 * f3)
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testSquareFreeMultivariate [
	| P x y f1 f2 f |
	P := QQ polynomialsIn: #(x y).
	x := P x.
	y := P y.
	f1 := x + 1.
	f2 := y + 1.
	f := f1*f1*f2*f2.
	self assert: f squareFree = (f1 * f2)
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testSubresultant [
	"deg(gcd(f,g)) = d iff subresultant(f,g,k) = 0 for all k < d and subresultant(f,g,d) ~= 0, and the d-th subresultant coefficient is in fact a gcd of f and g."
	| x f g |
	x := ZZ polynomials x.
	'f := (x^4 - 1)*6.
		g := (x^6 - 1)*9'.
	"self assert: (f gcd: g) = ((x^2 - 1)*3)"
	self assert: (f subresultant: 0 with: g) isZero.
	self assert: (f subresultant: 1 with: g) isZero.
	self assert: (f subresultant: 2 with: g) isZero not.
	self assert: (f subresultant: 2 with: g) primitive = ((x raiseTo: 2) - 1)
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testSubresultant0 [
	| Zx x f g |
	Zx := ZZ polynomials.
	x := Zx x.
	f := 2 * (x - 5) * (x - 11).
	g := 3 * (x - 7).
	self assert: (f resultant: g) = (f subresultant: 0 with: g) asScalar
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testUnivariateMultivariateConversion [
	| Qx x y f |
	Qx := QQ polynomialsIn: #(x y).
	x := Qx x.
	y := Qx y.
	'f := x^2*y'.
	self assert: f asUnivariate asMultivariate = f.
"	self assert: (f asUnivariateIn: 1 :: asMultivariate) = f."
	'self assert: (f asUnivariateIn: 2 :: asMultivariate) = f'
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testUnivariateMultivariateConversion2 [
	| Qx x y f f2 x0 y0 |
	Qx := QQ polynomialsIn: #(x y).
	x := Qx x.
	y := Qx y.
	f := Qx zero.
	'10 timesRepeat: [f := f + (10 atRandom - 5 * (x ^ (3 atRandom - 1) * (y ^ (3 atRandom - 1))))]'.
	f2 := f asUnivariate.
	self assert: f2 asMultivariate = f.
	x0 := (-100 to: 100) atRandom.
	y0 := (-100 to: 100) atRandom.
	self assert: ((f2 value: y0) value: x0) = (f value: {x0. y0})
]

{ #category : #'as yet unclassified' }
PolynomialTest >> testZeroCoefficientBug [
	| Qx |
	Qx := QQ polynomials.
	self assert: (Qx one * 0) isZero
]
