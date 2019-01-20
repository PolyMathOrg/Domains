Class {
	#name : #MathematicsTest,
	#superclass : #TestCase,
	#category : #MathematicsTests
}

{ #category : #tests }
MathematicsTest >> testAlgebraicExtension [
	| x E a b |
	x := QQ polynomials x.
	E := QQ extension: (x raiseTo: 4) - 2.
	a := E x.
	self assert: (a raiseTo: 4) representative asScalar equals: 2.
	b := (a raiseTo: 2) + (E embed: 3).
	self assert: b minimalPolynomial equals: (x raiseTo: 2) - (x * 6) + 7
]

{ #category : #tests }
MathematicsTest >> testBitCount [
	| v |
	v := '1 << 3000 :: atRandom'.
	'self assert: (v printStringBase: 2 :: count: [:x| x = $1]) = v bitCount'
]

{ #category : #tests }
MathematicsTest >> testBitParity [
	| v |
	v := '1 << 3000 :: atRandom'.
	'self assert: ((v printStringBase: 2 :: count: [:x| x = $1]) bitAnd: 1) = v bitParity'
]

{ #category : #tests }
MathematicsTest >> testCRT [
	| crt |
	crt := CRT mod: #(2 5 7).
	self assert: (crt solve: #(0 2 0)) = 42
]

{ #category : #tests }
MathematicsTest >> testCartesianProduct [
	| P x |
	P := CartesianProduct components: {PrimeField new: 3. GaloisField new: 4. SymmetricGroup new: 5}.
	self assert: P elements size = (3*4*5 factorial).
	x := {(P at: 1) atRandom. (P at: 2) atRandom. (P at: 3) atRandom}.
	self assert: (P elements includes: x)
]

{ #category : #tests }
MathematicsTest >> testContinuedFractions [
	| x |
	x := ContinuedFraction fromFraction: 415/93.
	self assert: x coefficients = (4, 2, 6, 7).
	self assert: x asFraction = (415/93)
]

{ #category : #tests }
MathematicsTest >> testContinuedFractions2 [
	-2 to: 2 by: 1/2 do:
		[:x| self assert: (ContinuedFraction fromFraction: x) asFraction = x]
]

{ #category : #tests }
MathematicsTest >> testContinuedFractionsE [
	| x e |
	e := ContinuedFraction e.
	x := e convergentAt: 20.
	self assert: (x asFloat - 1 exp) abs < 0.0000001
]

{ #category : #tests }
MathematicsTest >> testContinuedFractionsGoldenRatio [
	| x phi |
	phi := ContinuedFraction phi.
	x := phi convergentAt: 20.
	self assert: (x asFloat - 1.6180339887) abs < 0.000001
]

{ #category : #tests }
MathematicsTest >> testContinuedFractionsGoldenRatio2 [
	| phi denominators |
	phi := ContinuedFraction phi.
	denominators := phi convergents collect: [:each| each denominator].
	self assert: (denominators equals: Sequence fibonacci << 1 upTo: 100)
]

{ #category : #tests }
MathematicsTest >> testContinuedFractionsNegated [
	| x |
	x := ContinuedFraction fromFraction: 415/93.
	self assert: x negated asFraction = (-415/93)
]

{ #category : #tests }
MathematicsTest >> testContinuedFractionsReciprocal [
	| x |
	x := ContinuedFraction fromFraction: 415/93.
	self assert: x reciprocal asFraction = (93/415)
]

{ #category : #tests }
MathematicsTest >> testCyclotomicPolynomials [
	| P |
	P := QQ polynomials.
	1 to: 20 do: [:n| self assert: (P cyclotomic: n) degree = n phi]
]

{ #category : #tests }
MathematicsTest >> testCyclotomicPolynomials2 [
	| P x n |
	P := QQ polynomials.
	x := P x.
	n := 100 atRandom.
	'self assert: (n divisors product: [:d| P cyclotomic: d]) = (x^n - 1)'
]

{ #category : #tests }
MathematicsTest >> testExtendedEuclid [
	| a b euclid |
	a := '-1000 to: 1000 :: atRandom'.
	b := '-1000 to: 1000 :: atRandom'.
	euclid := ExtendedEuclid on: {a. b}.
	self assert: euclid gcd | a.
	self assert: euclid gcd | b.
	self assert: (euclid bezout * {a. b}) sum = euclid gcd.
	self assert: euclid gcd = (a gcd: b).
	self assert: euclid verify
]

{ #category : #tests }
MathematicsTest >> testFieldAutomorphisms [
	self assert: QQ automorphisms isTrivial
]

{ #category : #tests }
MathematicsTest >> testFreeAlgebra [
	| A f g h |
	A := QQ freeAlgebraIn: #(x y z).
	f := A atRandomBits: 100.
	g := A atRandomBits: 100.
	h := A atRandomBits: 100.
	self assert: (f*g)*h = (f*(g*h)). "associativity"
	self assert: (f+g)*h = (f*h + (g*h)). "distributivity"
	self assert: f * A one = f.
	self assert: A one * f = f
]

{ #category : #tests }
MathematicsTest >> testFunctionComposition [
	| f g a |
	f := Function from: ZZ to: ZZ evaluating: [:x| x * 2].
	g := Function from: ZZ to: ZZ evaluating: [:x| x + 1].
	a := 1000 atRandom.
	'self assert: (f î g value: a) = (f value: (g value: a)).
		self assert: (g î f value: a) = (g value: (f value: a))'
]

{ #category : #tests }
MathematicsTest >> testFunctionComposition2 [
	| f g a |
	f := Function from: ZZ to: QQ evaluating: [:x| x / 2].
	g := Function from: QQ to: ZZ evaluating: [:x| x numerator].
	a := 1000 atRandom.
	'self assert: (f î g value: a) = (f value: (g value: a)).
		self assert: (g î f value: a) = (g value: (f value: a))'
]

{ #category : #tests }
MathematicsTest >> testFunctionComposition3 [
	| f g |
	f := Function from: ZZ to: QQ evaluating: [:x| x / 2].
	g := Function from: ZZ to: ZZ evaluating: [:x| x + 1].
	'self should: [g î f] raise: DomainError'
]

{ #category : #tests }
MathematicsTest >> testFunctionNewFrom [
	| f g |
	'f := QQ^3 :: endomorphisms atRandomBits: 1000'. "f is a LinearMap"
	g := f as: Function. "downgrade it to a simple Function, not a LinearMap any more"
	self assert: (g as: LinearMap) = f
]

{ #category : #tests }
MathematicsTest >> testFundamentalDiscriminant [
	self assert: ((1 to: 33) select: [:each| each isFundamentalDiscriminant]) =  #(1 5 8 12 13 17 21 24 28 29 33).
	self assert: ((0 to: -31 by: -1) select: [:each| each isFundamentalDiscriminant]) = #(-3 -4 -7 -8 -11 -15 -19 -20 -23 -24 -31) 

]

{ #category : #tests }
MathematicsTest >> testGaloisFields [
	| GF pi x one a |
	GF := GaloisField new: (3 raiseTo: 3).
	self assert: GF isField.
	self assert: GF characteristic = 3.
	pi := GF projection.
	x := pi domain x.
	one := pi domain one.
	a := 'pi value: x^2 + one'.
	self assert: a * a reciprocal = GF one.
	[(a := GF atRandom) isZero] whileTrue.
	self assert: a * a reciprocal = GF one
]

{ #category : #tests }
MathematicsTest >> testInfinity [
	self assert: Infinity positive > Infinity negative.
	self assert: Infinity positive > 127934879182734.
	self assert: Infinity negative < -198273498712341.
	self assert: Infinity positive >= 127934879182734.
	self assert: Infinity negative <= -198273498712341.
	self assert: -918723948719 > Infinity negative.
	self assert: 91872123948719 < Infinity positive
]

{ #category : #tests }
MathematicsTest >> testInfinityUndeterminates [
	self should: [Infinity positive + Infinity negative] raise: Error.
	self should: [Infinity positive * 0] raise: Error.
	self should: [Infinity positive / Infinity positive] raise: Error.
	self should: ['Infinity positive ^ 0'] raise: Error

]

{ #category : #tests }
MathematicsTest >> testIntegerDivisors [
	self assert: 12 numberOfDivisors = 6.
	self assert: 12 divisors size = 6
]

{ #category : #tests }
MathematicsTest >> testIntegerIdealsPrimePrimarySemiprime [
	self assert: (ZZ*5) isPrime.
	self assert: (ZZ*6) isPrime not.
	self assert: (ZZ*25) isPrimary.
	self assert: (ZZ*30) isPrimary not.
	self assert: (ZZ*30) isSemiprime.
	self assert: (ZZ*12) isSemiprime not
]

{ #category : #tests }
MathematicsTest >> testIteratorCovering [
	| F |
	F := ZZ / 3.
	'self assert: (F^3 upTo: 3^3) asSet size = (3^3).
		self assert: (ZZ^3 upTo: 100) asSet size = 100'
]

{ #category : #tests }
MathematicsTest >> testIteratorCovering2 [
	| F |
	F := GaloisField new: 9.
	'self assert: ((F^3) upTo: 9^3) asSet size = (9^3).
		self assert: ((F^3) upTo: 9^3+100) asSet size = (9^3)'
]

{ #category : #tests }
MathematicsTest >> testIteratorCovering3 [
	| F |
	F := GaloisField new: 3.
	'self assert: ((F^4) upTo: 3^4) asSet size = (3^4).
		self assert: ((F^4) upTo: 3^4+100) asSet size = (3^4)'
]

{ #category : #tests }
MathematicsTest >> testJacobiAndLegendreSymbols [
	| a p |
	10 timesRepeat:
		[p := (1000 atRandom + 2) nextPrime. "an odd prime"
		a := 1000 atRandom - 1.
		self assert: (a legendre: p) = (a jacobi: p)]
]

{ #category : #tests }
MathematicsTest >> testKroneckerAndLegendreSymbols [
	| a p |
	10 timesRepeat:
		[p := (1000 atRandom + 2) nextPrime. "an odd prime"
		a := 1000 atRandom - 1.
		self assert: (a legendre: p) = (a kronecker: p)]
]

{ #category : #tests }
MathematicsTest >> testKroneckerSymbol [
	| a b c |
	a := (-100 to: 100) atRandom.
	b := (-100 to: 100) atRandom.
	self assert: ((a kronecker: b) = 0) = ((a gcd: b) ~= 1).
	c := (-100 to: 100) atRandom.
	self assert: (a*b kronecker: c) = ((a kronecker: c) * (b kronecker: c)).
	b*c = 0 ifFalse: [self assert: (a kronecker: b*c) = ((a kronecker: b) * (a kronecker: c))]
]

{ #category : #tests }
MathematicsTest >> testLegendreSymbol [
	self assert: ((1 to: 10) collect: [:k| k legendre: 43]) = #(1 -1 -1 1 -1 1 -1 -1 1 1)
]

{ #category : #tests }
MathematicsTest >> testModularIntegerLift [
	'self assert: (2 to: 100 :: allSatisfy: [:m| 1 to: m :: allSatisfy: [:x| x % m :: lift % m = (x % m)]])'
]

{ #category : #tests }
MathematicsTest >> testModularIntegersField [
	| F a b |
	F := ZZ / 7.
	self assert: F isField.
	self assert: F characteristic = 7.
	a := F projection value: 3.
	b := F projection value: 5.
	self assert: a * a reciprocal = F one.
	self assert: a * 7 = F zero.
	self assert: (b raisedTo:( (F size - 1))) = F one	"Euler's theorem"
]

{ #category : #tests }
MathematicsTest >> testPartitions [
	self assert: 42 partitions size =  53174
]

{ #category : #tests }
MathematicsTest >> testPermutationProduct [
	| G a b |
	G := SymmetricGroup new: 5.
	a := G ! #((1 4 5) (2 3)).
	b := G ! #((2 4) (5 1)).
	self assert: b*a = (G ! #((1 2 3 4))).
	self assert: a*a = (G ! #((1 5 4)))
]

{ #category : #tests }
MathematicsTest >> testPermutationProduct2 [
	| G a b |
	G := SymmetricGroup new: 5.
	a := G ! #((1 4 5) (2 3)).
	b := G ! #((2 4) (5 1)).
	self assert: b*a = (G ! #((1 2 3 4))).
	self assert: a*a = (G ! #((1 5 4)))
]

{ #category : #tests }
MathematicsTest >> testPermutationProduct3 [
	| G a b |
	G := SymmetricGroup new: 4.
	a := G ! #((2 3 4)).
	b := G ! #((1 2) (3 4)).
	self assert: b*a = (G ! #((1 2 4))).
	self assert: a*b = (G ! #((1 3 2)))
]

{ #category : #tests }
MathematicsTest >> testPolynomialVectorSpace [
	| Qx V S x |
	Qx := QQ polynomials.
	x := Qx x.
	V := Qx filtrationAt: 5.
	'S := V span: {Qx one. x^2. x*2}.
		self assert: (S includes: x^2 + 2).
		self deny: (S includes: x^3 + 2).
		self assert: (S orthogonalProjection value: x^3 - (x^2) + (x*2) + 3) = ((x^2) negated + (x*2) + 3)'
]

{ #category : #tests }
MathematicsTest >> testPrimeSignature [
	self assert: 1 primeSignature = #().
	self assert: 7 primeSignature = #(1).
	self assert: (7*5) primeSignature = #(1 1).
	self assert: 12 primeSignature = #(2 1).
	self assert: 100 primeSignature = #(2 2).
	self assert: 42 primeSignature = #(1 1 1).
	self assert: 16 primeSignature = #(4)
]

{ #category : #tests }
MathematicsTest >> testQuadraticResiduesModp [
	| F |
	F := PrimeField new: 1000 atRandom nextPrime.
	self assert: F atRandom squared isQuadraticResidue.
	self assert: ((1000 count: [F atRandom isQuadraticResidue]) between: 400 and: 600)
]

{ #category : #tests }
MathematicsTest >> testRadicalAndIsSquareFree [
	| n |
	n := (-1000 to: 1000) atRandom.
	self assert: n isSquareFree = (n radical = n)
]

{ #category : #tests }
MathematicsTest >> testRealIntervalIntersects [
	| I J |
	I := RealInterval open: -1 closed: 0.
	J := RealInterval open: 0 closed: 1.
	self assert: (I intersects: J) not.
	J := RealInterval closed: 0 open: 1.
	self assert: (I intersects: J).
	J := RealInterval closed: -2 closed: -1.
	self assert: (I intersects: J) not
]

{ #category : #tests }
MathematicsTest >> testSmallPrimeField [
	| p F E |
	p := 20 atRandom nextPrime.
	F := ZZ/p.
	E := SmallPrimeField new: p.
	F do: [:a|
		F do: [:b| | c d |
			c := E ! a representative.
			d := E ! b representative.
			self assert: (a+b) representative = (c+d) representative.
			self assert: (a-b) representative = (c-d) representative.
			self assert: (a*b) representative = (c*d) representative.
			b isZero ifFalse:
				[self assert: (a/b) representative = (c/d) representative.
				self assert: b reciprocal representative = d reciprocal representative]]]
]

{ #category : #tests }
MathematicsTest >> testSmallPrimeFieldTables [
	| p F g |
	p := 20 atRandom nextPrime.
	F := SmallPrimeField new: p.
	g := F primitiveRoot.
	1 to: p-1 do: [:n| self assert: (F expTable at: n) = (g raiseTo: n) representative].
	0 to: p-2 do: [:n| self assert: (F logTable at: (g raiseTo: n) representative) = n]
]

{ #category : #tests }
MathematicsTest >> testSquareRootModp [
	| F a |
	100 timesRepeat:
		[F := PrimeField new: (1000 atRandom + 1) nextPrime.
		a := F atRandom.
		a := a squared.
		self assert: a squareRoot * a squareRoot = a]
]

{ #category : #tests }
MathematicsTest >> testWord [
	| x y |
	x := Word x: #x.
	y := Word x: #y.
	self assert: (x*y) * y reciprocal = x.
	self assert: (x*y * (y reciprocal * x reciprocal)) isEmpty.
	self assert: x*y*y * (y reciprocal * y reciprocal * x) = (x raiseTo: 2).
	self assert: x * (y * y * x) = (x * y * (y * x)).
	self assert: (x*y * (x*y) reciprocal) isEmpty
]

{ #category : #tests }
MathematicsTest >> testWordOrdering [
	| F p q r |
	F := FreeMonoid new: 3.
	p := F atRandomBits: 20 atRandom.
	r := F atRandomBits: 20 atRandom.
	[p < (q := F atRandomBits: 20 atRandom)] whileFalse.
	self assert: p*r <= (q*r).
	self assert: r*p <= (r*q).
	p := q * r.
	self assert: (p > q or: [p = q and: [r isEmpty]]).
	self assert: (p > r or: [p = r and: [q isEmpty]])
]

{ #category : #tests }
MathematicsTest >> testYoungTableauxSemistandard [
	| T |
	T := YoungTableau rows: #((1 1 2 2 3) (2 3 4 4) (4) (5)).
	self assert: T isSemistandard.
	self assert: T shape = #(5 4 1 1)
]

{ #category : #tests }
MathematicsTest >> testYoungTableauxStandard [
	| T |
	T := YoungTableau rows: #((1 4 6 8) (2 5 7) (3)).
	self assert: T isStandard.
	self assert: T weight = #(1 1 1 1 1 1 1 1).
	self assert: T shape = #(4 3 1)
]

{ #category : #tests }
MathematicsTest >> testZ6IsNotPID [
	self assert: (ZZ/6) isPID not
]
