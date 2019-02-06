Class {
	#name : #RingTest,
	#superclass : #TestCase,
	#category : #MathematicsTests
}

{ #category : #private }
RingTest >> newQuotientRing [
	| R I |
	2 atRandom = 1 ifTrue: [^ ZZ / (2 to: 10) atRandom].
	R := ZZ polynomials.
	I := R * (R atRandomBits: 10 maxDegree: 5).
	^ R / I
]

{ #category : #private }
RingTest >> newRing [
	4 atRandom = 1 ifTrue: [^ self newQuotientRing].
	2 atRandom = 1 ifTrue: [^ {ZZ. QQ. ZZ / (2 to: 10) atRandom} atRandom polynomialsIn: (1 to: 3) atRandom].
	^ {ZZ. QQ. ZZ / (2 to: 10) atRandom} atRandom
]

{ #category : #general }
RingTest >> testCanonicalMorphisms [
	| R x Q |
	R := QQ polynomials.
	x := R x.
	Q := R / ((x raisedTo: 2) + 1).
	'self assert: (ZZ  R value: 4) = (R embed: 4)'.	"canonical morphism from initial object"
	'self assert: (R  Q value: x^2 + 2) = Q one'	"canonical morphism to quotient object"
]

{ #category : #'finite rings' }
RingTest >> testFiniteRing [
	| R |
	R := (ZZ / 2) polynomials.
	R := R / ((R x raisedTo: 3) - R x).
	self assert: R isField not.
	self assert: R size equals: 8.
	self assert: R units size equals: 2.
	self assert: R zeroDivisors size equals: 6
	"also, this ring has two maximal ideals, and the Jacobson radical is {0, x^2 + x}"
]

{ #category : #'finite rings' }
RingTest >> testFiniteRing2 [
	| R |
	R := (ZZ / 2) polynomials.
	R := R / (R x * (R x + 1)).
	self assert: R isField not.
	self assert: R size equals: 4.
	self assert: R zeroDivisors size equals: 3.
	self assert: R characteristic equals: 2.
	self assert: R isLocal not
	"more about this ring: two maximal (and princial as well) ideals (so not a local ring)"
]

{ #category : #'finite rings' }
RingTest >> testFiniteRing2Alternative [
	| R |
	R := 'ZZ/2 ◊ (ZZ/2)'.
	self assert: R isField not.
	self assert: R size = 4.
	self assert: R zeroDivisors size = 3.
	self assert: R characteristic = 2.
	self assert: R isLocal not.
	"more about this ring: two maximal (and principal as well) ideals (so not a local ring)"
]

{ #category : #'finite rings' }
RingTest >> testFiniteRing3 [
	| R |
	R := 'ZZ/4 ◊ (ZZ/4)'.
	self assert: R characteristic equals: 4.
	self assert: R isField not.
	self assert: R size equals: 16.
	self assert: R zeroDivisors size equals: 12.
	self assert: R units size equals: 4
	"more about this ring: two maximal ideals (so not a local ring), and non-trivial jacobson radical"
]

{ #category : #'finite rings' }
RingTest >> testFiniteRing4 [
	| R S |
	R := ZZ / 6.	"this is not a Galois ring, the zero-divisors dont form an ideal"
	S := ZZ / 8.	"this is a Galois ring"
	self assert: R isLocal not.
	self assert: S isLocal
]

{ #category : #'finite rings' }
RingTest >> testGaloisRing [
	| R |
	R := GaloisRing new: 3 to: 3 to: 2.
	self assert: R characteristic equals: (3 raisedTo: 3).
	self assert: R size equals: ((3 raisedTo: 3) raisedTo: 2).
	self assert: R isLocal.
	self assert: R isEuclidean.
	self testRing: R
]

{ #category : #'finite rings' }
RingTest >> testGaloisRingCanonicalEmbeddingIntoOverring [
	"Canonical homomorphism from GR(p^n,m) to GR(p^n,m*k)."
	| p n m k A B phi |
	p := #(2 3 5) atRandom.
	n := 3 atRandom.
	m := 3 atRandom.
	k := 3 atRandom.
	A := GaloisRing new: p to: n to: m.
	B := GaloisRing new: p to: n to: m * k.
	phi := 'A  B'.
	self testRingHomomorphism: phi
]

{ #category : #'finite rings' }
RingTest >> testGaloisRingCanonicalHomomorphismToPrimeSubfield [
	"Canonical homomorphism from GR(p^n,m) to Z/<p>."
	| p n m A B phi |
	p := #(2 3 5) atRandom.
	n := 3 atRandom.
	m := 3 atRandom.
	A := GaloisRing new: p to: n to: m.
	B := ZZ/p.
	phi := 'A  B'.
	self testRingHomomorphism: phi
]

{ #category : #'finite rings' }
RingTest >> testGaloisRingCanonicalProjectionOntoResidueField [
	"Canonical homomorphism from GR(p^n,m) to GF(p,m)."
	| p n m A B phi |
	p := #(2 3 5) atRandom.
	n := 3 atRandom.
	m := 3 atRandom.
	A := GaloisRing new: p to: n to: m.
	B := GaloisField new: p to: m.
	phi := 'A  B'.
	self testRingHomomorphism: phi
]

{ #category : #'finite rings' }
RingTest >> testGaloisRingNilradical [
	| R |
	R := GaloisRing new: 3 to: 3 to: 2.
	self assert: R nilradical = (R * 3)
]

{ #category : #general }
RingTest >> testKrullDimension [
	| R I |
	self assert: ZZ dimension equals: 1.
	self assert: QQ dimension equals: 0.
	self assert: (ZZ polynomialsIn: 2) dimension equals: 3.
	R := QQ polynomialsIn: #(x y).
	I := R * {((R x raisedTo: 2) + (R y raisedTo: 2) - 1)}.
	self assert: (R / I) dimension equals: 1
]

{ #category : #localizations }
RingTest >> testLocalizationInclusions [
	| Z2 Z3 Z6 |
	Z2 := ZZ localizationAt: 2.
	Z3 := ZZ localizationAt: 3.
	Z6 := ZZ localizationAt: 6.
	self assert: Z6 >= Z2.
	self assert: Z6 >= Z3.
	self deny: Z3 >= Z2.
	self deny: Z2 >= Z3.
	self deny: Z2 >= Z6
]

{ #category : #localizations }
RingTest >> testLocalizationMaximalIdeal [
	| Z2 |
	Z2 := ZZ localizationAt: 2.
	self assert: Z2 maximalIdeal = (Z2 * 2)
]

{ #category : #localizations }
RingTest >> testLocalizationOfZAt2 [
	| L |
	L := ZZ localizationAt: 2.
	self assert: (L includes: 1/3).
	self assert: (L includes: 3/2) not.
	self assert: (L includes: 2).
	self assert: (L includes: 3).
	self assert: (L atRandomBits: 10) denominator odd.
	self testRing: L.
	self testRingHomomorphism: L embedding
]

{ #category : #general }
RingTest >> testMatrixRing [
	self testRing: (ZZ raisedTo: (5@5)) asRing
]

{ #category : #'finite rings' }
RingTest >> testModularIntegers [
	| Zm |
	Zm := ZZ / (10 atRandom + 1).
	self testRing: Zm.
	self testRingHomomorphism: Zm projection
]

{ #category : #polynomials }
RingTest >> testMultivariatePolynomialRing [
	| R |
	R := ZZ polynomialsIn: #(x y z).
	self testRing: R.
	self testRingHomomorphism: R embedding
]

{ #category : #general }
RingTest >> testNilradical [
	self assert: ZZ nilradical equals: ZZ * 0.
	self assert: (ZZ / 12) nilradical equals: ZZ / 12 * 6
]

{ #category : #polynomials }
RingTest >> testPolynomialRing [
	| R |
	R := ZZ polynomials.
	self testRing: R.
	self testRingHomomorphism: R embedding
]

{ #category : #polynomials }
RingTest >> testPolynomialRingPrimeNotMaximalIdeal [
	"Z[x]/<x> is isomorphic to Z, which is an integral domain but not a field. So <x> is prime but not maximal."
	| R I |
	R := ZZ polynomials.
	I := R * R x.
	self assert: I isPrime.
	self assert: I isMaximal not
]

{ #category : #polynomials }
RingTest >> testPolynomialRingPrimeNotMaximalIdeal2 [
	"Q[x,y]/<x> is isomorphic to Q[y], which is an integral domain but not a field. So <x> is prime but not maximal."
	| R I |
	R := QQ polynomialsIn: 2.
	I := R * R x.
	self assert: I isPrime.
	self assert: I isMaximal not
]

{ #category : #'finite rings' }
RingTest >> testPrimeFieldLogarithm [
	| F g a b p |
	p := 17.
	F := ZZ/p.
	g := F primitiveRoot.
	[(a := F atRandom) isZero] whileTrue.
	[(b := F atRandom) isZero] whileTrue.
	'self assert: g ^ (a log: g) = a'.
	self assert: (a log: g) + (b log: g) \\ (p-1) = ((a*b log: g) \\ (p-1)).
	self assert: (a log: g) - (b log: g) \\ (p-1) = ((a/b log: g) \\ (p-1))
]

{ #category : #'finite rings' }
RingTest >> testPrimeFieldPrimitiveRoot [
	| p F g i x |
	p := 100 atRandom nextPrime.
	F := ZZ/p.
	g := F primitiveRoot.
	self assert: g multiplicativeOrder = (p-1).
	i := 1.
	x := g.
	[x = F one] whileFalse: [x := x*g. i := i+1].
	self assert: i = (p-1)
]

{ #category : #'finite rings' }
RingTest >> testPrimeRing [
	| R |
	R := PrimeRing new: 3 to: 3.
	self assert: R characteristic = (3 raiseTo: 3).
	self assert: R size = (3 raiseTo: 3).
	self assert: R isLocal.
	self assert: R isEuclidean.
	self assert: R maximalIdeal = (R*3).
	self testRing: R
]

{ #category : #'finite rings' }
RingTest >> testPrimeRingCanonicalProjections [
	"Canonical homomorphism from ZZ/<p^n> to ZZ/<p^m> with 1 <= m <= n."
	| p n m A B phi a b |
	p := 100 atRandom nextPrime.
	n := 4 atRandom.
	'A := ZZ/(p^n).
		m := n atRandom.
		B := ZZ/(p^m).
		phi := A  B'.
	a := A atRandom.
	b := phi value: a.
	self assert: (B includes: b).
	self assert: a representative \\ (p raiseTo: m) = b representative.
	self testRingHomomorphism: phi
]

{ #category : #'finite rings' }
RingTest >> testPrimeRingNilradical [
	| R |
	R := PrimeRing new: 3 to: 3.
	self assert: R nilradical = (R * 3)
]

{ #category : #general }
RingTest >> testProductRing [
	| R S P |
	R := self newRing.
	S := self newRing.
	P := 'R ◊ S'.
	self testRing: P.
	self testRingHomomorphism: (P projection: 2 atRandom)
]

{ #category : #quotients }
RingTest >> testQuotientRing [
	| Q |
	Q := self newQuotientRing.
	self testRing: Q.
	self testRingHomomorphism: Q projection
]

{ #category : #quotients }
RingTest >> testQuotientRing2 [
	| Q pi f g |
	Q := self newQuotientRing.
	f := Q base atRandomBits: 10.
	g := Q relations atRandomBits: 10.
	pi := Q projection.
	self assert: (pi value: g) isZero.
	self assert: (Q includes: (pi value: f)).
	self testRingHomomorphism: pi.
"	self assert: (pi value: f) = (pi value: f + g)."
"	h := Q atRandomBits: 100.
	self assert: (pi value: (pi section value: h)) = h"
]

{ #category : #quotients }
RingTest >> testQuotientRingNotIntegralDomain [
	| R |
	R := QQ polynomials.
	R := R / (((R x) raisedTo: 2) - 1).
	self assert: R isField not.
	self assert: R isIntegralDomain not
]

{ #category : #quotients }
RingTest >> testQuotientRingWhichIsAField [
	| R |
	R := QQ polynomials.
	R := R / (((R x) raisedTo: 2) + (R x * 2) + 2).
	self assert: R isField
]

{ #category : #general }
RingTest >> testRing: R [
	| one zero a b c |
	one := R one.
	zero := R zero.
	a := R atRandomBits: 100.
	b := R atRandomBits: 100.
	c := R atRandomBits: 100.
	self assert: a * one = a.
	self assert: one * a = a.
	self assert: zero * a = zero.
	self assert: a * zero = zero.
	self assert: zero + a = a.
	self assert: a + zero = a.
	self assert: a + b = (b + a). "commutativity of addition"
	self assert: (a + b + c) = (a + (b + c)). "associativity of addition"
	self assert: (a * b * c) = (a * (b * c)). "associativity of multiplication"
	R isCommutative ifTrue: [self assert: a * b = (b * a)]. "commutativity of multiplication"
]

{ #category : #general }
RingTest >> testRingHomomorphism: phi [
	| R S a b |
	R := phi domain.
	S := phi codomain.
	a := R atRandomBits: 10.
	b := R atRandomBits: 10.
	self assert: (phi value: R zero) = S zero.
	self assert: (phi value: R one) = S one.
	self assert: (phi value: a + b) = ((phi value: a) + (phi value: b)).
	self assert: (phi value: a * b) = ((phi value: a) * (phi value: b)) "this sometimes fails because f and -f are not equal regular functions, for example"
]

{ #category : #general }
RingTest >> testZZ [
	self testRing: ZZ
]

{ #category : #general }
RingTest >> testZZPrimeNotMaximalIdeal [
| I |
	I := ZZ * 0.
	self assert: I isPrime.
	self assert: I isMaximal not
]
