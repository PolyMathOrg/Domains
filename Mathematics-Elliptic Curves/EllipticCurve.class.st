"
Elliptic curves are the projective plane curves of genus 1. They can be defined by a Weierstrass equation (see WeierstrassEquation).

Elliptic curves are abelian varieties, i.e. the sets E(K) of K-rational points are abelian groups. See EllipticCurvePoint and EllipticCurveGroup.

"
Class {
	#name : #EllipticCurve,
	#superclass : #ProjectivePlaneCurve,
	#instVars : [
		'equation'
	],
	#category : #'Mathematics-Elliptic Curves'
}

{ #category : #'instance creation' }
EllipticCurve class >> coefficients: aTuple [
	^ self equation: (WeierstrassEquation coefficients: aTuple)
]

{ #category : #examples }
EllipticCurve class >> cremona11a1 [
	"Elliptic curve 11a1, first curve in the Cremona database."
	^ EllipticCurve coefficients: (0,-1,1,-10,-20)
]

{ #category : #examples }
EllipticCurve class >> cremona11a2 [
	"Elliptic curve 11a2 from the Cremona database."
	^ EllipticCurve coefficients: (0,-1,1,-7820,-263580)
]

{ #category : #examples }
EllipticCurve class >> cremona11a3 [
	"Elliptic curve 11a3 from the Cremona database."
	^ EllipticCurve coefficients: (0,-1,1,0,0)
]

{ #category : #examples }
EllipticCurve class >> cremona37a [
	"Elliptic curve 37a from the Cremona database.
	This is the elliptic curve of rank 1 with smallest conductor."
	^ EllipticCurve coefficients: (0,0,1,-1,0)
]

{ #category : #examples }
EllipticCurve class >> cremona389a1 [
	"Elliptic curve 389a1 from the Cremona database."
	^ EllipticCurve coefficients: (0,1,1,-2,0)
]

{ #category : #'instance creation' }
EllipticCurve class >> equation: aWeierstrassEquation [
	^ self new equation: aWeierstrassEquation
]

{ #category : #examples }
EllipticCurve class >> secp256k1 [
	"Answer the SECP256K1 elliptic curve, used by Bitcoin.
	The group of this curve has order 115792089237316195423570985008687907852837564279074904382605163141518161494337."
	| F |
	F := PrimeField new: 16rFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F.
	^ self coefficients: ((0,0,0,0,7) over: F)
]

{ #category : #converting }
EllipticCurve >> % anInteger [
	"Answer the reduction of the receiver modulo anInteger."
	(self scalars isKindOf: RationalField) ifFalse: [^ DomainError signal: 'not over the rationals'].
	^ self over: ZZ % anInteger
]

{ #category : #operations }
EllipticCurve >> badPrimes [
	"Answer the set of primes for which the receiver doesn't have 'good reduction'."
	^ self discriminant factors asSet
]

{ #category : #operations }
EllipticCurve >> discriminant [
	^ self equation discriminant
]

{ #category : #private }
EllipticCurve >> divisionPolynomial0: n at: x [
	"Answer the n-th division polynomial, without the 2-torsion factor if n is even, evaluated at x."
	n = -2 ifTrue: [^ (self divisionPolynomial: -1 at: x) squared].
	'n = -1 ifTrue: [^ x^3 * 4 + (x^2 * equation b2) + (x * equation b4 * 2) + equation b6]'.
	n <= 0 ifTrue: [DomainError signal].
	(n = 1 or: [n = 2]) ifTrue: [^ x one].
	'n = 3 ifTrue: [^ x^4 + (x^3 * equation b2) + (x^2 * equation b4 * 3) + (x * equation b6 * 3) + equation b8]'.
		'n = 4 ifTrue: [^ (x^2 * 6 + (x * equation b2) + equation b4) * (self divisionPolynomial: 3 at: x) + (self divisionPolynomial: -2 at: x)]'.
	^ 'n even
			ifTrue:
				[| m |
				m := n - 2 // 2.
				(self divisionPolynomial: m+1 at: x) *
				((self divisionPolynomial: m at: x)^2 * (self divisionPolynomial: m+3 at: x) -
				((self divisionPolynomial: m+2 at: x)^2 * (self divisionPolynomial: m-1 at: x)))]
			ifFalse:
				[| m |
				m := n - 1 // 2.
				m even
					ifTrue: [(self divisionPolynomial: m at: x)^3 * (self divisionPolynomial: -2 at: x) * (self divisionPolynomial: m+2 at: x) - ((self divisionPolynomial: m+1 at: x)^3 * (self divisionPolynomial: m-1 at: x))]
					ifFalse: [(self divisionPolynomial: m at: x)^3 * (self divisionPolynomial: m+2 at: x) - ((self divisionPolynomial: m+1 at: x)^3 * (self divisionPolynomial: m-1 at: x) * (self divisionPolynomial: -2 at: x))]]'
]

{ #category : #operations }
EllipticCurve >> divisionPolynomial: n [
	"Answer the n-th division polynomial."
	^ self divisionPolynomial: n at: self scalars polynomials x
]

{ #category : #operations }
EllipticCurve >> divisionPolynomial: n at: x [
	"Answer the n-th division polynomial of the receiver evaluated at x."
	^ self notYetImplemented
]

{ #category : #operations }
EllipticCurve >> divisionPolynomialNew: n [
	"Answer the n-th division polynomial."
	| R w x y |
	R := ZZ polynomialsIn: #(x y).
	n == 1 ifTrue: [^ R one].
	w := self equation.
	x := R x.
	y := R y.
	'n == 2 ifTrue: [^ y*2 + (w a1 * x) + w a3].
		n == 3 ifTrue: [^ x^4 * 3 + (x^3 * w b2) + (x^2 * 3 * w b4) + (x * 3 * w b6) + w b8].
		n == 4 ifTrue: [^ (self divisionPolynomial: 2) * (x^6 * 2 + (x^5 * w b2) + (x^4 * w b4 * 5) + (x^3 * 10 * w b6) + (x^2 * 10 * w b8) + (x * (w b2 * w b8 - (w b4 * w b6))) + (w b4 * w b8 - w b6 squared))].'
"	n odd ifTrue: [
		m := n - 1 // 2.
		^ (self divisionPolynomial: m+2) * ((self divisionPolynomial: m) ^ 3) - (self divisionPolynomial"
]

{ #category : #operations }
EllipticCurve >> divisionPolynomials [
	"Answer the sequence of division polynomials.
	Reference: Silverman, 'The Arithmetic of Elliptic Curves', Exercise 3.7, pag. 105."
	| R x y phi1 phi2 phi3 phi4 a1 a3 b2 b4 b6 b8 |
	R := self scalars polynomialsIn: #(x y). x := R x. y := R y.
	a1 := self equation a1.
	a3 := self equation a3.
	b2 := self equation b2.
	b4 := self equation b4.
	b6 := self equation b6.
	b8 := self equation b8.
	phi1 := R one.
	phi2 := y*2 + (a1 * x) + a3.
	'phi3 := x^4 * 3 + (x^3 * b2) + (x^2 * 3 * b4) + (x * 3 * b6) + b8.
		phi4 := phi2 * (x^6 * 2 + (x^5 * b2) + (x^4 * b4 * 5) + (x^3 * 10 * b6) + (x^2 * 10 * b8) + (x * (b2 * b8 - (b4 * b6))) + (b4 * b8 - b6 squared))'.
	^ 'Sequence to: R initialValues: {phi1. phi2. phi3. phi4} recurrence: [:phi :n|
			| m |
			n odd
				ifTrue:
					[m := n - 1 // 2.
					(phi at: m+2) * ((phi at: m) ^ 3) - ((phi at: m - 1) * ((phi at: m + 1) ^ 3))]
				ifFalse:
					[m := n // 2.
					(phi at: m-1) squared * (phi at: m) * (phi at: m+2) - ((phi at: m-2) * (phi at: m) * (phi at: m+1) squared // phi2)]]'
]

{ #category : #accessing }
EllipticCurve >> equation [
	^ equation
]

{ #category : #'accessing-private' }
EllipticCurve >> equation: aWeierstrassEquation [
	equation := aWeierstrassEquation.
	self coordinateRing: aWeierstrassEquation homogeneousPolynomial asIdeal quotientRing
]

{ #category : #accessing }
EllipticCurve >> genus [
	"Answer the geometric genus of the receiver."
	^ 1
]

{ #category : #testing }
EllipticCurve >> isSmooth [
	^ self discriminant isZero not
]

{ #category : #operations }
EllipticCurve >> multiplicationBy: m [
	| F f omega phi psi x |
	psi := self divisionPolynomials.
	f := psi at: m.
	x := psi codomain x.
"	y := psi codomain y."
	F := self ambient functionField.
	phi := x * f squared - ((psi at: m+1) * (psi at: m-1)).
	omega := (psi at: m+2) * (psi at: m-1) squared - ((psi at: m-2) * (psi at: m+1) squared).
	f := f value: {F x. F y}.
	omega := (omega value: {F x. F y}) / (F y * 4).
	phi := phi value: {F x. F y}.
	^ "self from: self to: self representatives:" {phi / f squared. omega / (f raiseTo: 3). F z}
]

{ #category : #converting }
EllipticCurve >> over: aRing [
	^ self class equation: (self equation over: aRing)
]

{ #category : #points }
EllipticCurve >> pointAt: aTuple [
	aTuple size = 2 ifTrue: [^ EllipticCurvePoint on: self coordinates: (aTuple copyWith: aTuple scalars one)].
	^ EllipticCurvePoint on: self coordinates: aTuple
]

{ #category : #points }
EllipticCurve >> pointAtRandom: aRandom [
	"Answer randomly a point of the receiver. Assume the scalars are a finite field."
	| points |
	[(points := self pointsAtX: (self scalars atRandom: aRandom)) isEmpty] whileTrue.
	^ points atRandom: aRandom
]

{ #category : #points }
EllipticCurve >> pointsAtX: x [
	"Answer the points with x coordinate as given by the argument."
	| P |
	P := self scalars polynomials.
	^ (self polynomial value: {P ! x. P x. P one}) roots collect: [:y| self pointAt: (x,y)]
]

{ #category : #points }
EllipticCurve >> pointsOver: aField [
	"Answer the group of K-rational points on the receiver."
	^ EllipticCurveGroup on: self over: aField
]

{ #category : #printing }
EllipticCurve >> printOn: aStream [
	aStream "nextPutAll: 'E : ';" print: self equation
]
