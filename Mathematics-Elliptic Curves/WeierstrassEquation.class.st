"
Weierstrass equations are equations of the form
	y^2 + a1 xy + a3 y = x^3 + a2 x^2 + a4 x + a0
with coefficients (a1,a2,a3,a4,a6) in some field.

When the discriminant is not zero, they define an elliptic curve. See EllipticCurve.
"
Class {
	#name : #WeierstrassEquation,
	#superclass : #Object,
	#instVars : [
		'coefficients'
	],
	#category : #'Mathematics-Elliptic Curves'
}

{ #category : #'instance creation' }
WeierstrassEquation class >> coefficients: aTuple [
	^ self new coefficients: aTuple
]

{ #category : #invariants }
WeierstrassEquation >> a1 [
	^ coefficients at: 1
]

{ #category : #invariants }
WeierstrassEquation >> a2 [
	^ coefficients at: 2
]

{ #category : #invariants }
WeierstrassEquation >> a3 [
	^ coefficients at: 3
]

{ #category : #invariants }
WeierstrassEquation >> a4 [
	^ coefficients at: 4
]

{ #category : #invariants }
WeierstrassEquation >> a6 [
	^ coefficients at: 5
]

{ #category : #invariants }
WeierstrassEquation >> b2 [
	^ self a1 squared + (self a2 * 4) "NOTE: this is wrong in Silverman 'The Arithmetic Of Elliptic Curves'"
]

{ #category : #invariants }
WeierstrassEquation >> b4 [
	^ self a4 * 2 + (self a1 * self a3)
]

{ #category : #invariants }
WeierstrassEquation >> b6 [
	^ self a3 squared + (self a6 * 4)
]

{ #category : #invariants }
WeierstrassEquation >> b8 [
	^ self a1 squared * self a6 + (self a2 * self a6 * 4) - (self a1 * self a3 * self a4) + (self a2 * self a3 squared) - self a4 squared
]

{ #category : #invariants }
WeierstrassEquation >> c4 [
	^ self b2 squared - (self b4 * 24)
]

{ #category : #invariants }
WeierstrassEquation >> c6 [
	^ ((self b2) raiseTo: 3) negated + (self b2 * self b4 * 36) - (self b6 * 216)
]

{ #category : #'accessing-private' }
WeierstrassEquation >> coefficients: aTuple [
	coefficients := aTuple
]

{ #category : #accessing }
WeierstrassEquation >> curve [
	^ EllipticCurve equation: self
]

{ #category : #invariants }
WeierstrassEquation >> discriminant [
	^ '(self b2 squared * self b8) negated - (self b4 ^ 3 * 8) - (self b6 squared * 27) + (self b2 * self b4 * self b6 * 9)'
]

{ #category : #accessing }
WeierstrassEquation >> homogeneousPolynomial [
	^ (self scalars polynomialsIn: #(x y z)) ! self polynomial homogenizedIn: 3
]

{ #category : #invariants }
WeierstrassEquation >> j [
	^ 'self c4 ^ 3 / self discriminant'
]

{ #category : #converting }
WeierstrassEquation >> over: aRing [
	^ self class coefficients: (coefficients over: aRing)
]

{ #category : #accessing }
WeierstrassEquation >> polynomial [
	^ '(self scalars polynomialsIn: #(x y)) ! [:x :y|
				y^2 + (x*y * self a1) + (y * self a3) - (x^3) - (x^2 * self a2) - (x * self a4) - self a6]'
]

{ #category : #printing }
WeierstrassEquation >> printOn: aStream [
	| P x y |
	P := self scalars polynomialsIn: #(x y) ordering: (MonomialOrdering glex: #(2 1)).
	x := P x.
	y := P y.
	'aStream print: y^2 + (x*y * self a1) + (y * self a3).
		aStream
			nextPutAll: ' = ';
			print: (x^3) + (x^2 * self a2) + (x * self a4) + self a6'
]

{ #category : #accessing }
WeierstrassEquation >> scalars [
	^ coefficients scalars
]
