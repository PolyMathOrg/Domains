Class {
	#name : #EllipticCurvesTest,
	#superclass : #TestCase,
	#category : #MathematicsTests
}

{ #category : #accessing }
EllipticCurvesTest >> testBInvariants [
	| W |
	W := WeierstrassEquation coefficients: 1 , 2 , 3 , 4 , 5.
	self assert: W b2 equals: 9.
	self assert: W b4 equals: 11.
	self assert: W b6 equals: 29.
	self assert: W b8 equals: 35
]

{ #category : #accessing }
EllipticCurvesTest >> testCInvariants [
	| W |
	W := WeierstrassEquation coefficients: 0 , -1 , 1 , -10 , -20.
	self assert: W c4 equals: 496.
	self assert: W c6 equals: 20008
]

{ #category : #accessing }
EllipticCurvesTest >> testGroupLaw [
	| E P Q O |
	E := EllipticCurve cremona389a1.
	P := E pointAt: -1 , 1.
	Q := E pointAt: 0 , -1.
	O := E pointAt: 0 , 1 , 0.
	self assert: P + Q equals: (E pointAt: 4 , 8).
	self assert: P - Q equals: (E pointAt: 1 , 0).
	self
		assert: 3 * P - (5 * Q)
		equals: (E pointAt: 328 / 361 , (-2800 / 6859)).
	self assert: O + P equals: P.
	self assert: P + O equals: P.
	self assert: P - P equals: O
]

{ #category : #'as yet unclassified' }
EllipticCurvesTest >> testPointAtX [
	| E p |
	E := EllipticCurve secp256k1.
	p := E scalars modulus.
	10
		count: [ (E pointsAtX: p atRandom)
				allSatisfy: [ :each | E satisfies: each coordinates ] ]
]

{ #category : #accessing }
EllipticCurvesTest >> testWeierstrassEquationInvariants [
	| W |
	W := WeierstrassEquation
		coefficients: ((ZZ raisedTo: 5) atRandomBits: 100).
	self assert: W b8 * 4 equals: W b2 * W b6 - W b4 squared.
	self
		assert: W discriminant * 1728
		equals: (W c4 raisedTo: 3) - W c6 squared
]
