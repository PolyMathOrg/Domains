Class {
	#name : #EllipticCurvesTest,
	#superclass : #TestCase,
	#category : #MathematicsTests
}

{ #category : #'as yet unclassified' }
EllipticCurvesTest >> testBInvariants [
	| W |
	W := WeierstrassEquation coefficients: (1,2,3,4,5).
	self assert: W b2 = 9.
	self assert: W b4 = 11.
	self assert: W b6 = 29.
	self assert: W b8 = 35
]

{ #category : #'as yet unclassified' }
EllipticCurvesTest >> testCInvariants [
	| W |
	W := WeierstrassEquation coefficients: (0,-1,1,-10,-20).
	self assert: W c4 = 496.
	self assert: W c6 = 20008
]

{ #category : #'as yet unclassified' }
EllipticCurvesTest >> testGroupLaw [
	| E P Q O |
	E := EllipticCurve cremona389a1.
	P := E pointAt: (-1,1).
	Q := E pointAt: (0,-1).
	O := E pointAt: (0,1,0).
	self assert: P+Q = (E pointAt: (4,8)).
	self assert: P-Q = (E pointAt: (1,0)).
	self assert: 3*P - (5*Q) = (E pointAt: (328/361,(-2800/6859))).
	self assert: O+P = P.
	self assert: P+O = P.
	self assert: P-P = O
]

{ #category : #'as yet unclassified' }
EllipticCurvesTest >> testPointAtX [
	| E p |
	E := EllipticCurve secp256k1.
	p := E scalars modulus.
	10 count: [(E pointsAtX: p atRandom) allSatisfy: [:each| E satisfies: each coordinates]]
]

{ #category : #'as yet unclassified' }
EllipticCurvesTest >> testWeierstrassEquationInvariants [
	| W |
	W := WeierstrassEquation coefficients: ('ZZ ^ 5' atRandomBits: 100).
	self assert: W b8 * 4 = (W b2 * W b6 - W b4 squared).
	self assert: W discriminant * 1728 = ('W c4 ^ 3' - W c6 squared)
]
