Class {
	#name : #QuadraticFormTest,
	#superclass : #TestCase,
	#category : #MathematicsTests
}

{ #category : #'as yet unclassified' }
QuadraticFormTest >> newQuadraticForm [
	^ self newQuadraticForm: (2 to: 5) atRandom
]

{ #category : #'as yet unclassified' }
QuadraticFormTest >> newQuadraticForm: n [
	| V |
	V := 'QQ^n'.
	^ 'QuadraticForm from: V coefficients: (QQ^(n + 1 * n / 2) atRandomBits: 100)'
]

{ #category : #'as yet unclassified' }
QuadraticFormTest >> testArithmetic [
	| n Q1 Q2 p a |
	n := (1 to: 5) atRandom.
	Q1 := self newQuadraticForm: n.
	Q2 := self newQuadraticForm: n.
	p := Q1 domain atRandomBits: 100.
	a := QQ atRandomBits: 100.
	self assert: (Q1 value: p) + (Q2 value: p) = (Q1 + Q2 value: p).
	self assert: (Q1 * a value: p) = ((Q1 value: p) * a).
	self assert: Q1 + Q2 + Q2 negated = Q1
]

{ #category : #'as yet unclassified' }
QuadraticFormTest >> testAsPolynomial [
	| Q f p |
	Q := self newQuadraticForm.
	f := Q asPolynomial.
	p := Q domain atRandomBits: 100.
	self assert: (Q value: p) = (f value: p).
	self assert: (f degree = 2 and: [f isHomogeneous])
]

{ #category : #'as yet unclassified' }
QuadraticFormTest >> testAssociatedBilinearForm [
	"Example from Sage."
	| Q B |
	Q := QuadraticForm coefficients: ((1,4,0,1,4,1) over: ZZ).
	B := Q associatedBilinearForm.
	self assert: (B value: {(1,2,0) over: ZZ. (0,1,1) over: ZZ}) = 8
]

{ #category : #'as yet unclassified' }
QuadraticFormTest >> testAssociatedBilinearForm2 [
	"Example from Sage."
	| Q B |
	Q := QuadraticForm coefficients: (1/2, 2, 1).
	B := Q associatedBilinearForm.
	self assert: (B value: {(1,1). (1/2,2)}) = (19/4)
]

{ #category : #'as yet unclassified' }
QuadraticFormTest >> testEvaluation [
	"Example from Sage."
	| Q |
	Q := QuadraticForm from: 'QQ^3' coefficients: (0 to: 5).
	self assert: (Q value: (1,2,3)) = 89.
	self assert: (Q value: (1,0,0)) = 0.
	self assert: (Q value: (1,1,1)) = 15
]
