Class {
	#name : #NumberFieldTest,
	#superclass : #TestCase,
	#category : #MathematicsTests
}

{ #category : #tests }
NumberFieldTest >> testCyclotomicFieldDiscriminant [
	self assert: (CyclotomicField new: 20) discriminant equals: 4000000.
	self assert: (CyclotomicField new: 18) discriminant equals: -19683
]

{ #category : #tests }
NumberFieldTest >> testMinimalPolynomial [
	"Example from 'Algebraic Number Theory: A Computational Approach' by William Stein (28 pp)."

	| x K a |
	x := QQ polynomials x.
	K := QQ extension: (x raisedTo: 2) - 2.
	a := K x.
	self assert: a minimalPolynomial equals: (x raisedTo: 2) - 2.
	self
		assert: (a / 2 + 3) minimalPolynomial
		equals: (x raisedTo: 2) - (x * 6) + (17 / 2)
]

{ #category : #tests }
NumberFieldTest >> testMinimalPolynomial2 [
	"Example from 'Algebraic Number Theory: A Computational Approach' by William Stein (29 pp)."

	| x K a alpha |
	x := QQ polynomials x.
	K := QuadraticField sqrt: 5.
	a := K x.
	self assert: a squared equals: 5.
	alpha := (1 + a) / 2.
	self assert: alpha minimalPolynomial equals: (x raisedTo: 2) - x - 1
]

{ #category : #tests }
NumberFieldTest >> testMinimalPolynomial3 [
	"Example from 'Algebraic Number Theory: A Computational Approach' by William Stein (29 pp)."

	| x alpha |
	x := QQ polynomials x.
	alpha := (1 + 5 squareRoot) / 2.
	self assert: alpha minimalPolynomial equals: (x raisedTo: 2) - x - 1
]

{ #category : #tests }
NumberFieldTest >> testNormTraceAndMinimalPolynomial [
	"Example H38E17 from Magma documentation."

	| x F a |
	x := QQ polynomials x.
	F := QQ extension: (x raisedTo: 4) - ((x raisedTo: 2) * 420) + 40000.
	a := F x / 2.
	self assert: a trace equals: 0.
	self assert: a norm equals: 2500.
	self
		assert: a minimalPolynomial
		equals: (x raisedTo: 4) - ((x raisedTo: 2) * 105) + 2500
]

{ #category : #tests }
NumberFieldTest >> testQSqrt2 [
	| E x |
	x := QQ polynomials x.
	E := QQ adjoin: RealAlgebraicNumber sqrt2.
	self assert: E x minimalPolynomial equals: E polynomial.
	self assert: E x squared minimalPolynomial equals: x - 2
]

{ #category : #tests }
NumberFieldTest >> testQSqrt2RealEmbeddings [
	| E embeddings roots |
	E := QQ adjoin: RealAlgebraicNumber sqrt2.
	embeddings := E realEmbeddings.
	roots := (E polynomial rootsIn: RR) asSet.
	self
		assert: (embeddings collect: [ :f | f value: E x ]) asSet
		equals: roots
]

{ #category : #tests }
NumberFieldTest >> testQuadraticFieldFundamentalDiscriminant [
	self assert: (QuadraticField sqrt: 102) discriminant equals: 408.
	self assert: (QuadraticField sqrt: 720) discriminant equals: 5.
	self assert: (QuadraticField sqrt: 2) discriminant equals: 8
]

{ #category : #tests }
NumberFieldTest >> testQuadraticFieldSqrt2 [
	| E x |
	E := QuadraticField sqrt: 2.
	x := QQ polynomials x.
	self assert: E x minimalPolynomial equals: E polynomial.
	self assert: E x squared minimalPolynomial equals: x - 2.
	self assert: E discriminant equals: 8
]

{ #category : #tests }
NumberFieldTest >> testQuadraticFieldSqrtMinusFive [
	| e |
	e := QuadraticField sqrt: -5.
	self assert: e x minimalPolynomial equals: e polynomial.
	self assert: e x squared equals: (e embed: -5).
	self assert: (e x raisedTo: 4) equals: (e embed: 25).
	self assert: e discriminant equals: -20
]

{ #category : #tests }
NumberFieldTest >> testSignature [
	| x F |
	x := QQ polynomials x.
	F := NumberField polynomial: (x raisedTo: 2) + 1.
	self assert: F signature equals: #(0 1).
	F := NumberField polynomial: (x raisedTo: 3) - 2.
	self assert: F signature equals: #(1 1).
	F := CyclotomicField new: 5.
	self assert: F signature equals: #(0 2).
	F := NumberField polynomial: (x raisedTo: 6) + x + 1.
	self assert: F signature equals: #(0 3).
	F := NumberField
		polynomial: (x raisedTo: 3) + (x raisedTo: 2) - (x * 5) - 1.
	self assert: F signature equals: #(3 0)
]

{ #category : #tests }
NumberFieldTest >> testTotallyImaginary [
	| x E |
	x := QQ polynomials x.
	E := NumberField polynomial: (x raisedTo: 2) + 2.
	self assert: E isImaginary.
	E := NumberField polynomial: (x raisedTo: 2) - 2.
	self assert: E isImaginary not.
	E := NumberField polynomial: (x raisedTo: 4) - 2.
	self assert: E isImaginary not
]

{ #category : #tests }
NumberFieldTest >> testTotallyReal [
	| x E |
	x := QQ polynomials x.
	E := NumberField polynomial: (x raisedTo: 2) + 2.
	self assert: E isReal not.
	E := NumberField polynomial: (x raisedTo: 2) - 2.
	self assert: E isReal.
	E := NumberField polynomial: (x raisedTo: 4) - 2.
	self assert: E isReal not
]
