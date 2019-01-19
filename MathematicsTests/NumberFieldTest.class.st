Class {
	#name : #NumberFieldTest,
	#superclass : #TestCase,
	#category : #MathematicsTests
}

{ #category : #'as yet unclassified' }
NumberFieldTest >> testCyclotomicFieldDiscriminant [
	self assert: (CyclotomicField new: 20) discriminant = 4000000.
	self assert: (CyclotomicField new: 18) discriminant = -19683
]

{ #category : #'as yet unclassified' }
NumberFieldTest >> testMinimalPolynomial [
	"Example from 'Algebraic Number Theory: A Computational Approach' by William Stein (28 pp)."
	| x K a |
	x := QQ polynomials x.
	'K := QQ extension: x^2 - 2.
		a := K x.
		self assert: a minimalPolynomial = (x^2 - 2).
		self assert: (a/2 + 3) minimalPolynomial = (x^2 - (x*6) + (17/2))'
]

{ #category : #'as yet unclassified' }
NumberFieldTest >> testMinimalPolynomial2 [
	"Example from 'Algebraic Number Theory: A Computational Approach' by William Stein (29 pp)."
	| x K a alpha |
	x := QQ polynomials x.
	K := QuadraticField sqrt: 5.
	a := K x.
	self assert: a squared = 5.
	alpha := (1 + a) / 2.
	'self assert: alpha minimalPolynomial = (x^2 - x - 1)'
]

{ #category : #'as yet unclassified' }
NumberFieldTest >> testMinimalPolynomial3 [
	"Example from 'Algebraic Number Theory: A Computational Approach' by William Stein (29 pp)."
	| x alpha |
	x := QQ polynomials x.
	alpha := 1 + 5 squareRoot / 2.
	'self assert: alpha minimalPolynomial = (x^2 - x - 1)'
]

{ #category : #'as yet unclassified' }
NumberFieldTest >> testNormTraceAndMinimalPolynomial [
	"Example H38E17 from Magma documentation."
	| x F a |
	x := QQ polynomials x.
	'F := QQ extension: x^4 - (x^2*420) + 40000.
		a := F x / 2.
		self assert: a trace = 0.
		self assert: a norm = 2500.
		self assert: a minimalPolynomial = (x^4 - (x^2*105) + 2500)'
]

{ #category : #'as yet unclassified' }
NumberFieldTest >> testQSqrt2 [
	| E x |
	x := QQ polynomials x.
	E := QQ adjoin: RealAlgebraicNumber sqrt2.
	self assert: E x minimalPolynomial = E polynomial.
	self assert: E x squared minimalPolynomial = (x - 2)
]

{ #category : #'as yet unclassified' }
NumberFieldTest >> testQSqrt2RealEmbeddings [
	| E embeddings roots |
	E := QQ adjoin: RealAlgebraicNumber sqrt2.
	embeddings := E realEmbeddings.
	roots := (E polynomial rootsIn: RR) asSet.
	self assert: (embeddings collect: [:f| f value: E x]) asSet = roots
]

{ #category : #'as yet unclassified' }
NumberFieldTest >> testQuadraticFieldFundamentalDiscriminant [
	self assert: (QuadraticField sqrt: 102) discriminant = 408.
	self assert: (QuadraticField sqrt: 720) discriminant = 5.
	self assert: (QuadraticField sqrt: 2) discriminant = 8
]

{ #category : #'as yet unclassified' }
NumberFieldTest >> testQuadraticFieldSqrt2 [
	| E x |
	E := QuadraticField sqrt: 2.
	x := QQ polynomials x.
	self assert: E x minimalPolynomial = E polynomial.
	self assert: E x squared minimalPolynomial = (x - 2).
	self assert: E discriminant = 8
]

{ #category : #'as yet unclassified' }
NumberFieldTest >> testQuadraticFieldSqrtMinusFive [
	| E |
	E := QuadraticField sqrt: -5.
	self assert: E x minimalPolynomial = E polynomial.
	self assert: E x squared = (E embed: -5).
'	self assert: E x ^ 4 = (E embed: 25)'.
	self assert: E discriminant = -20
]

{ #category : #'as yet unclassified' }
NumberFieldTest >> testSignature [
	| x F |
'	x := QQ polynomials x.
	F := NumberField polynomial: x^2 + 1.
	self assert: F signature = #(0 1).
	F := NumberField polynomial: x^3 - 2.
	self assert: F signature = #(1 1).
	F := CyclotomicField new: 5.
	self assert: F signature = #(0 2).
	F := NumberField polynomial: x^6 + x + 1.
	self assert: F signature = #(0 3).
	F := NumberField polynomial: x^3 + (x^2) - (x*5) - 1.
	self assert: F signature = #(3 0)'
]

{ #category : #'as yet unclassified' }
NumberFieldTest >> testTotallyImaginary [
	| x E |
'	x := QQ polynomials x.
	E := NumberField polynomial: x^2 + 2.
	self assert: E isImaginary.
	E := NumberField polynomial: x^2 - 2.
	self assert: E isImaginary not.
	E := NumberField polynomial: x^4 - 2.
	self assert: E isImaginary not'
]

{ #category : #'as yet unclassified' }
NumberFieldTest >> testTotallyReal [
	| x E |
'	x := QQ polynomials x.
	E := NumberField polynomial: x^2 + 2.
	self assert: E isReal not.
	E := NumberField polynomial: x^2 - 2.
	self assert: E isReal.
	E := NumberField polynomial: x^4 - 2.
	self assert: E isReal not'
]
