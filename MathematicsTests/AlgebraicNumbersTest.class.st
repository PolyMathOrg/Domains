Class {
	#name : #AlgebraicNumbersTest,
	#superclass : #TestCase,
	#category : #MathematicsTests
}

{ #category : #accessing }
AlgebraicNumbersTest >> testArithmetic [
	| sqrt2 sqrt3 sqrt5 sqrt6 |
	sqrt2 := ComplexAlgebraicNumber sqrt2.
	sqrt3 := ComplexAlgebraicNumber sqrt: 3.
	sqrt5 := ComplexAlgebraicNumber sqrt: 5.
	sqrt6 := ComplexAlgebraicNumber sqrt: 6.
	self assert: sqrt2 squared equals: 2.
	self assert: (sqrt2 + sqrt3) * sqrt2 equals: 2 + sqrt6.
	self assert: (sqrt3 / sqrt5) squared reciprocal equals: 5 / 3.
	"self assert: ((5 root: 3) + sqrt2 - sqrt2 raiseTo: 3) asRational = 5"
]

{ #category : #'as yet unclassified' }
AlgebraicNumbersTest >> testDivision [
	| sqrt3 sqrt5 |
	sqrt3 := ComplexAlgebraicNumber sqrt: 3.
	sqrt5 := ComplexAlgebraicNumber sqrt: 5.
	self assert: sqrt3 / sqrt5 / sqrt3 / sqrt5 = (1/5)
]

{ #category : #'as yet unclassified' }
AlgebraicNumbersTest >> testMultiplicationByi [
	| a |
	a := ComplexAlgebraicNumber sqrt2.
	self assert: a i i = a negated
]

{ #category : #'as yet unclassified' }
AlgebraicNumbersTest >> testNorm [
	| a |
	a := ComplexAlgebraicNumber phi.
	self assert: a norm = a conjugates product
]

{ #category : #'as yet unclassified' }
AlgebraicNumbersTest >> testProduct [
	| sqrt3 sqrt5 |
	sqrt3 := ComplexAlgebraicNumber sqrt: 3.
	sqrt5 := ComplexAlgebraicNumber sqrt: 5.
	self assert: sqrt3 * sqrt5 * sqrt3 * sqrt5 = 15
]

{ #category : #'as yet unclassified' }
AlgebraicNumbersTest >> testRealArithmetic [
	| sqrt2 sqrt3 sqrt5 sqrt6 |
	sqrt2 := RealAlgebraicNumber sqrt2.
	sqrt3 := RealAlgebraicNumber sqrt: 3.
	sqrt5 := RealAlgebraicNumber sqrt: 5.
	sqrt6 := RealAlgebraicNumber sqrt: 6.
	self assert: sqrt2 squared asRational = 2.
	self assert: (sqrt2 + sqrt3) * sqrt2 = (2 + sqrt6).
	self assert: (sqrt3 / sqrt5) squared reciprocal = (5/3).
"	self assert: (((five root: 3) + sqrt2 - sqrt2) ^ 3) asRational = 5"
]

{ #category : #'as yet unclassified' }
AlgebraicNumbersTest >> testRealDivision [
	| sqrt3 sqrt5 |
	sqrt3 := RealAlgebraicNumber sqrt: 3.
	sqrt5 := RealAlgebraicNumber sqrt: 5.
	self assert: (sqrt3 / sqrt5 / sqrt3 / sqrt5) asRational = (1/5)
]

{ #category : #'as yet unclassified' }
AlgebraicNumbersTest >> testRealNormalizationBug [
	| f interval x |
	x := QQ polynomials x.
	f := 'x^4 * 1576875 - (x^2 * 877250) + 43923'.
	interval := RealInterval open: (-260139/1345600) closed: (81631/134560).
	RealAlgebraicNumber polynomial: f bounds: interval
]

{ #category : #'as yet unclassified' }
AlgebraicNumbersTest >> testRealProduct [
	| sqrt3 sqrt5 |
	sqrt3 := RealAlgebraicNumber sqrt: 3.
	sqrt5 := RealAlgebraicNumber sqrt: 5.
	self assert: (sqrt3 * sqrt5 * sqrt3 * sqrt5) asRational = 15
]

{ #category : #'as yet unclassified' }
AlgebraicNumbersTest >> testRealSquare [
	| sqrt2 |
	sqrt2 := RealAlgebraicNumber sqrt2.
	self assert: sqrt2 squared asRational = 2
]

{ #category : #'as yet unclassified' }
AlgebraicNumbersTest >> testRealSquareRoot [
	| a |
	a := RealAlgebraicNumber sqrt2.
	self assert: a squareRoot squared = a
]

{ #category : #'as yet unclassified' }
AlgebraicNumbersTest >> testRealSum [
	| sqrt2 sqrt3 sqrt5 |
	sqrt2 := RealAlgebraicNumber sqrt: 2.
	sqrt3 := RealAlgebraicNumber sqrt: 3.
	sqrt5 := RealAlgebraicNumber sqrt: 5.
	self assert: sqrt3 + sqrt5 + sqrt2 - sqrt3 - sqrt5 = sqrt2
]

{ #category : #'as yet unclassified' }
AlgebraicNumbersTest >> testSquare [
	| sqrt2 |
	sqrt2 := ComplexAlgebraicNumber sqrt2.
	self assert: sqrt2 squared = 2
]

{ #category : #'as yet unclassified' }
AlgebraicNumbersTest >> testSquareRoot [
	| a |
	a := ComplexAlgebraicNumber sqrt2.
	self assert: a squareRoot squared = a
]

{ #category : #'as yet unclassified' }
AlgebraicNumbersTest >> testSum [
	| sqrt2 sqrt3 sqrt5 |
	sqrt2 := ComplexAlgebraicNumber sqrt: 2.
	sqrt3 := ComplexAlgebraicNumber sqrt: 3.
	sqrt5 := ComplexAlgebraicNumber sqrt: 5.
	self assert: sqrt3 + sqrt5 + sqrt2 - sqrt3 - sqrt5 = sqrt2
]

{ #category : #'as yet unclassified' }
AlgebraicNumbersTest >> testTrace [
	| a |
	a := ComplexAlgebraicNumber phi.
	self assert: a trace = a conjugates sum
]
