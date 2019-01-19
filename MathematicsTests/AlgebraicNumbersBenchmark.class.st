"
AlgebraicNumbersBenchmark new run

testComplexAlgebraicNumberAddition	1.1 per second. (25 May 2018)
testComplexAlgebraicNumberDivision	63.9 per second.
testComplexAlgebraicNumberProduct	68.3 per second.
testComplexAlgebraicNumberSquare	2,080 per second.
testRealAlgebraicNumberAddition	0.936 per second.
testRealAlgebraicNumberDivision	61.7 per second.
testRealAlgebraicNumberProduct	67.1 per second.
testRealAlgebraicNumberSquare	2,010 per second.

testComplexAlgebraicNumberAddition	0.907 per second. (18 May 2018)
testComplexAlgebraicNumberDivision	61 per second.
testComplexAlgebraicNumberProduct	64.7 per second.
testComplexAlgebraicNumberSquare	1,760 per second.
testRealAlgebraicNumberAddition	0.997 per second.
testRealAlgebraicNumberDivision	58.2 per second.
testRealAlgebraicNumberProduct	62.6 per second.
testRealAlgebraicNumberSquare	1,730 per second.

testComplexAlgebraicNumberAddition	0.84 per second.
testComplexAlgebraicNumberDivision	58.4 per second.
testComplexAlgebraicNumberProduct	61.6 per second.
testComplexAlgebraicNumberSquare	1,770 per second.
testRealAlgebraicNumberAddition	0.952 per second.
testRealAlgebraicNumberDivision	48.3 per second.
testRealAlgebraicNumberProduct	56.2 per second.
testRealAlgebraicNumberSquare	1,460 per second.

testComplexAlgebraicNumberAddition	1.08 per second. (29 Apr 2018)
testComplexAlgebraicNumberDivision	57.6 per second.
testComplexAlgebraicNumberProduct	61.2 per second.
testComplexAlgebraicNumberSquare	1,660 per second.
testRealAlgebraicNumberAddition	0.78 per second.
testRealAlgebraicNumberDivision	55.8 per second.
testRealAlgebraicNumberProduct	59.1 per second.
testRealAlgebraicNumberSquare	1,610 per second.' 

"
Class {
	#name : #AlgebraicNumbersBenchmark,
	#superclass : #Benchmark,
	#category : #MathematicsTests
}

{ #category : #'as yet unclassified' }
AlgebraicNumbersBenchmark >> testComplexAlgebraicNumberAddition [
	| sqrt2 sqrt3 sqrt5 |
	sqrt2 := ComplexAlgebraicNumber sqrt: 2.
	sqrt3 := ComplexAlgebraicNumber sqrt: 3.
	sqrt5 := ComplexAlgebraicNumber sqrt: 5.
	10 timesRepeat: [sqrt3 + sqrt5 + sqrt2 - sqrt3 - sqrt5]
]

{ #category : #'as yet unclassified' }
AlgebraicNumbersBenchmark >> testComplexAlgebraicNumberDivision [
	| sqrt3 sqrt5 |
	sqrt3 := ComplexAlgebraicNumber sqrt: 3.
	sqrt5 := ComplexAlgebraicNumber sqrt: 5.
	10 timesRepeat: [sqrt3 / sqrt5 / sqrt3 / sqrt5]
]

{ #category : #'as yet unclassified' }
AlgebraicNumbersBenchmark >> testComplexAlgebraicNumberProduct [
	| sqrt3 sqrt5 |
	sqrt3 := ComplexAlgebraicNumber sqrt: 3.
	sqrt5 := ComplexAlgebraicNumber sqrt: 5.
	10 timesRepeat: [sqrt3 * sqrt5 * sqrt3 * sqrt5]
]

{ #category : #'as yet unclassified' }
AlgebraicNumbersBenchmark >> testComplexAlgebraicNumberSquare [
	| sqrt2 |
	sqrt2 := ComplexAlgebraicNumber sqrt2.
	10 timesRepeat: [sqrt2 squared]
]

{ #category : #'as yet unclassified' }
AlgebraicNumbersBenchmark >> testRealAlgebraicNumberAddition [
	| sqrt2 sqrt3 sqrt5 |
	sqrt2 := RealAlgebraicNumber sqrt: 2.
	sqrt3 := RealAlgebraicNumber sqrt: 3.
	sqrt5 := RealAlgebraicNumber sqrt: 5.
	10 timesRepeat: [sqrt3 + sqrt5 + sqrt2 - sqrt3 - sqrt5]
]

{ #category : #'as yet unclassified' }
AlgebraicNumbersBenchmark >> testRealAlgebraicNumberDivision [
	| sqrt3 sqrt5 |
	sqrt3 := RealAlgebraicNumber sqrt: 3.
	sqrt5 := RealAlgebraicNumber sqrt: 5.
	10 timesRepeat: [sqrt3 / sqrt5 / sqrt3 / sqrt5]
]

{ #category : #'as yet unclassified' }
AlgebraicNumbersBenchmark >> testRealAlgebraicNumberProduct [
	| sqrt3 sqrt5 |
	sqrt3 := RealAlgebraicNumber sqrt: 3.
	sqrt5 := RealAlgebraicNumber sqrt: 5.
	10 timesRepeat: [sqrt3 * sqrt5 * sqrt3 * sqrt5]
]

{ #category : #'as yet unclassified' }
AlgebraicNumbersBenchmark >> testRealAlgebraicNumberSquare [
	| sqrt2 |
	sqrt2 := RealAlgebraicNumber sqrt2.
	10 timesRepeat: [sqrt2 squared]
]
