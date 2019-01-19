"
Timings giving in [1] on computers with 0.8ghz - 1ghz intel cpus: general purpose system 20s-100s, tuned systems 2.3s-10s. For big coefficients: singular 28s, pari 77s.

[1] R.J. Fateman, Comparing the speed of sparse polynomial multiplication.


self new run

testBigCoefficientsProduct	8.5 seconds. (25 Dec 2017, after refactoring MultivariatePolynomial and removing MonomialIndexedTuple)
testBigExponentsProduct	6.38 seconds.
testProduct	0.295 per second.

testBigCoefficientsProduct	8.39 seconds. (polynomials as sorted dictionaries monomial -> coefficient)
testBigExponentsProduct	9.86 seconds.
testProduct	0.328 per second.

testBigCoefficientsProduct	10.5 seconds. (polynomials as dictionaries monomial -> coefficient)
testBigExponentsProduct	10.2 seconds.
testProduct	0.289 per second.

"
Class {
	#name : #SparsePolynomialMultiplicationBenchmark,
	#superclass : #Benchmark,
	#instVars : [
		'p',
		'pPlusOne',
		'pBigCoefficients',
		'pBigExponents',
		'pBigCoefficientsPlusOne',
		'pBigExponentsPlusOne'
	],
	#category : #MathematicsTests
}

{ #category : #'as yet unclassified' }
SparsePolynomialMultiplicationBenchmark >> setUp [
	| P x y z |
	P := ZZ polynomialsIn: #(x y z).
	x := P x.
	y := P y.
	z := P z.
	'p := (1+x+y+z)^20.
		pBigCoefficients := 10000000001*(1+x+y+z)^20. "big coefficients"
		pBigExponents := 1 + (x^2147483647) + (y^2147483647) + (z^2147483647) ^ 20. "big exponents"
		pPlusOne := p + 1.
		pBigCoefficientsPlusOne := pBigCoefficients + 1.
		pBigExponentsPlusOne := pBigExponents + 1'
]

{ #category : #'as yet unclassified' }
SparsePolynomialMultiplicationBenchmark >> testBigCoefficientsProduct [
	pBigCoefficients * pBigCoefficientsPlusOne
]

{ #category : #'as yet unclassified' }
SparsePolynomialMultiplicationBenchmark >> testBigExponentsProduct [
	pBigExponents * pBigExponentsPlusOne
]

{ #category : #'as yet unclassified' }
SparsePolynomialMultiplicationBenchmark >> testProduct [
	p * pPlusOne
]
