"
GroebnerBasisBenchmark new run

fixed katsura generators:
testCyclic3	10,600 per second.
testCyclic4	1,870 per second.
testCyclic5	6.69 per second.
testEliminationExample	3,280 per second.
testKatsura2	16,400 per second.
testKatsura3	3,990 per second.
testKatsura4	559 per second.
testModularCyclic3	9,680 per second.
testModularKatsura2	14,800 per second.
testModularKatsura3	4,110 per second.
testModularKatsura4	674 per second.

changed Buchberger>>run to do full reductions (calling reduceFull:).
This seems to be slower when the number of variables is low, but starts to pay off for n > 3
testCyclic3	10,200 per second.
testCyclic4	1,810 per second.
testCyclic5	6.56 per second.
testEliminationExample	3,260 per second.
testKatsura2	16,800 per second.
testKatsura3	4,230 per second.
testKatsura4	554 per second.
testModularCyclic3	9,810 per second.
testModularKatsura2	16,000 per second.
testModularKatsura3	4,470 per second.
testModularKatsura4	695 per second.

testCyclic3	14,400 per second. (11 May 2018, Buchberger>>run replaced Set by OrderedCollection)
testCyclic4	1,810 per second.
testCyclic5	3.37 per second.
testEliminationExample	3,950 per second.
testKatsura2	23,600 per second.
testKatsura3	6,120 per second.
testKatsura4	487 per second.
testModularCyclic3	13,300 per second.
testModularKatsura2	22,000 per second.
testModularKatsura3	6,270 per second.
testModularKatsura4	593 per second.

testCyclic3	14,600 per second. (10 May 2018, optimized Buchberger to reduce the polynomials from S before adding them to basis, fixed definition of the ideal of cyclic n-roots)
testCyclic4	1,860 per second.
testCyclic5	2.64 per second.
testEliminationExample	3,920 per second.
testKatsura2	23,900 per second.
testKatsura3	6,400 per second.
testKatsura4	496 per second.
testModularCyclic3	13,900 per second.
testModularKatsura2	22,500 per second.
testModularKatsura3	6,400 per second.
testModularKatsura4	613 per second.' 

testCyclic3	8,190 per second. (9 May 2018, optimized Buchberger>>run, added i0)
testCyclic4	2,920 per second.
testCyclic5	1,060 per second.
testCyclic6	381 per second.
testEliminationExample	2,820 per second.
testKatsura2	16,300 per second.
testKatsura3	3,930 per second.
testKatsura4	42.2 per second.
testModularCyclic3	7,820 per second.
testModularKatsura2	15,200 per second.
testModularKatsura3	3,630 per second.
testModularKatsura4	54.4 per second.

testCyclic3	4,730 per second. (25 Dec 2017, after refactoring MultivariatePolynomial and removing MonomialIndexedTuple)
testCyclic4	1,040 per second.
testCyclic5	258 per second.
testCyclic6	63.5 per second.
testEliminationExample	1,700 per second.
testKatsura2	13,900 per second.
testKatsura3	2,060 per second.
testKatsura4	16.7 per second.
testModularCyclic3	4,480 per second.
testModularKatsura2	12,800 per second.
testModularKatsura3	1,900 per second.
testModularKatsura4	22.3 per second.' 

testCyclic3	4,400 per second. (optimized GroebnerBasis>>reduce:)
testCyclic4	1,000 per second.
testCyclic5	238 per second.
testCyclic6	58 per second.
testEliminationExample	1,840 per second.
testKatsura2	13,600 per second.
testKatsura3	1,950 per second.
testKatsura4	15.6 per second.
testModularCyclic3	4,270 per second.
testModularKatsura2	12,600 per second.
testModularKatsura3	1,800 per second.
testModularKatsura4	20.6 per second.

testCyclic3	2,260 per second. (modular inversion using extended euclid)
testCyclic4	520 per second.
testCyclic5	124 per second.
testCyclic6	28.9 per second.
testEliminationExample	897 per second.
testKatsura2	6,690 per second.
testKatsura3	869 per second.
testKatsura4	10.6 per second.
testModularCyclic3	2,430 per second.
testModularKatsura2	7,470 per second.
testModularKatsura3	1,050 per second.
testModularKatsura4	15.5 per second.

testCyclic3	2,230 per second. (polynomials as sorted dictionaries monomial -> coefficient)
testCyclic4	512 per second.
testCyclic5	121 per second.
testCyclic6	28.7 per second.
testEliminationExample	867 per second.
testKatsura2	6,700 per second.
testKatsura3	860 per second.
testKatsura4	11 per second.
testModularCyclic3	2,320 per second.
testModularKatsura2	6,960 per second.
testModularKatsura3	858 per second.
testModularKatsura4	12.1 per second.

testCyclic3	2,270 per second. (polynomials as dictionaries monomial -> coefficient)
testCyclic4	511 per second.
testCyclic5	118 per second.
testCyclic6	26.1 per second.
testEliminationExample	816 per second.
testKatsura2	6,750 per second.
testKatsura3	866 per second.
testKatsura4	11.8 per second.
testModularCyclic3	2,410 per second.
testModularKatsura2	6,780 per second.
testModularKatsura3	844 per second.
testModularKatsura4	13.3 per second.

testCyclic3	2,240 per second. (with Groebner bases kept sorted, GroebnerBasis>>initialize)
testCyclic4	520 per second.
testCyclic5	120 per second.
testCyclic6	26 per second.
testEliminationExample	720 per second.
testKatsura2	6,730 per second.
testKatsura3	755 per second.
testKatsura4	34.9 per second.
testModularCyclic3	2,310 per second.
testModularKatsura2	6,720 per second.
testModularKatsura3	727 per second.
testModularKatsura4	33 per second.

testCyclic3	2,140 per second. (reverted Monomial>>hash)
testCyclic4	676 per second.
testCyclic5	112 per second.
testCyclic6	36.2 per second.
testEliminationExample	773 per second.
testKatsura2	6,430 per second.
testKatsura3	821 per second.
testKatsura4	7.72 per second.
testModularCyclic3	2,220 per second.
testModularKatsura2	6,490 per second.
testModularKatsura3	797 per second.
testModularKatsura4	12.6 per second.

testCyclic3	2,240 per second. (defined Monomial>>hash as 'exponents hash')
testCyclic4	682 per second.
testCyclic5	116 per second.
testCyclic6	40.4 per second.
testEliminationExample	827 per second.
testKatsura2	6,650 per second.
testKatsura3	857 per second.
testKatsura4	7.82 per second.
testModularCyclic3	2,370 per second.
testModularKatsura2	6,840 per second.
testModularKatsura3	861 per second.
testModularKatsura4	13.6 per second.

testCyclic3	1,780 per second. (spur 32 bits)
testCyclic4	354 per second.
testCyclic5	26.8 per second.
testCyclic6	12.2 per second.
testEliminationExample	614 per second.
testKatsura2	5,540 per second.
testKatsura3	130 per second.
testKatsura4	10.7 per second.
testModularCyclic3	177 per second.
testModularKatsura2	194 per second.

[self new modularCyclic: 7 :: groebnerBasis] bench
 '3.63 per second.' (spur 32 bits)
 '165 seconds.' 

testCyclic3	1,300 per second.
testCyclic4	264 per second.
testCyclic5	60.1 per second.
testCyclic6	9.7 per second.
testElimination	143 per second.
testKatsura2	4,230 per second.
testKatsura3	407 per second.
testKatsura4	4.06 per second.
testModularCyclic3	175 per second.
testModularKatsura2	194 per second. 

testCyclic3	1,130 per second.
testCyclic4	195 per second.
testCyclic5	48.7 per second.
testCyclic6	9.31 per second.
testElimination	116 per second.
testKatsura2	3,440 per second.
testKatsura3	354 per second.
testKatsura4	2.8 per second.
testModularCyclic3	149 per second.
testModularKatsura2	184 per second.'

'testCyclic3	1,080 per second.
testCyclic4	36.8 per second.
testCyclic5	1.19 per second.
testElimination	77.1 per second.
testKatsura2	3,810 per second.
testKatsura3	26.1 per second.
testModularCyclic3	173 per second.
testModularKatsura2	201 per second.' 

testCyclic3	1,060 per second.
testCyclic4	56.3 per second.
testCyclic5	1.08 per second.
testElimination	241 per second.
testKatsura2	4,790 per second.
testKatsura3	11.5 per second.
testModularCyclic3	173 per second.
testModularKatsura2	200 per second.

testCyclic3	615 per second.
testCyclic4	29.2 per second.
testCyclic5	1.38 per second.
testElimination	43.5 per second.
testKatsura2	2,330 per second.
testKatsura3	7.21 per second.

testCyclic3	632 per second.
testCyclic4	4.34 per second.
testElimination	3.45 per second.
testKatsura2	2,190 per second.
testKatsura3	0.288 per second.

testCyclic3	524 per second.
testCyclic4	4.85 per second.
testElimination	2.82 per second.
testKatsura2	1,950 per second.
testKatsura3	0.251 per second.

testCyclic3	540 per second.
testCyclic4	3.73 per second.
testElimination	2 per second.
testKatsura2	2,130 per second.
testKatsura3	0.257 per second.

testCyclic3	494 per second.
testCyclic4	2.41 per second.
testElimination	1.34 per second.
testKatsura2	1,950 per second.
testKatsura3	5.38 seconds.

testCyclic3	393 per second.
testCyclic4	1.62 per second.
testElimination	1.29 per second.
testKatsura2	1,830 per second.
testKatsura3	6.58 seconds.

old:
testCyclic3	312 per second.
testElimination	0.911 per second.
testKatsura2	1,260 per second.

"
Class {
	#name : #GroebnerBasisBenchmark,
	#superclass : #Benchmark,
	#category : #MathematicsTests
}

{ #category : #'as yet unclassified' }
GroebnerBasisBenchmark >> testCyclic3 [
	(QQ polynomialsIn: 3) cyclicIdeal groebnerBasis
]

{ #category : #'as yet unclassified' }
GroebnerBasisBenchmark >> testCyclic4 [
	(QQ polynomialsIn: 4) cyclicIdeal groebnerBasis
]

{ #category : #'as yet unclassified' }
GroebnerBasisBenchmark >> testCyclic5 [
	(QQ polynomialsIn: 5) cyclicIdeal groebnerBasis
]

{ #category : #'as yet unclassified' }
GroebnerBasisBenchmark >> testEliminationExample [
	| Qx x y z I |
	Qx := QQ polynomialsIn: #(x y z).
	x := Qx x. y := Qx y. z := Qx z.
	I := 'Qx * {x^2 + y + z - 1. x + (y^2) + z - 1. x + y + (z^2) - 1}'.
	I eliminateAll: #(1 2)
]

{ #category : #'as yet unclassified' }
GroebnerBasisBenchmark >> testKatsura2 [
	(QQ polynomialsIn: 2) katsuraIdeal groebnerBasis
]

{ #category : #'as yet unclassified' }
GroebnerBasisBenchmark >> testKatsura3 [
	(QQ polynomialsIn: 3) katsuraIdeal groebnerBasis
]

{ #category : #'as yet unclassified' }
GroebnerBasisBenchmark >> testKatsura4 [
	(QQ polynomialsIn: 4) katsuraIdeal groebnerBasis
]

{ #category : #'as yet unclassified' }
GroebnerBasisBenchmark >> testModularCyclic3 [
	((PrimeField new: 32003) polynomialsIn: 3) cyclicIdeal groebnerBasis
]

{ #category : #'as yet unclassified' }
GroebnerBasisBenchmark >> testModularKatsura2 [
	((PrimeField new: 32003) polynomialsIn: 2) katsuraIdeal groebnerBasis
]

{ #category : #'as yet unclassified' }
GroebnerBasisBenchmark >> testModularKatsura3 [
	((PrimeField new: 32003) polynomialsIn: 3) katsuraIdeal groebnerBasis
]

{ #category : #'as yet unclassified' }
GroebnerBasisBenchmark >> testModularKatsura4 [
	((PrimeField new: 32003) polynomialsIn: 4) katsuraIdeal groebnerBasis
]
