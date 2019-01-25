"
Some tests on a 300x300 matrix over Z/32003.

self new run

testAddition	384 per second.
testGaussianElimination	1.88 per second.
testImage	1.84 per second.
testKernel	0.736 per second.
testSquared	1.39 per second.
testTransposition	89.8 per second.

testAddition	387 per second.
testGaussianElimination	1.82 per second.
testSquared	1.43 per second.
testTransposition	89.7 per second.

testAddition	203 per second.
testGaussianElimination	1.81 per second.
testSquared	1.32 per second.
testTransposition	66.9 per second.
"
Class {
	#name : #ModularMatrixBenchmark,
	#superclass : #Benchmark,
	#instVars : [
		'field',
		'matrix'
	],
	#category : #MathematicsTests
}

{ #category : #'as yet unclassified' }
ModularMatrixBenchmark >> field: aField [
	field := aField
]

{ #category : #'as yet unclassified' }
ModularMatrixBenchmark >> setUp [
	| random |
	random := Random seed: 1234.
	field isNil
		ifTrue: [ field := ZZ / 32003 ].
	matrix := field
		matrix: 300 @ 300
		evaluating: [ :i :j | field atRandom: random ]
]

{ #category : #'as yet unclassified' }
ModularMatrixBenchmark >> testAddition [
	matrix + matrix
]

{ #category : #'as yet unclassified' }
ModularMatrixBenchmark >> testGaussianElimination [
	matrix reduction reduced
]

{ #category : #'as yet unclassified' }
ModularMatrixBenchmark >> testImage [
	matrix image
]

{ #category : #'as yet unclassified' }
ModularMatrixBenchmark >> testKernel [
	matrix kernel
]

{ #category : #'as yet unclassified' }
ModularMatrixBenchmark >> testSquared [
	matrix squared
]

{ #category : #'as yet unclassified' }
ModularMatrixBenchmark >> testTransposition [
	matrix transposed
]
