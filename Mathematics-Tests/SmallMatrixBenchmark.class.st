"
This benchmark tests some basic operations on 64x64 matrices over Z, Z/2Z, and Z/32003Z.

self new run

testAdditionZ	7,830 per second. (23/1/2018)
testAdditionZ2	216,000 per second.
testAdditionZp	8,140 per second.
testCopyZ	158,000 per second.
testCopyZ2	448,000 per second.
testCopyZp	176,000 per second.
testImageZ	FAILED
testImageZ2	35.5 per second.
testImageZp	141 per second.
testKernelZ	FAILED
testKernelZ2	14.4 per second.
testKernelZp	61.5 per second.
testMultiplicationZ	164 per second.
testMultiplicationZ2	171 per second.
testMultiplicationZp	130 per second.
testTranspositionZ	4,520 per second.
testTranspositionZ2	1,400 per second.
testTranspositionZp	1,930 per second.

testAdditionZ	7,770 per second.
testAdditionZ2	88,100 per second.
testAdditionZp	8,140 per second.
testCopyZ	145,000 per second.
testCopyZ2	441,000 per second.
testCopyZp	164,000 per second.
testImageZ	FAILED
testImageZ2	31.2 per second.
testImageZp	133 per second.
testKernelZ	FAILED
testKernelZ2	13.7 per second.
testKernelZp	59.7 per second.
testMultiplicationZ	169 per second.
testMultiplicationZ2	158 per second.
testMultiplicationZp	128 per second.
testTranspositionZ	4,360 per second.
testTranspositionZ2	1,090 per second.
testTranspositionZp	1,960 per second.

testAdditionZ	7,960 per second.
testAdditionZ2	85,700 per second.
testAdditionZp	7,710 per second.
testCopyZ	162,000 per second.
testCopyZ2	477,000 per second.
testCopyZp	181,000 per second.
testMultiplicationZ	174 per second.
testMultiplicationZ2	161 per second.
testMultiplicationZp	130 per second.
testTranspositionZ	4,600 per second.
testTranspositionZ2	1,090 per second.
testTranspositionZp	2,110 per second.

testAdditionZ	7,840 per second. (spur 32 bits)
testAdditionZ2	86,600 per second.
testCopyZ	144,000 per second.
testCopyZ2	471,000 per second.
testMultiplicationZ	171 per second.
testMultiplicationZ2	159 per second.
testTranspositionZ	4,390 per second.
testTranspositionZ2	1,010 per second.

testAdditionZ	5,220 per second.
testAdditionZ2	42,600 per second.
testCopyZ	84,700 per second.
testCopyZ2	210,000 per second.
testMultiplicationZ	122 per second.
testMultiplicationZ2	106 per second.
testTranspositionZ	2,020 per second.
testTranspositionZ2	603 per second.

testAdditionZ	4,500 per second.
testAdditionZ2	33,700 per second.
testCopyZ	58,200 per second.
testCopyZ2	164,000 per second.
testMultiplicationZ	20.1 per second.
testMultiplicationZ2	7.81 per second.
testTranspositionZ	1,580 per second.
testTranspositionZ2	565 per second.

"
Class {
	#name : #SmallMatrixBenchmark,
	#superclass : #Benchmark,
	#instVars : [
		'integerMatrix',
		'binaryMatrix',
		'modularMatrix'
	],
	#category : #'Mathematics-Tests'
}

{ #category : #'as yet unclassified' }
SmallMatrixBenchmark >> setUp [
'	integerMatrix := ZZ ^ (64@64) :: atRandomBits: 10000.
	binaryMatrix := (PrimeField new: 2) ^ (64@64) :: atRandom.
	modularMatrix := (PrimeField new: 32003) ^ (64@64) :: atRandom'
]

{ #category : #'as yet unclassified' }
SmallMatrixBenchmark >> testAdditionZ [
	integerMatrix + integerMatrix
]

{ #category : #'as yet unclassified' }
SmallMatrixBenchmark >> testAdditionZ2 [
	binaryMatrix + binaryMatrix
]

{ #category : #'as yet unclassified' }
SmallMatrixBenchmark >> testAdditionZp [
	modularMatrix + modularMatrix
]

{ #category : #'as yet unclassified' }
SmallMatrixBenchmark >> testCopyZ [
	integerMatrix copy
]

{ #category : #'as yet unclassified' }
SmallMatrixBenchmark >> testCopyZ2 [
	binaryMatrix copy
]

{ #category : #'as yet unclassified' }
SmallMatrixBenchmark >> testCopyZp [
	modularMatrix copy
]

{ #category : #'as yet unclassified' }
SmallMatrixBenchmark >> testImageZ [
	integerMatrix image
]

{ #category : #'as yet unclassified' }
SmallMatrixBenchmark >> testImageZ2 [
	binaryMatrix image
]

{ #category : #'as yet unclassified' }
SmallMatrixBenchmark >> testImageZp [
	modularMatrix image
]

{ #category : #'as yet unclassified' }
SmallMatrixBenchmark >> testKernelZ [
	integerMatrix kernel
]

{ #category : #'as yet unclassified' }
SmallMatrixBenchmark >> testKernelZ2 [
	binaryMatrix kernel
]

{ #category : #'as yet unclassified' }
SmallMatrixBenchmark >> testKernelZp [
	modularMatrix kernel
]

{ #category : #'as yet unclassified' }
SmallMatrixBenchmark >> testMultiplicationZ [
	integerMatrix * integerMatrix
]

{ #category : #'as yet unclassified' }
SmallMatrixBenchmark >> testMultiplicationZ2 [
	binaryMatrix * binaryMatrix
]

{ #category : #'as yet unclassified' }
SmallMatrixBenchmark >> testMultiplicationZp [
	modularMatrix * modularMatrix
]

{ #category : #'as yet unclassified' }
SmallMatrixBenchmark >> testTranspositionZ [
	integerMatrix transposed
]

{ #category : #'as yet unclassified' }
SmallMatrixBenchmark >> testTranspositionZ2 [
	binaryMatrix transposed
]

{ #category : #'as yet unclassified' }
SmallMatrixBenchmark >> testTranspositionZp [
	modularMatrix transposed
]
