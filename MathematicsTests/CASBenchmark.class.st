"
These benchmarks show some of the fundamental bottlenecks for a computational algebra system in pure Smalltalk. Many important algorithms end up doing these operations.

To run the benchmarks, just doIt:
self new run

Cuis 4.5 with Cog 4.5 #9 (r3370, 2015-06-04), 32 bits, Intel i5-3210M @ 2.5Ghz, cache 3072 KB, 4990 bobomips, running inside virtualbox
testEqualsBytes	40,600 per second.
testEqualsWords	36,100 per second.
testHashBytes	245,000 per second.
testHashWords	23,500 per second.
testModularConvolutionBytes	20.6 per second.
testModularConvolutionWords	16.9 per second.
testModularDotProductBytes	36,900 per second.
testModularDotProductWords	30,400 per second.
testModularSumBytes	26,200 per second.
testModularSumWords	21,600 per second.
testPermutationCompositionArray	33,900 per second.
testPermutationCompositionWords	31,400 per second.

Cuis 5.0 with Cog 5.0-201611161032, 32 bits, Intel i5-3210M @ 2.5Ghz, cache 3072 KB, 4990 bobomips, running inside virtualbox
testEqualsBytes	59,900 per second.
testEqualsWords	49,600 per second.
testHashBytes	249,000 per second.
testHashWords	23,000 per second.
testModularConvolutionBytes	27.2 per second.
testModularConvolutionWords	23.9 per second.
testModularDotProductBytes	41,000 per second.
testModularDotProductWords	37,000 per second.
testModularSumBytes	37,900 per second.
testModularSumWords	34,100 per second.
testPermutationCompositionArray	69,100 per second.
testPermutationCompositionWords	51,900 per second.

"
Class {
	#name : #CASBenchmark,
	#superclass : #Object,
	#category : #MathematicsTests
}

{ #category : #'as yet unclassified' }
CASBenchmark >> run [
	| output |
	output := WriteStream on: (String new: 1000).
	(self class selectors asArray select: [:each|
		(each beginsWith: 'test') and: [each numArgs isZero]]) sort
		do: [:each|
			output nextPutAll: each; tab.
			"self setUp."
			Smalltalk garbageCollect.
			[output nextPutAll: (self perform: each)] on: Error do: [output nextPutAll: 'FAILED'].
			"self tearDown"]
		separatedBy: [output newLine].
	^ output contents
]

{ #category : #'as yet unclassified' }
CASBenchmark >> testConvolution: a with: b into: c modulo: m [
	c atAllPut: 0.
	1 to: a size do: [:i|
		1 to: b size do: [:j| | index |
			index := i+j-1.
			c at: index put: (a at: i) * (b at: j) + (c at: index) \\ m]].
	^ c
]

{ #category : #'as yet unclassified' }
CASBenchmark >> testDotProduct: a with: b modulo: m [
	| answer |
	answer := 0.
	1 to: a size do: [:i| answer := (a at: i) * (b at: i) + answer \\ m].
	^ answer
]

{ #category : #'as yet unclassified' }
CASBenchmark >> testEqualsBytes [
	| random a b |
	random := Random seed: 1234.
	a := ((1 to: 1000) collect: [:each| (random nextInteger: 256) - 1]) asByteArray.
	b := a copy.
	^ [a = b] bench
]

{ #category : #'as yet unclassified' }
CASBenchmark >> testEqualsWords [
	| random a b |
	random := Random seed: 1234.
	a := ((1 to: 1000) collect: [:each| (random nextInteger: 256) - 1]) asWordArray.
	b := a copy.
	^ [a = b] bench
]

{ #category : #'as yet unclassified' }
CASBenchmark >> testHashBytes [
	| random a |
	random := Random seed: 1234.
	a := ((1 to: 1000) collect: [:each| (random nextInteger: 256) - 1]) asByteArray.
	^ [a hash] bench
]

{ #category : #'as yet unclassified' }
CASBenchmark >> testHashWords [
	| random a |
	random := Random seed: 1234.
	a := ((1 to: 1000) collect: [:each| (random nextInteger: 256) - 1]) asWordArray.
	^ [a hash] bench
]

{ #category : #'as yet unclassified' }
CASBenchmark >> testModularConvolutionBytes [
	| random p a b c |
	p := 251.
	random := Random seed: 1234.
	a := ((1 to: 1000) collect: [:each| (random nextInteger: p) - 1]) asByteArray.
	b := ((1 to: 1000) collect: [:each| (random nextInteger: p) - 1]) asByteArray.
	c := ByteArray new: 2000.
	^ [self testConvolution: a with: b into: c modulo: p] bench
]

{ #category : #'as yet unclassified' }
CASBenchmark >> testModularConvolutionWords [
	| random p a b c |
	p := 32003.
	random := Random seed: 1234.
	a := ((1 to: 1000) collect: [:each| (random nextInteger: p) - 1]) asWordArray.
	b := ((1 to: 1000) collect: [:each| (random nextInteger: p) - 1]) asWordArray.
	c := WordArray new: 2000.
	^ [self testConvolution: a with: b into: c modulo: p] bench
]

{ #category : #'as yet unclassified' }
CASBenchmark >> testModularDotProductBytes [
	| random p a b |
	p := 251.
	random := Random seed: 1234.
	a := ((1 to: 1000) collect: [:each| (random nextInteger: p) - 1]) asByteArray.
	b := ((1 to: 1000) collect: [:each| (random nextInteger: p) - 1]) asByteArray.
	^ [self testDotProduct: a with: b modulo: p] bench
]

{ #category : #'as yet unclassified' }
CASBenchmark >> testModularDotProductWords [
	| random p a b |
	p := 32003.
	random := Random seed: 1234.
	a := ((1 to: 1000) collect: [:each| (random nextInteger: p) - 1]) asWordArray.
	b := ((1 to: 1000) collect: [:each| (random nextInteger: p) - 1]) asWordArray.
	^ [self testDotProduct: a with: b modulo: p] bench
]

{ #category : #'as yet unclassified' }
CASBenchmark >> testModularSumBytes [
	| random p a b c |
	p := 251.
	random := Random seed: 1234.
	a := ((1 to: 1000) collect: [:each| (random nextInteger: p) - 1]) asByteArray.
	b := ((1 to: 1000) collect: [:each| (random nextInteger: p) - 1]) asByteArray.
	c := ByteArray new: 1000.
	^ [self testSum: a with: b into: c modulo: p] bench
]

{ #category : #'as yet unclassified' }
CASBenchmark >> testModularSumWords [
	| random p a b c |
	p := 32003.
	random := Random seed: 1234.
	a := ((1 to: 1000) collect: [:each| (random nextInteger: p) - 1]) asWordArray.
	b := ((1 to: 1000) collect: [:each| (random nextInteger: p) - 1]) asWordArray.
	c := WordArray new: 1000.
	^ [self testSum: a with: b into: c modulo: p] bench
]

{ #category : #'as yet unclassified' }
CASBenchmark >> testPermutate: a with: b into: c [
	1 to: a size do: [:i| c at: i put: (b at: (a at: i))]
]

{ #category : #'as yet unclassified' }
CASBenchmark >> testPermutationCompositionArray [
	| n a b c |
	n := 1000.
	a := (1 to: n) shuffled.
	b := (1 to: n) shuffled.
	c := Array new: n.
	^ [self testPermutate: a with: b into: c] bench
]

{ #category : #'as yet unclassified' }
CASBenchmark >> testPermutationCompositionWords [
	| n a b c |
	n := 1000.
	a := (1 to: n) shuffled asWordArray.
	b := (1 to: n) shuffled asWordArray.
	c := WordArray new: n.
	^ [self testPermutate: a with: b into: c] bench
]

{ #category : #'as yet unclassified' }
CASBenchmark >> testSum: a with: b into: c modulo: m [
	1 to: a size do: [:i| c at: i put: (a at: i) + (b at: i) \\ m].
	^ c
]
