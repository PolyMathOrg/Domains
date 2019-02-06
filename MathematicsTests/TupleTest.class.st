Class {
	#name : #TupleTest,
	#superclass : #TestCase,
	#category : #MathematicsTests
}

{ #category : #tests }
TupleTest >> testBitTupleBug [
	| Z2 |
	Z2 := PrimeField new: 2.
	self assert: ((1 , 0 , 0) % 2) sum equals: Z2 one.
	self assert: ((0 , 1 , 0) % 2) sum equals: Z2 one.
	self assert: ((1 , 1 , 0) % 2) sum equals: Z2 zero.
	self assert: ((1 , 1 , 1) % 2) sum equals: Z2 one
]

{ #category : #tests }
TupleTest >> testBitTupleOperations [
	| n a b |
	n := 120 atRandom.
	a := (ZZ raisedTo: n) atRandomBits: n * 2.
	b := (ZZ raisedTo: n) atRandomBits: n * 2.
	#(+ - convolution: dot: hadamard:)
		do: [ :op | 
			self
				testTuple: a
				with: b
				operation: op
				modulo: 2 ].
	#(negated reversed copy sum product)
		do: [ :op | self testTuple: a operation: op modulo: 2 ]
]

{ #category : #tests }
TupleTest >> testBitTupleReversed [
	| v i |
	v := ((ZZ / 2) raisedTo: (100 atRandom) ) atRandom.
	i := v size atRandom.
	self assert: (v reversed at: i) = (v at: v size - i + 1).
	self assert: v reversed reversed = v
]

{ #category : #tests }
TupleTest >> testBitTupleSum [
	self
		assert: (BitTuple fromInteger: 2r1011101) sum representative
		equals: 1.
	self
		assert: (BitTuple fromInteger: 2r10000100100010) sum representative
		equals: 0
]

{ #category : #tests }
TupleTest >> testHomogeneousTuples [
	self assert: (1 , 2 , 3) ~ (2 , 4 , 6).
	self deny: (1 , 2 , 3) ~ (-2 , 4 , 6)
]

{ #category : #tests }
TupleTest >> testHomogeneousTuples2 [
	| P Q |
	P := 1 , 2 over: ZZ.
	Q := 2 , 4 over: ZZ.
	self assert: P ~ Q.
	P := 1 , 2 over: ZZ.
	Q := 1 , 0 over: ZZ.
	self deny: P ~ Q 
]

{ #category : #tests }
TupleTest >> testHomogeneousTuples3 [
	| R x P Q |
	R := QQ polynomials.
	x := R x.
	P := R
		tuple:
			{x.
			((x raisedTo: 2) + 1)}.
	Q := R
		tuple:
			{(x raisedTo: 2).
			(x raisedTo: 3 + x)}.
	self assert: P ~ Q
]

{ #category : #tests }
TupleTest >> testHomogeneousTuples4 [
	| P Q |
	P := (2 , 4 , 1) % 6.
	Q := (0 , 1 , 3) % 6.
	self deny: P ~ Q
]

{ #category : #tests }
TupleTest >> testMakeZero: aTuple [
	self assert: (aTuple * 0) isZero.
	self assert: (0 * aTuple) isZero.
	self assert: (aTuple + aTuple negated) isZero.
	self assert: (aTuple - aTuple) isZero
]

{ #category : #tests }
TupleTest >> testModTupleConcatenation [
	self
		assert: (1 , 2 , 3) % 7 , ((2 , 3 , 4) % 7)
		equals: (1 , 2 , 3 , 2 , 3 , 4) % 7
]

{ #category : #tests }
TupleTest >> testModTupleConvolution [
	| a b |
	a := 1 , 2 , 3.
	b := 2 , 3 , 4.
	self
		assert: (a % 7 convolution: b % 7)
		equals: (a convolution: b) % 7
]

{ #category : #tests }
TupleTest >> testModTupleOperations [
	| a b modulus |
	modulus := 10 atRandom + 1.
	a := (ZZ raisedTo: 5) atRandomBits: 30.
	b := (ZZ raisedTo: 5) atRandomBits: 30.
	#(+ - convolution: dot: hadamard:)
		do: [ :op | 
			self
				testTuple: a
				with: b
				operation: op
				modulo: modulus ].
	#(negated reversed copy sum product)
		do: [ :op | self testTuple: a operation: op modulo: modulus ]
]

{ #category : #tests }
TupleTest >> testModTupleSum [
	| a b |
	a := ZZ tuple: ((1 to: 10) collect: [ :i | 100 atRandom ]).
	b := a % 7.
	self assert: b sum equals: a sum % 7
]

{ #category : #tests }
TupleTest >> testTuple: a operation: aSymbol modulo: modulus [
	self assert: (a perform: aSymbol) % modulus = (a % modulus perform: aSymbol)
]

{ #category : #tests }
TupleTest >> testTuple: a with: b operation: aSymbol modulo: modulus [
	self assert: (a perform: aSymbol with: b) % modulus = (a % modulus perform: aSymbol with: b % modulus)
]

{ #category : #tests }
TupleTest >> testTupleSum [
	self assert: (1 , 2 , 3) sum equals: 1 + 2 + 3
]

{ #category : #tests }
TupleTest >> testTuplesModuleMembership [
	self assert: ((QQ raisedTo: 3) includes: 1 , 2 , 3).
	self assert: ((QQ raisedTo: 3) includes: 1 , 2 , 3 , 4) not
]
