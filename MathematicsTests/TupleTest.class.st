Class {
	#name : #TupleTest,
	#superclass : #TestCase,
	#category : #MathematicsTests
}

{ #category : #'as yet unclassified' }
TupleTest >> testBitTupleBug [
	| Z2 |
	Z2 := PrimeField new: 2.
	'self assert: ((1,0,0) % 2 :: sum = Z2 one).
		self assert: ((0,1,0) % 2 :: sum = Z2 one).
		self assert: ((1,1,0) % 2 :: sum = Z2 zero).
		self assert: ((1,1,1) % 2 :: sum = Z2 one)'
]

{ #category : #'as yet unclassified' }
TupleTest >> testBitTupleOperations [
	| n a b |
	n := 120 atRandom.
'	a := ZZ^n atRandomBits: n*2.
	b := ZZ^n atRandomBits: n*2'.
	#(+ - convolution: dot: hadamard:) do: [:op|
		self testTuple: a with: b operation: op modulo: 2].
	#(negated reversed copy sum product) do: [:op|
		self testTuple: a operation: op modulo: 2]
]

{ #category : #'as yet unclassified' }
TupleTest >> testBitTupleReversed [
	| v i |
'	v := ZZ / 2 ^ 100 atRandom :: atRandom'.
	i := v size atRandom.
	self assert: (v reversed at: i) = (v at: v size - i + 1).
	self assert: v reversed reversed = v
]

{ #category : #'as yet unclassified' }
TupleTest >> testBitTupleSum [
	self assert: (BitTuple fromInteger: 2r1011101) sum representative = 1.
	self assert: (BitTuple fromInteger: 2r10000100100010) sum representative = 0
]

{ #category : #'as yet unclassified' }
TupleTest >> testHomogeneousTuples [
	self assert: (1,2,3) ~ (2,4,6).
	self deny: (1,2,3) ~ (-2,4,6)
]

{ #category : #'as yet unclassified' }
TupleTest >> testHomogeneousTuples2 [
	| P Q |
	P := (1,2) over: ZZ.
	Q := (2,4) over: ZZ.
	self assert: P ~ Q.
	P := (1,2) over: ZZ.
	Q := (1,0) over: ZZ.
	self deny: P ~ Q
]

{ #category : #'as yet unclassified' }
TupleTest >> testHomogeneousTuples3 [
	| R x P Q |
	R := QQ polynomials.
	x := R x.
	'P := R tuple: {x. x^2 + 1}.
		Q := R tuple: {x^2. x^3 + x}'.
	self assert: P ~ Q
]

{ #category : #'as yet unclassified' }
TupleTest >> testHomogeneousTuples4 [
	| P Q |
	P := (2,4,1) % 6.
	Q := (0,1,3) % 6.
	self deny: P ~ Q
]

{ #category : #'as yet unclassified' }
TupleTest >> testMakeZero: aTuple [
	self assert: (aTuple * 0) isZero.
	self assert: (0 * aTuple) isZero.
	self assert: (aTuple + aTuple negated) isZero.
	self assert: (aTuple - aTuple) isZero
]

{ #category : #'as yet unclassified' }
TupleTest >> testModTupleConcatenation [
	self assert: (1,2,3) % 7, ((2,3,4) % 7) = ((1,2,3,2,3,4) % 7)
]

{ #category : #'as yet unclassified' }
TupleTest >> testModTupleConvolution [
	| a b |
	a := (1,2,3).
	b := (2,3,4).
	self assert: (a % 7 convolution: b % 7) = ((a convolution: b) % 7)
]

{ #category : #'as yet unclassified' }
TupleTest >> testModTupleOperations [
	| a b modulus |
	modulus := 10 atRandom + 1.
	'a := ZZ^5 atRandomBits: 30.
		b := ZZ^5 atRandomBits: 30'.
	#(+ - convolution: dot: hadamard:) do: [:op|
		self testTuple: a with: b operation: op modulo: modulus].
	#(negated reversed copy sum product) do: [:op|
		self testTuple: a operation: op modulo: modulus].
]

{ #category : #'as yet unclassified' }
TupleTest >> testModTupleSum [
	| a b |
	a := ZZ tuple: ((1 to: 10) collect: [:i| 100 atRandom]).
	b := a % 7.
	self assert: b sum = (a sum % 7)
]

{ #category : #'as yet unclassified' }
TupleTest >> testTuple: a operation: aSymbol modulo: modulus [
	self assert: (a perform: aSymbol) % modulus = (a % modulus perform: aSymbol)
]

{ #category : #'as yet unclassified' }
TupleTest >> testTuple: a with: b operation: aSymbol modulo: modulus [
	self assert: (a perform: aSymbol with: b) % modulus = (a % modulus perform: aSymbol with: b % modulus)
]

{ #category : #'as yet unclassified' }
TupleTest >> testTupleSum [
	self assert: (1,2,3) sum = (1 + 2 + 3)
]

{ #category : #'as yet unclassified' }
TupleTest >> testTuplesModuleMembership [
	self assert: ('QQ^3' includes: (1,2,3)).
	self assert: ('QQ^3' includes: (1,2,3,4)) not
]
