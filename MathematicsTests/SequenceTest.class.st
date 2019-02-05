Class {
	#name : #SequenceTest,
	#superclass : #TestCase,
	#category : #MathematicsTests
}

{ #category : #tests }
SequenceTest >> testBellNumbers [
	self
		assert: (Sequence bellNumbers beginsWith: #(1 2 5 15 52 203 877)).
	"The binomial transform is the shift operator for the Bell numbers:"
	self
		assert:
			(Sequence bellNumbers binomialTransform2
				beginsWith: #(2 5 15 52 203 877))
]

{ #category : #tests }
SequenceTest >> testBernoulliNumbers [
	self
		assert:
			(Sequence bernoulli
				beginsWith: {1. -1/2. 1/6. 0. -1/30. 0. 1/42.})
]

{ #category : #tests }
SequenceTest >> testDirichletConvolution [
	self
		assert: ((Sequence phi dirichlet: Sequence one) beginsWith: #(1 2 3 4 5)).
	self
		assert: ((Sequence moebius dirichlet: Sequence one) beginsWith: #(1 0 0 0 0))
]

{ #category : #tests }
SequenceTest >> testLinearRecursiveSequenceBug [
	| F |
	F := CFiniteSequence fibonacci.
	self assert: (F - F at: 1) equals: 0
]

{ #category : #tests }
SequenceTest >> testPowerSeries [
	| cos sin |
	sin := PowerSeries sin.
	cos := PowerSeries cos.
	self
		assert:
			((cos squared + sin squared) coefficients
				beginsWith: #(1 0 0 0 0 0 0 0 0))
]

{ #category : #tests }
SequenceTest >> testRecursive [
	| f g |
	f := Sequence fibonacci.
	g := CFiniteSequence to: ZZ evaluating: f maxOrder: 5.
	self assert: (f equals: g upTo: 20).
	self assert: g order equals: 2.
	self
		assert: g characteristicPolynomial coefficients asArray
		equals: #(-1 -1 1)
]

{ #category : #tests }
SequenceTest >> testRecursive2 [
	| a b c |
	a := CFiniteSequence fibonacci.
	b := CFiniteSequence lucasNumbers.
	c := a + (b * 2) - (b + b).
	self assert: a equals: c
]

{ #category : #tests }
SequenceTest >> testRecursiveConvolution [
	| a b c a2 b2 c2 |
	a := CFiniteSequence fibonacci.
	b := CFiniteSequence lucasNumbers.
	a2 := Sequence evaluating: [ :i | a at: i ].
	b2 := Sequence evaluating: [ :i | b at: i ].
	c := a convolution: b.
	c2 := a2 convolution: b2.
	self assert: (c equals: c2 upTo: 20)
]

{ #category : #tests }
SequenceTest >> testRecursiveEquals [
	| a b c |
	a := CFiniteSequence fibonacci.
	b := CFiniteSequence to: ZZ evaluating: [ :i | a at: i ] maxOrder: 10.
	c := CFiniteSequence lucasNumbers.
	self assert: a equals: b.
	self assert: a ~= c
]

{ #category : #tests }
SequenceTest >> testRecursiveIndefiniteSumation [
	| a c a2 c2 |
	a := CFiniteSequence fibonacci.
	a2 := Sequence evaluating: [ :i | a at: i ].
	c := a sum.
	c2 := a2 sum.
	self assert: (c isKindOf: CFiniteSequence).
	self assert: (c equals: c2 upTo: 20)
]

{ #category : #tests }
SequenceTest >> testRecursiveMinimal [
	| a f |
	a := CFiniteSequence initialValues: #(0 1 1) coefficients: #(0 1 1).
	f := CFiniteSequence fibonacci.
	self assert: a isMinimal not.
	self assert: a order equals: 3.
	self assert: a minimal order equals: 2.
	self assert: a minimalPolynomial equals: f characteristicPolynomial
]

{ #category : #tests }
SequenceTest >> testRecursiveProduct [
	| a b c c2 |
	a := CFiniteSequence fibonacci.
	b := CFiniteSequence pellNumbers.
	c := a * b.
	c2 := Sequence evaluating: [ :i | (a at: i) * (b at: i) ].
	self assert: (c isKindOf: CFiniteSequence).
	self assert: (c equals: c2 upTo: 20).
	self assert: c order equals: 4
]

{ #category : #tests }
SequenceTest >> testRecursiveScalarMultiplication [
	| a c a2 c2 |
	a := CFiniteSequence fibonacci.
	a2 := Sequence evaluating: [ :i | a at: i ].
	c := a * 7.
	c2 := a2 * 7. 
	self assert: (c isKindOf: CFiniteSequence).
	self assert: (c equals: c2 upTo: 20)
]

{ #category : #tests }
SequenceTest >> testRecursiveShiftLeft [
	| a c a2 c2 |
	a := CFiniteSequence fibonacci.
	a2 := Sequence evaluating: [ :i | a at: i ].
	c := a << 5.
	c2 := a2 << 5.
	self assert: (c isKindOf: CFiniteSequence). 
	self assert: (c equals: c2 upTo: 20)
]

{ #category : #tests }
SequenceTest >> testRecursiveSum [
	| a b c c2 |
	a := CFiniteSequence fibonacci.
	b := CFiniteSequence lucasNumbers.
	c := a + b.
	c2 := Sequence evaluating: [ :i | (a at: i) + (b at: i) ].
	self assert: (c isKindOf: CFiniteSequence).
	self assert: (c equals: c2 upTo: 20) 
]
