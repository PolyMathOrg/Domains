Class {
	#name : #AbelianGroupTest,
	#superclass : #TestCase,
	#category : #MathematicsTests
}

{ #category : #'as yet unclassified' }
AbelianGroupTest >> testAbelianGroup: G [
	| zero a b c |
	zero := G identity.
	a := G atRandomBits: 100.
	b := G atRandomBits: 100.
	c := G atRandomBits: 100.
	self assert: zero + a = a.
	self assert: a + zero = a.
	self assert: a + b = (b + a). "commutativity"
	self assert: (a + b + c) = (a + (b + c)). "associativity"
]

{ #category : #'as yet unclassified' }
AbelianGroupTest >> testAbelianGroupHomomorphism: phi [
	| G H a b |
	G := phi domain.
	H := phi codomain.
	a := G atRandomBits: 100.
	b := G atRandomBits: 100.
	self assert: (phi value: G identity) = H identity.
	self assert: (phi value: a + b) = ((phi value: a) + (phi value: b))
]

{ #category : #'as yet unclassified' }
AbelianGroupTest >> testDirectSum [
	| G |
	G := ZZ asAbelianGroup "Í" directSum: (ZZ / (2 to: 10) atRandom) asAbelianGroup.
	self testAbelianGroup: G.
	self testAbelianGroupHomomorphism: (G projection: 2 atRandom).
	self testAbelianGroupHomomorphism: (G embedding: 2 atRandom)
]

{ #category : #'as yet unclassified' }
AbelianGroupTest >> testIntegerTuples [
	| M |
	M := 'ZZ ^ (1 to: 10) atRandom'.
	self testAbelianGroup: M asAbelianGroup.
	self testAbelianGroupHomomorphism: (M projection: (1 to: M rank) atRandom) asAbelianGroupHomomorphism
]

{ #category : #'as yet unclassified' }
AbelianGroupTest >> testIntegers [
	self testAbelianGroup: ZZ asAbelianGroup
]

{ #category : #'as yet unclassified' }
AbelianGroupTest >> testModularIntegers [
	| R |
	R := ZZ / (2 to: 10) atRandom.
	self testAbelianGroup: R asAbelianGroup.
	self testAbelianGroupHomomorphism: R projection asAbelianGroupHomomorphism
]
