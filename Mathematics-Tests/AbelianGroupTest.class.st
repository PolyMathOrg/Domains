Class {
	#name : #AbelianGroupTest,
	#superclass : #TestCase,
	#category : #'Mathematics-Tests'
}

{ #category : #tests }
AbelianGroupTest >> testAbelianGroup: G [
	| zero a b c |
	zero := G identity.
	a := G atRandomBits: 100.
	b := G atRandomBits: 100.
	c := G atRandomBits: 100.
	self assert: zero + a equals: a.
	self assert: a + zero equals: a.
	self assert: a + b equals: b + a.
	self assert: a + b + c equals: a + (b + c)
]

{ #category : #tests }
AbelianGroupTest >> testAbelianGroupHomomorphism: phi [
	| G H a b |
	G := phi domain.
	H := phi codomain.
	a := G atRandomBits: 100.
	b := G atRandomBits: 100.
	self assert: (phi value: G identity) equals: H identity.
	self
		assert: (phi value: a + b)
		equals: (phi value: a) + (phi value: b)
]

{ #category : #tests }
AbelianGroupTest >> testDirectSum [
	| G |
	G := ZZ asAbelianGroup
		directSum: (ZZ / (2 to: 10) atRandom) asAbelianGroup.	"Í"
	self testAbelianGroup: G.
	self testAbelianGroupHomomorphism: (G projection: 2 atRandom).
	self testAbelianGroupHomomorphism: (G embedding: 2 atRandom)
]

{ #category : #tests }
AbelianGroupTest >> testIntegerTuples [
	| M |
	M := ZZ raisedTo: ((1 to: 10) atRandom).
	self testAbelianGroup: M asAbelianGroup.
	self
		testAbelianGroupHomomorphism: (M projection: (1 to: M rank) atRandom) asAbelianGroupHomomorphism
]

{ #category : #tests }
AbelianGroupTest >> testIntegers [
	self testAbelianGroup: ZZ asAbelianGroup
]

{ #category : #tests }
AbelianGroupTest >> testModularIntegers [
	| R |
	R := ZZ / (2 to: 10) atRandom.
	self testAbelianGroup: R asAbelianGroup.
	self
		testAbelianGroupHomomorphism: R projection asAbelianGroupHomomorphism
]
