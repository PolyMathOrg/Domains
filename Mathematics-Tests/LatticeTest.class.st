Class {
	#name : #LatticeTest,
	#superclass : #TestCase,
	#category : #'Mathematics-Tests'
}

{ #category : #'as yet unclassified' }
LatticeTest >> testE8 [
	| E8 a |
	E8 := Lattice E8.
	a := E8 atRandomBits: 100.
	self assert: ((a allSatisfy: [:x| x isInteger]) or: [a allSatisfy: [:x| x isInteger not and: [(x*2) isInteger]]]).
	self assert: (a sum isInteger and: [a sum even]).
	self assert: E8 isIntegral.
	self assert: E8 isUnimodular.
	self assert: E8 isEven.
	self assert: E8 isSelfDual
]

{ #category : #accessing }
LatticeTest >> testLLL [
	| b1 b2 b3 lll |
	b1 := 1 , 1 , 1.
	b2 := -1 , 0 , 2.
	b3 := 3 , 5 , 6.
	lll := LLL
		basis:
			{b1.
			b2.
			b3}.
	self
		assert: lll reducedBasis
		equals:
			{(0 , 1 , 0).
			(1 , 0 , 1).
			(-1 , 0 , 2)}
]

{ #category : #accessing }
LatticeTest >> testLatticeAnDual [
	| A3 D |
	A3 := Lattice A: 3.
	D := Lattice Adual: 3.
	self assert: A3 reciprocal equals: D.
	self assert: A3 equals: D reciprocal
]

{ #category : #'as yet unclassified' }
LatticeTest >> testLatticeD4SelfDual [
	| D4 |
	D4 := Lattice D4.
	self assert: D4 isSelfDual
]

{ #category : #accessing }
LatticeTest >> testLatticeDnDual [
	| D R |
	D := Lattice D: 5.
	R := Lattice Ddual: 5.
	self assert: D reciprocal equals: R.
	self assert: D equals: R reciprocal
]

{ #category : #accessing }
LatticeTest >> testLatticeDual [
	| L R I |
	L := Lattice
		basis:
			{(-1 , 0 , 0).
			(0 , 1 , 2).
			(0 , 1 , 1)}.
	R := L reciprocal.
	I := L matrix identity.
	self
		assert: (L ambient span: L basis)
		equals: (R ambient span: R basis).
	self assert: L determinant equals: 1 / R determinant.
	self assert: R matrix * L matrix transposed equals: I
]

{ #category : #accessing }
LatticeTest >> testLatticeDual2 [
	| L R |
	L := Lattice
		basis:
			{(-1 , 0 , 0).
			(0 , 1 , 2)}.	"not full rank"
	R := L reciprocal.
	self
		assert: (L ambient span: L basis)
		equals: (R ambient span: R basis).
	self assert: L determinant equals: 1 / R determinant.
	self assert: (R matrix * L matrix transposed) isIdentity
]

{ #category : #accessing }
LatticeTest >> testLeech [
	| L |
	L := Lattice leech.
	"	a := L atRandomBits: 100.
		self assert: ((a allSatisfy: [:x| x isInteger]) or: [a allSatisfy: [:x| x isInteger not and: [(x*2) isInteger]]]).
		self assert: (a sum isInteger and: [a sum even])."
	self assert: L determinant equals: 1.
	self assert: L kissingNumber equals: 196560.
	self assert: L minimalNorm equals: 4.
	self assert: L isIntegral.
	self assert: L isUnimodular.
	self assert: L isEven
]
