Class {
	#name : #PAdicsTest,
	#superclass : #TestCase,
	#category : #MathematicsTests
}

{ #category : #'as yet unclassified' }
PAdicsTest >> testPAdicNorm [
	| Z7 x |
	Z7 := AdicIntegerRing p: 2.
	x := Z7 embed: 7.
	self assert: x valuation = 0.
	self assert: x norm = 1.
	x := x * 4.
	self assert: x valuation = 2.
	self assert: x norm = (1/4)
]
