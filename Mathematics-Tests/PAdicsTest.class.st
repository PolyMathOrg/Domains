Class {
	#name : #PAdicsTest,
	#superclass : #TestCase,
	#category : #'Mathematics-Tests'
}

{ #category : #tests }
PAdicsTest >> testPAdicNorm [
	| Z7 x |
	Z7 := AdicIntegerRing p: 2.
	x := Z7 embed: 7.
	self assert: x valuation equals: 0.
	self assert: x norm equals: 1.
	x := x * 4.
	self assert: x valuation equals: 2.
	self assert: x norm equals: 1 / 4
]
