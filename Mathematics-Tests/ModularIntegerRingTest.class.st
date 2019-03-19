"
A ModularIntegerRingTest is a test class for testing the behavior of ModularIntegerRing
"
Class {
	#name : #ModularIntegerRingTest,
	#superclass : #TestCase,
	#category : #'Mathematics-Tests'
}

{ #category : #tests }
ModularIntegerRingTest >> testModularTestRing [
	"Reproduce example from SAGE
	 http://doc.sagemath.org/html/en/tutorial/tour_numtheory.html"

	| r a b |
	r := ModularIntegerRing new: 97.
	a := (r project: 2) / (r project: 3).
	self assert: a representative equals: 33.
	self assert: a asRational equals: 2 / 3.
	b := r project: 47.
	self assert: (b raisedTo: 20052005) representative equals: 50.
	self assert: b modulus equals: 97
]
