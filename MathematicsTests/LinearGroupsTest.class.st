Class {
	#name : #LinearGroupsTest,
	#superclass : #TestCase,
	#category : #MathematicsTests
}

{ #category : #'as yet unclassified' }
LinearGroupsTest >> testGeneralLinearAtRandom [
	| V G |
	V := 'QQ ^ 3'.
	G := V automorphisms.
	self assert: (G atRandomBits: 100) isInvertible.
	self assert: (G includes: (G atRandomBits: 100))
]

{ #category : #'as yet unclassified' }
LinearGroupsTest >> testOrthogonalAtRandom [
	| V G |
	V := 'QQ ^ 3'.
	G := V automorphisms orthogonal.
	self assert: (G atRandomBits: 100) isOrthogonal.
	self assert: (G includes: (G atRandomBits: 100))
]

{ #category : #'as yet unclassified' }
LinearGroupsTest >> testRotationsBy90Degrees [
	"Group of rotations by 90 degrees in the plane, isomorphic to Z/4Z."
	| V G |
	V := 'QQ ^ 2'.
	G := (LinearGroup on: V) generators: {V endomorphisms elementAt: (0, 1, -1, 0)}.
	self assert: G size = 4.
	self assert: G isCyclic.
	self flag: #todo.
	"test invariant ring K[x,y]^G = K[x^2+y^2, x^2y^2, x^3y-xy^3], isomorphic to K[a,b,c]/<c^2-a^2b+4b^2>"
	"test hilbert series is 1-z^8 / ((1-z^2)^2(1-z^4)) = 1 + z^2 + 3z^4 + 3z^6 + ..."
]
