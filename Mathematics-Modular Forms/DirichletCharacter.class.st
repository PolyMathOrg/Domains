"
Characters on the units of Z/nZ, i.e. group homomorphisms (Z/nZ)* -> C* from the unit group of the ring Z/nZ to the multiplicative group of nonzero complex numbers.
"
Class {
	#name : #DirichletCharacter,
	#superclass : #GroupMap,
	#category : #'Mathematics-Modular Forms'
}

{ #category : #'as yet unclassified' }
DirichletCharacter >> conductor [
	| factors p e answer |
	(self modulus = 1 or: [self isTrivial]) ifTrue: [^ 1].
	(factors := self modulus factors) asSet size > 1
		ifTrue: [^ self decomposition product: [:each| each conductor]].
	p := factors anyOne.
	e := factors size.
	answer := 'p ^ ((self size valuation: p) + 1)'.
"	p = 2 and: [e > 2 and: [ ..."
	^ answer
]

{ #category : #'as yet unclassified' }
DirichletCharacter >> even [
	^ (self value: -1 % self modulus) = self codomain one
]

{ #category : #'as yet unclassified' }
DirichletCharacter >> isPrimitive [
	^ self conductor = self modulus
]

{ #category : #'as yet unclassified' }
DirichletCharacter >> modulus [
	^ self domain modulus
]

{ #category : #'as yet unclassified' }
DirichletCharacter >> odd [
	^ (self value: -1 % self modulus) = self codomain one negated
]
