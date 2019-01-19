"
Given a group and an object X, a group representation is a group homomorphism from G to the automorphisms group Aut(X). X is called the representation space. Informally speaking, a representation allows us to view a group as symmetries of an object.

For example, a linear representation of a group G on a vector space V is a group homomorphism G -> GL(V). A permutation representation of G on a set X is a group homomorphism G -> Sym(X). 
Any group action can be seen as a permutation representation. In turn, any representation phi has an associated action on the representation space that maps (g,x) -> phi(g)(x).

References:
	https://en.wikipedia.org/wiki/Group_representation
"
Class {
	#name : #GroupRepresentation,
	#superclass : #GroupMap,
	#category : #'Mathematics-Groups'
}

{ #category : #accessing }
GroupRepresentation >> action [
	"Answer the associated group action on the representation space."
	^ GroupAction from: (self domain, self space) to: self space evaluatingWithArguments: [:x :y| (self value: x) value: y]
]

{ #category : #invariants }
GroupRepresentation >> character [
	"Answer the character of the receiver, assuming it's a linear or matrix representation."
	"This is a class function, i.e. it's constant on conjugacy classes, because similar matrices (or linear maps) have the same trace."
	self space isModule ifFalse: [^ self error: 'not a linear or matrix representation'].
	^ Function from: self domain to: self space scalars evaluating: [:g| (self value: g) trace] "should be a GroupMap?"
]

{ #category : #accessing }
GroupRepresentation >> space [
	"Answer the representation space."
	^ self codomain space
]
