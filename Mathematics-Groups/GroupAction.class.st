"
(Left) group actions.

Given a group G and a set X, a (left) group action phi:GxX -> X is a function that satisfies:
- identity: phi(id,x) = x;
- compatibility: phi(g, phi(h,x)) = phi(g*h, x).

The group G is said to 'act' on X (on the left). The set X is called a (left) G-set (or G-space, G-module, depending on the category of X). Here we just call it 'space'.

References:
	https://en.wikipedia.org/wiki/Group_action
"
Class {
	#name : #GroupAction,
	#superclass : #Function,
	#category : #'Mathematics-Groups'
}

{ #category : #graphs }
GroupAction >> actionGraph: groupGenerators [
	"Answer the action diagram with respect to the given group generators.
	This is similar to a Cayley diagram.
	The connected components of the action diagram are the orbits of the action."
	| G |
	self space isFinite ifFalse: [^ self error: 'not a finite space'].
	G := Digraph unorderedLabeled.
	groupGenerators do: [:g|
		self space do: [:x|
			G addEdgeFrom: x to: (self value: {g.x}) label: g]].
	^ G
]

{ #category : #graphs }
GroupAction >> actionGraphMorph [
	^ self actionGraphMorph: self group generators
]

{ #category : #graphs }
GroupAction >> actionGraphMorph: generators [
	| G answer colors |
	G := self actionGraph: generators.
	answer := G asMorph.
	colors := DiscretePalette default.
	answer edgesAndLabelsDo: [:each :label| each hideLabel; color: (colors at: label)].
	answer nodesDo: [:each| each color: Color transparent; radius: 0].
	^ answer
]

{ #category : #converting }
GroupAction >> asPermutationRepresentation [
	| S |
	S := SymmetricGroup on: self space.
	^ GroupRepresentation
		from: self group
		to: S
		evaluating: [:g| S evaluating: [:x| self value: {g.x}]]
]

{ #category : #converting }
GroupAction >> asRepresentation [
	^ GroupRepresentation
		from: self group
		to: self space automorphisms
		evaluating: [:g| self space to: self space evaluating: [:x| self value: {g.x}]]
]

{ #category : #accessing }
GroupAction >> degree [
	^ self space size
]

{ #category : #accessing }
GroupAction >> fixedPoints [
	^ self space select: [:each| self isFixedPoint: each]
]

{ #category : #accessing }
GroupAction >> fixedPointsOf: anElement [
	"Dual idea to the stabilizer. The fixed points are the orbits of size 1."
	^ self space select: [:each| (self value: {anElement. each}) = each]
]

{ #category : #accessing }
GroupAction >> group [
	^ self domain at: 1
]

{ #category : #testing }
GroupAction >> isFaithful [
	"A group action G x X -> X is faithful (or effective) if the homomorphism G -> Sym(X) has trivial kernel {id}."
	^ self propertyAt: #isFaithful ifAbsentPut: [self kernel isTrivial]
]

{ #category : #testing }
GroupAction >> isFixedPoint: aPoint [
	"Answer true if the argument is a fixed point of the receiver."
	self group do: [:each| (self value: {each. aPoint}) = aPoint ifFalse: [^ false]].
	^ true
]

{ #category : #testing }
GroupAction >> isImprimitive [
	^ self isPrimitive not
]

{ #category : #testing }
GroupAction >> isPrimitive [
	^ self orbits allSatisfy: [:each| each size = 1 or: [each size = self space size]]
]

{ #category : #testing }
GroupAction >> isRegular [
	^ self isTransitive and: [(self stabilizerOf: self space anyOne) isTrivial]
]

{ #category : #testing }
GroupAction >> isTransitive [
	^ self orbits size = 1
]

{ #category : #accessing }
GroupAction >> kernel [
	"This is also the intersection of all the stabilizers."
	^ self group select: [:g| self space allSatisfy: [:x| (self value: {g.x}) = x]]
	"^ self asPermutationRepresentation kernel"
]

{ #category : #accessing }
GroupAction >> orbitOf: aPoint [
	"Answer the set of points to which aPoint can be 'moved' by elements of the group G.
	All the orbits form a partition of the underlying set (space) X, and it's written X/G and called the quotient of the action. In geometric situations it may be called the orbit space, and in algebraic situations it is called the space of coinvariants (in contrast with the space of invariants, that are the fixed points)."
	| answer |
	self group generators
		ifNotNil: [:S| ^ (SchreierTree root: aPoint generators: S action: self) orbit].
	answer := Set new.
	self group do: [:each| answer add: (self value: {each. aPoint})].
	^ answer
]

{ #category : #accessing }
GroupAction >> orbits [
	"Answer the quotient of the action, also called space of orbits in geometric situations and space of coinvariants in algebraic situations."
	| answer |
	answer := Set new.
	self space do: [:each| answer add: (self orbitOf: each)].
	^ answer
]

{ #category : #accessing }
GroupAction >> reynolds [
	"Answer the Reynolds operator, assuming the group acts on a polynomial ring S.
	Properties:
	- K-linear map S -> S^G (it's the G-invariant projection from S to S^G;
	- restricts to the identity on S^G;
	- it's an S^G-module homomorphisms: R(p*q) = p*R(q) for all invariants p in S^G."
	| order |
	order := self group size.
	^ self space to: self space evaluating: [:p| (self group elements sum: [:g| self value: {g. p}]) / order]
]

{ #category : #accessing }
GroupAction >> space [
	"Answer the underlying set X of the action G x X -> X."
	^ self codomain
]

{ #category : #accessing }
GroupAction >> stabilizerOf: aPoint [
	"Answer the stabilizer subgroup (or isotropy group or little group) of aPoint, defined as the set of elements that 'fix' aPoint. The stabilizer of fixed points is the whole group, and the kernel of the action homomorphism G -> Sym(X) is the intersection of all stabilizers."
	self group generators
		ifNotNil: [:S| ^ (SchreierTree root: aPoint generators: S action: self) stabilizer].
	^ self group select: [:each| (self value: {each. aPoint}) = aPoint]
]
