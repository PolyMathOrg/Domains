"
An equivalence relation on X is a binary relation ~ on X with the following properties:
- For every element a in X, a ~ a (reflexivity);
- For every two elements a, b in X, if a ~ b then b ~ a (symmetry);
- For every three elements a, b, c in X, if a ~ b and b ~ c then a ~ c (transitivity).

See EquivalenceClass.

References:
	https://en.wikipedia.org/wiki/Equivalence_relation
"
Class {
	#name : #EquivalenceRelation,
	#superclass : #Domain,
	#category : #'Mathematics-Sets'
}

{ #category : #'instance creation' }
EquivalenceRelation class >> on: aDomain evaluating: aBlock [
	^ self new domain: aDomain; block: aBlock
]

{ #category : #'accessing-private' }
EquivalenceRelation >> block: aBlock [
	self propertyAt: #block put: aBlock
]

{ #category : #enumerating }
EquivalenceRelation >> do: aBlock [
	self domain do: [:x|
		self domain do: [:y|
			| r |
			(self includes: (r := {x.y})) ifTrue: [aBlock value: r]]]
]

{ #category : #accessing }
EquivalenceRelation >> domain [
	^ self propertyAt: #domain
]

{ #category : #'accessing-private' }
EquivalenceRelation >> domain: aDomain [
	self propertyAt: #domain put: aDomain
]

{ #category : #testing }
EquivalenceRelation >> includes: anArray [
	^ (self propertyAt: #block) valueWithArguments: anArray
]

{ #category : #testing }
EquivalenceRelation >> isReflexive [
	^ true
]

{ #category : #testing }
EquivalenceRelation >> isSymmetric [
	^ true
]

{ #category : #testing }
EquivalenceRelation >> isTransitive [
	^ true
]

{ #category : #printing }
EquivalenceRelation >> printOn: aStream [
	((self hasProperty: #name) or: [self hasProperty: #elements])
		ifTrue: [^ super printOn: aStream].
	aStream nextPut: $~
]
