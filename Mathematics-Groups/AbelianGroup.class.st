"
Abelian groups can be viewed as Z-modules. They are isomorphic to Z^n x T, where T is the torsion subgroup (the subgroup of elements of finite order), and n is called the rank of the group.
"
Class {
	#name : #AbelianGroup,
	#superclass : #Group,
	#category : #'Mathematics-Groups-Abelian'
}

{ #category : #operations }
AbelianGroup >> centralizerOf: aCollection [
	^ self
]

{ #category : #operations }
AbelianGroup >> commutator: aSubgroup [
	"Answer the commutator group [G,H] of the receiver G with the argument H.
	Since the receiver is commutative, this is the trivial group."
	^ self null
]

{ #category : #private }
AbelianGroup >> defaultInverseMap [
	^ self additiveInverseMap
]

{ #category : #private }
AbelianGroup >> defaultOperation [
	^ self additiveOperation
]

{ #category : #operations }
AbelianGroup >> directSum: anAbelianGroup [
	"Answer the direct sum of the receiver and the argument."
	(anAbelianGroup isKindOf: AbelianGroup) ifFalse: [^ DomainError signal: 'argument is not an abelian group'].
	^ DirectSumGroup components: {self. anAbelianGroup}
]

{ #category : #testing }
AbelianGroup >> isAbelianGroup [
	^ true
]

{ #category : #testing }
AbelianGroup >> isInitial [
	"In the category of abelian groups the trivial group is the zero object (both initial and terminal)."
	^ self isTrivial
]

{ #category : #testing }
AbelianGroup >> isTerminal [
	"In the category of abelian groups the trivial group is the zero object (both initial and terminal)."
	^ self isTrivial
]

{ #category : #testing }
AbelianGroup >> isTorsion [
	"Answer true if the receiver is a torsion (or periodic) group, i.e. if all its elements have finite order."
	^ self torsion = self
]

{ #category : #testing }
AbelianGroup >> isTorsionFree [
	^ self torsion isTrivial
]

{ #category : #operations }
AbelianGroup >> mult: anAbelianGroup [ " ◊ "
	anAbelianGroup isAbelianGroup ifTrue: [^ self ê anAbelianGroup].
	^ 'super ◊ anAbelianGroup'
]

{ #category : #accessing }
AbelianGroup >> rank [
	^ self propertyAt: #rank
]

{ #category : #private }
AbelianGroup >> species [
	"Any subgroup of an abelian group is also abelian."
	^ AbelianGroup
]

{ #category : #morphisms }
AbelianGroup >> to: aCodomain [
	(aCodomain isAbelianGroup and: [self isTrivial or: [aCodomain isTrivial]])
		ifTrue: [^ self to: aCodomain evaluating: [:x| aCodomain identity]].
	^ super to: aCodomain
]

{ #category : #accessing }
AbelianGroup >> torsion [
	"Answer the torsion subgroup of the receiver consisting of all elements that have finite order (the torsion elements)."
	^ self propertyAt: #torsion
]
