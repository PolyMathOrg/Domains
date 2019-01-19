"
Abelian groups with a basis. They can be viewed also as free Z-modules. They are isomorphic to Z^n (this is, they are torsion-free).
"
Class {
	#name : #FreeAbelianGroup,
	#superclass : #AbelianGroup,
	#category : #'Mathematics-Groups-Abelian'
}

{ #category : #'instance creation' }
FreeAbelianGroup class >> new: anInteger [
	^ self new generators: ('ZZ^anInteger') generators
]

{ #category : #accessing }
FreeAbelianGroup >> identity [
	self isTrivial ifTrue: [^ ZZ tuple: #()].
	^ super identity
]

{ #category : #testing }
FreeAbelianGroup >> isInfiniteCyclic [
	^ self basis size = 1
]

{ #category : #testing }
FreeAbelianGroup >> isTrivial [
	^ self generators size = 0
]

{ #category : #accessing }
FreeAbelianGroup >> presentation [
	| commutators |
	commutators := OrderedCollection new.
	self generators do: [:x|
		self generators do: [:y|
			commutators add: x * y * x reciprocal * y reciprocal]].
	self flag: #fix. "generators are additive or multiplicative?"
	^ GroupPresentation generators: self basis relators: commutators
]

{ #category : #printing }
FreeAbelianGroup >> printOn: aStream [
	self isTrivial ifTrue: [^ super printOn: aStream].
	aStream nextPut: Character ZZ.
	self rank > 0 ifTrue: [aStream nextPutAll: self rank printString super].
]

{ #category : #accessing }
FreeAbelianGroup >> rank [
	^ self generators size
]

{ #category : #accessing }
FreeAbelianGroup >> size [
	^ self rank = 0 ifTrue: [1] ifFalse: [Aleph new: 0]
]

{ #category : #private }
FreeAbelianGroup >> species [
	"Any subgroup of a free abelian group is also free."
	^ FreeAbelianGroup
]

{ #category : #accessing }
FreeAbelianGroup >> torsion [
	^ self null
]
