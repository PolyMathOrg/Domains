"
The alternating group Alt(X) of even permutations on the elements of a set X (which we call 'space'). This is a subgroup of Sym(X) (see SymmetricGroup).
"
Class {
	#name : #AlternatingGroup,
	#superclass : #PermutationGroup,
	#category : #'Mathematics-Groups-Permutations'
}

{ #category : #examples }
AlternatingGroup class >> example1 [
	"The group of even permutations on the set of 3 elements {1,2,3}."
	^ AlternatingGroup new: 3
]

{ #category : #examples }
AlternatingGroup class >> example2 [
	"The group of even permutations on the set {a,b,c}."
	^ AlternatingGroup on: #(a b c).
]

{ #category : #'instance creation' }
AlternatingGroup class >> new: anInteger [
	^ self new ambient: (SymmetricGroup new: anInteger)
]

{ #category : #'instance creation' }
AlternatingGroup class >> on: aCollection [
	^ self new ambient: (SymmetricGroup on: aCollection)
]

{ #category : #random }
AlternatingGroup >> atRandom: aRandom bits: bitSize [
	| S answer |
	S := self ambient.
	[(answer := S atRandom: aRandom bits: bitSize) even] whileFalse.
	^ answer
]

{ #category : #private }
AlternatingGroup >> computeGenerators [
	| X |
	X := self space asArray.
	^ (1 to: self degree - 2) collect: [:i| self ambient cycle: {X at: i. X at: i+1. X at: i+2}]
]

{ #category : #testing }
AlternatingGroup >> contains: aPermutation [
	"Answer true if the receiver contains the given element of its ambient."
	^ aPermutation even
]

{ #category : #enumerating }
AlternatingGroup >> do: aBlock [
	self ambient do: [:each| each even ifTrue: [aBlock value: each]]
]

{ #category : #testing }
AlternatingGroup >> isSimple [
	^ self degree >= 5
]

{ #category : #printing }
AlternatingGroup >> printOn: aStream [
	aStream nextPutAll: 'Alt('; print: self space; nextPut: $)
]

{ #category : #accessing }
AlternatingGroup >> size [
	^ self degree factorial / 2
]
