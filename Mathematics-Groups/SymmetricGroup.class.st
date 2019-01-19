"
The symmetric group Sym(X) of permutations on the elements of a set X (which we call 'space'). This is the ambient of all PermutationGroups.
"
Class {
	#name : #SymmetricGroup,
	#superclass : #PermutationGroup,
	#category : #'Mathematics-Groups-Permutations'
}

{ #category : #examples }
SymmetricGroup class >> example1 [
	"The group of permutations on the set of 3 elements {1,2,3}."
	^ SymmetricGroup new: 3
]

{ #category : #examples }
SymmetricGroup class >> example2 [
	"The group of permutations on the set {a,b,c}."
	^ SymmetricGroup on: #(a b c).
]

{ #category : #'instance creation' }
SymmetricGroup class >> new: anInteger [
	^ StandardSymmetricGroup new: anInteger
]

{ #category : #'instance creation' }
SymmetricGroup class >> on: aCollection [
	^ self new space: aCollection
]

{ #category : #elements }
SymmetricGroup >> ! anObject [
	"Coerce anObject to an element of the receiver (a permutation)."
	anObject isEvaluable
		ifTrue: [^ self evaluating: anObject].
	anObject isSequenceable
		ifFalse: [^ super ! anObject].
	(anObject allSatisfy: [:each| each isSequenceable]) "cycles"
		ifTrue: [^ self cycles: anObject].
	^ super ! anObject
]

{ #category : #comparing }
SymmetricGroup >> >= anObject [
	(anObject isKindOf: PermutationGroup)
		ifTrue: [^ self space >= anObject space].
	^ super >= anObject
]

{ #category : #accessing }
SymmetricGroup >> ambient [
	^ self
]

{ #category : #random }
SymmetricGroup >> atRandom: aRandom [
	| domain |
	domain := self space asArray.
	^ Permutation keys: domain values: (domain shuffledBy: aRandom)
]

{ #category : #random }
SymmetricGroup >> atRandom: aRandom bits: bits [
	^ self atRandom: aRandom
]

{ #category : #operations }
SymmetricGroup >> commutator [
	^ AlternatingGroup on: space
]

{ #category : #private }
SymmetricGroup >> computeGenerators [
	| answer X |
	answer := OrderedCollection new.
	X := self space asArray.
	2 to: X size do: [:i| answer add: (self transposing: (X at: 1) with: (X at: i))].
	^ answer
"alternatively: Coxeter generators, the set of (i,i+1) all the adjacent transpositions"
]

{ #category : #testing }
SymmetricGroup >> contains: aPermutation [
	"Answer true if the receiver contains the given element of its ambient."
	^ true
]

{ #category : #elements }
SymmetricGroup >> cycle: anArray [
	^ Permutation cycle: anArray
]

{ #category : #elements }
SymmetricGroup >> cycles: anArray [
	^ Permutation cycles: anArray
]

{ #category : #accessing }
SymmetricGroup >> degree [
	^ self space size
]

{ #category : #enumerating }
SymmetricGroup >> do: aBlock [
	| domain |
	domain := self space asArray.
	domain permutationsDo: [:each| aBlock value: (Permutation keys: domain values: each)]
]

{ #category : #elements }
SymmetricGroup >> evaluating: aBlock [
	^ Permutation on: self space evaluating: aBlock
]

{ #category : #elements }
SymmetricGroup >> identity [
	^ self propertyAt: #identity ifAbsentPut: [Permutation new]
]

{ #category : #testing }
SymmetricGroup >> includes: anObject [
	^ (anObject isKindOf: Permutation) and: [anObject domain <= self space]
]

{ #category : #testing }
SymmetricGroup >> isAlmostSimple [
	^ self degree >= 5
]

{ #category : #testing }
SymmetricGroup >> isStandard [
	"Answer true if the domain of the receiver is an interval [1..n]."
	^ false
]

{ #category : #printing }
SymmetricGroup >> printOn: aStream [
	aStream nextPutAll: 'Sym('; print: self space; nextPut: $)
]

{ #category : #accessing }
SymmetricGroup >> size [
	^ self degree factorial
]

{ #category : #accessing }
SymmetricGroup >> space [
	^ self propertyAt: #space
]

{ #category : #private }
SymmetricGroup >> space: aCollection [
	self propertyAt: #space put: aCollection
]

{ #category : #operations }
SymmetricGroup >> span: aCollection [
	^ PermutationGroup new ambient: self; generators: (aCollection collect: [:each| self ! each])
]

{ #category : #elements }
SymmetricGroup >> transposing: anObject with: anotherObject [
	"Answer the tranposition of anObject with anotherObject."
	^ Permutation transposing: anObject with: anotherObject
]
