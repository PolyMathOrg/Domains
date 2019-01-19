Class {
	#name : #AbstractPermutation,
	#superclass : #Morphism,
	#category : #'Mathematics-Groups-Permutations'
}

{ #category : #accessing }
AbstractPermutation >> aChange [
	"Answer an element changed by the receiver (or nil if there are no one)."

	self changesDo: [ :each | ^ each].
	^ nil
]

{ #category : #converting }
AbstractPermutation >> asStandard: anArray [
	^ StandardPermutation map: (anArray collect: [:each| anArray indexOf: (self at: each)])
]

{ #category : #accessing }
AbstractPermutation >> changes [
	"Answer the elements changed by the receiver."
	^ Iterator on: self performing: #changesDo:
]

{ #category : #accessing }
AbstractPermutation >> codomain [
	^ self domain
]

{ #category : #operations }
AbstractPermutation >> commutator: aPermutation [
	^ self inverse * aPermutation inverse * self * aPermutation
]

{ #category : #operations }
AbstractPermutation >> conjugateBy: aPermutation [
	^ aPermutation inverse * self * aPermutation
]

{ #category : #cycles }
AbstractPermutation >> cycles [
	"Answer the cycles of the receiver."
	^ Iterator on: self performing: #cyclesDo:
]

{ #category : #cycles }
AbstractPermutation >> cyclesDo: aBlock [
	"Iterate over the cycles of the receiver."
	| left first next cycle |
	left := self changes copyAs: Set.
	[left size > 0] whileTrue:
		[first := left anyOne.
		cycle := OrderedCollection new.
		next := first.
		[(cycle add: (left remove: (next := self at: next))) ~= first] whileTrue.
		aBlock value: cycle]
]

{ #category : #testing }
AbstractPermutation >> even [
	^ self sign = 1
]

{ #category : #testing }
AbstractPermutation >> hasLeftInverse [
	^ true
]

{ #category : #testing }
AbstractPermutation >> hasRightInverse [
	^ true
]

{ #category : #testing }
AbstractPermutation >> is: aSymbol [
	^ aSymbol == #Permutation or: [super is: aSymbol]
]

{ #category : #testing }
AbstractPermutation >> isConjugateWith: aPermutation [
	"Answer true if the receiver and the argument are conjugate."

	^ self type = aPermutation type
]

{ #category : #testing }
AbstractPermutation >> isCycle [
	"Answer true if the receiver is a cycle."

	^ self cycles size = 1
]

{ #category : #testing }
AbstractPermutation >> isIdentity [
	"Answer true if the receiver is the identity permutation."

	^ self changes size = 0
]

{ #category : #testing }
AbstractPermutation >> isTransposition [
	"Answer true if the receiver is a transposition."

	^ self changes size = 2
]

{ #category : #operations }
AbstractPermutation >> leftInverse [
	^ self inverse
]

{ #category : #testing }
AbstractPermutation >> odd [
	^ self sign = -1
]

{ #category : #accessing }
AbstractPermutation >> one [
	^ self identity
]

{ #category : #accessing }
AbstractPermutation >> order [
	self isIdentity ifTrue: [^ 1].
	^ self cycles inject: 1 into: [:last :each| last lcm: each size]
]

{ #category : #accessing }
AbstractPermutation >> order2 [
	| answer next |
	answer := 1.
	next := self.
	[next isIdentity] whileFalse: [next := next * self. answer := answer + 1].
	^ answer
]

{ #category : #actions }
AbstractPermutation >> permute: anArray [
	"Answer the permutation of the elements of anArray induced by the receiver."
	| answer |
	answer := Array new: anArray size.
	1 to: anArray size do: [:i| answer at: i put: (anArray at: (self at: i))].
	^ answer
]

{ #category : #printing }
AbstractPermutation >> printOn: aStream [
	"Print a representation of the receiver on the stream aStream."

	self isIdentity ifTrue: [aStream nextPutAll: 'id'. ^ self].
	self cyclesDo: [:cycle|
		aStream nextPut: $(.
		cycle do: [:element| element isSymbol ifTrue: [aStream nextPutAll: element] ifFalse: [aStream print: element]] separatedBy: [aStream space].
		aStream nextPut: $)]
]

{ #category : #operations }
AbstractPermutation >> quotequote: aPermutation [ "î "
	"Answer the composition of the receiver with the argument."
	^ self * aPermutation
]

{ #category : #operations }
AbstractPermutation >> raiseTo: anInteger [
	^ self îî anInteger
]

{ #category : #operations }
AbstractPermutation >> reciprocal [
	^ self inverse
]

{ #category : #operations }
AbstractPermutation >> rightInverse [
	^ self inverse
]

{ #category : #accessing }
AbstractPermutation >> sign [
	| answer |
	answer := 1.
	self cyclesDo: [:each| each size even ifTrue: [answer := answer * -1]].
	^ answer

	"^ self transpositions size even ifTrue: [1] ifFalse: [-1]"
]

{ #category : #accessing }
AbstractPermutation >> type [
	"Answer the type of the receiver."
	^ (self cycles asSortedCollection: [ :a :b | a size <= b size]) collect: [ :each | each size]
]

{ #category : #actions }
AbstractPermutation >> value: anObject [
	^ self at: anObject
]
