"
Tensor product over R of a list of free R-modules. This is a free R-module with basis given by elementary tensors on the choice of basis of the component modules.

See Tensor.
"
Class {
	#name : #TensorProductModule,
	#superclass : #FreeModule,
	#instVars : [
		'components'
	],
	#category : #'Mathematics-Multilinear'
}

{ #category : #'instance creation' }
TensorProductModule class >> components: anArray [
	^ self new components: anArray
]

{ #category : #elements }
TensorProductModule >> ! anObject [
	(anObject isSequenceable and: [anObject size = self arity and: [(1 to: self arity) allSatisfy: [:i| (self at: i) includes: (anObject at: i)]]])
		ifTrue: [^ self compose: anObject].
	^ super ! anObject
]

{ #category : #accessing }
TensorProductModule >> arity [
	^ components size
]

{ #category : #accessing }
TensorProductModule >> at: anInteger [
	^ components at: anInteger
]

{ #category : #private }
TensorProductModule >> components [
	^ components
]

{ #category : #private }
TensorProductModule >> components: anArray [
	components := anArray

"	| algebra indeterminates |
	components := anArray.
	indeterminates := OrderedCollection new.
	anArray withIndexDo: [:each :i| 1 to: each rank do: [:j| indeterminates add: 'x', (i printString, ',' j printString) sub]].
	algebra := components anyOne scalars freeAlgebraIn: indeterminates.
	self propertyAt: #ambientAlgebra put: algebra"
]

{ #category : #morphisms }
TensorProductModule >> compose: anArray [
	| coordinates answer |
	anArray size = self arity ifFalse: [DomainError signal].
	coordinates := anArray withIndexCollect: [:each :i| (self at: i) coordinatesOf: each].
	answer := Tensor new parent: self.
	self indices do: [:each|
		answer at: each put: ((1 to: coordinates size) inject: self scalars one into: [:product :i| product * ((coordinates at: i) at: (each at: i))])].
	^ answer
]

{ #category : #morphisms }
TensorProductModule >> composition [
	"This is the product of tensors. This is a multilinear map."
	^ (Function from: self asCartesianProduct to: self evaluating: [:each| self compose: each]) name: Character otimes asString
]

{ #category : #private }
TensorProductModule >> computeIndices [
	| indices |
	indices := OrderedCollection with: {}.
	components do: [:X| | newIndices |
		newIndices := OrderedCollection new.
		indices do: [:each| 1 to: X rank do: [:i| newIndices add: each, {i}]].
		indices := newIndices].
	^ indices
]

{ #category : #private }
TensorProductModule >> computeType [
	| V W i n |
	V := components first.
	i := components findFirst: [:each| each ~= V].
	i = 0 ifTrue: [^ {self arity. 0}].
	W := components at: i.
	W = V dual ifFalse: [^ nil].
	n := components findLast: [:each| each ~= W].
	i-1 = n ifFalse: [^ nil].
	^ {n. self arity - n}
]

{ #category : #basis }
TensorProductModule >> coordinatesOf: anElement [
	^ self scalars tuple: (self indices collect: [:each| anElement at: each])
]

{ #category : #basis }
TensorProductModule >> e: anInteger [
	^ Tensor new parent: self; at: (self indices at: anInteger) put: self scalars one; yourself
]

{ #category : #elements }
TensorProductModule >> evaluating: aBlock [
	| answer |
	answer := Tensor new parent: self.
	self indices do: [:each| answer at: each put: (aBlock value: each)].
	^ answer
]

{ #category : #testing }
TensorProductModule >> includes: anObject [
	^ (anObject isKindOf: Tensor) and: [anObject parent = self]
]

{ #category : #accessing }
TensorProductModule >> indices [
	^ self propertyAt: #indices ifAbsentPut: [self computeIndices]
]

{ #category : #converting }
TensorProductModule >> over: aRing [
	"Answer the change of base ring of the receiver."
	^ self class components: (components collect: [:each| each over: aRing])
]

{ #category : #printing }
TensorProductModule >> printOn: aStream [
	components do: [:each| aStream print: each] separatedBy: [aStream nextPut: Character otimes]
]

{ #category : #basis }
TensorProductModule >> rank [
	^ components product: [:each| each rank]
]

{ #category : #accessing }
TensorProductModule >> scalars [
	components do: [:any| ^ any scalars].
	^ nil
]

{ #category : #accessing }
TensorProductModule >> type [
	"Tensor products of n copies of a vector space and m copies of its dual are of type (n,m)."
	self propertyAt: #type ifAbsentPut: [self computeType]
]
