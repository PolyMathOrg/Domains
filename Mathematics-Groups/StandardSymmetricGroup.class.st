"
The symmetric group Sym(n) of permutations on the elements of a set [1..n] (which we call 'space').

"
Class {
	#name : #StandardSymmetricGroup,
	#superclass : #SymmetricGroup,
	#instVars : [
		'degree'
	],
	#category : #'Mathematics-Groups-Permutations'
}

{ #category : #'instance creation' }
StandardSymmetricGroup class >> new: n [
	^ self new degree: n
]

{ #category : #'instance creation' }
StandardSymmetricGroup class >> on: aCollection [
	^ self shouldNotImplement
]

{ #category : #elements }
StandardSymmetricGroup >> ! anObject [
	"Coerce anObject to an element of the receiver (a permutation)."
	anObject isSequenceable
		ifFalse: [^ super ! anObject].
	(anObject allSatisfy: [:each| each isInteger and: [each between: 1 and: degree]])
		ifTrue: [^ self mapping: anObject asArray].
	(anObject allSatisfy: [:each| each isSequenceable]) "cycles"
		ifTrue: [^ self cycles: anObject].
	^ super ! anObject
]

{ #category : #random }
StandardSymmetricGroup >> atRandom: aRandom [
	^ self mapping: ((1 to: degree) asArray shuffledBy: aRandom)
]

{ #category : #elements }
StandardSymmetricGroup >> cycle: anArray [
	^ StandardPermutation new: self degree cycle: anArray
]

{ #category : #elements }
StandardSymmetricGroup >> cycles: anArray [
	^ StandardPermutation new: self degree cycles: anArray
]

{ #category : #accessing }
StandardSymmetricGroup >> degree [
	^ degree
]

{ #category : #private }
StandardSymmetricGroup >> degree: anInteger [
	degree := anInteger
]

{ #category : #enumerating }
StandardSymmetricGroup >> do: aBlock [
	(1 to: degree) asArray permutationsDo: [:each| aBlock value: (self mapping: each copy)]
]

{ #category : #elements }
StandardSymmetricGroup >> evaluating: aBlock [
	^ StandardPermutation new: self degree evaluating: aBlock
]

{ #category : #elements }
StandardSymmetricGroup >> identity [
	^ self propertyAt: #identity ifAbsentPut: [StandardPermutation new: degree]
]

{ #category : #testing }
StandardSymmetricGroup >> includes: anObject [
	^ (anObject isKindOf: StandardPermutation) and: [anObject degree = self degree]
]

{ #category : #testing }
StandardSymmetricGroup >> isStandard [
	"Answer true if the domain of the receiver is an interval [1..n]."
	^ true
]

{ #category : #elements }
StandardSymmetricGroup >> mapping: anArray [
	^ StandardPermutation map: anArray
]

{ #category : #printing }
StandardSymmetricGroup >> printOn: aStream [
	aStream nextPutAll: 'S', degree printText sub
]

{ #category : #accessing }
StandardSymmetricGroup >> space [
	^ 1 to: degree
]

{ #category : #elements }
StandardSymmetricGroup >> transposing: anInteger with: anotherInteger [
	"Answer the tranposition of anInteger with anotherInteger."
	^ StandardPermutation new: degree transposing: anInteger with: anotherInteger
]
