"
A free monoid is a monoid whose elements are words (see Word) in a finite set of arbitrary objects (symbols), together with word concatenation as monoid operation.

See also FreeAbelianMonoid, the commutative analog.

"
Class {
	#name : #FreeMonoid,
	#superclass : #Monoid,
	#instVars : [
		'symbols'
	],
	#category : #'Mathematics-Monoids'
}

{ #category : #'instance creation' }
FreeMonoid class >> new: anInteger [
	^ self on: (1 to: anInteger)
]

{ #category : #'instance creation' }
FreeMonoid class >> on: aCollection [
	^ self new symbols: aCollection
]

{ #category : #random }
FreeMonoid >> atRandom: aRandom bits: bitSize [
	| answer n |
	answer := self identity.
	n := symbols size.
	bitSize // n highBit
		timesRepeat:
			[((n + 1) atRandom: aRandom) = 1
				ifFalse: [answer := (Word x: (symbols atRandom: aRandom)) * answer]].
	^ answer
]

{ #category : #testing }
FreeMonoid >> contains: aWord [
	aWord do: [:i :exp| ((symbols includes: i) and: [exp >= 0]) ifFalse: [^ false]].
	^ true
]

{ #category : #accessing }
FreeMonoid >> generators [
	^ symbols collect: [:each| Word x: each]
]

{ #category : #accessing }
FreeMonoid >> identity [
	^ Word empty
]

{ #category : #testing }
FreeMonoid >> includes: aWord [
	^ (aWord isKindOf: Word) and: [self contains: aWord]
]

{ #category : #testing }
FreeMonoid >> isCommutative [
	^ symbols size <= 1
]

{ #category : #printing }
FreeMonoid >> printOn: aStream [
	aStream nextPut: ${.
	symbols do: [:i| aStream print: (Word x: i)] separatedBy: [aStream nextPut: $,].
	aStream nextPutAll: '}*'
]

{ #category : #morphisms }
FreeMonoid >> projection: anObject [
	"Answer the 'string projection' endomorphism that removes all occurrences of a letter from a string."
	^ self to: (self copyWithout: anObject) evaluating: [:w| w copyWithout: anObject]
]

{ #category : #accessing }
FreeMonoid >> rank [
	^ symbols size
]

{ #category : #accessing }
FreeMonoid >> size [
	^ self rank > 0 ifTrue: [Aleph new] ifFalse: [1]
]

{ #category : #accessing }
FreeMonoid >> symbols [
	^ symbols
]

{ #category : #'accessing-private' }
FreeMonoid >> symbols: aCollection [
	symbols := aCollection
]

{ #category : #elements }
FreeMonoid >> x: anIndeterminate [
	^ self x: anIndeterminate to: 1
]

{ #category : #elements }
FreeMonoid >> x: anIndeterminate to: exponent [
	^ Word x: anIndeterminate to: exponent
]
