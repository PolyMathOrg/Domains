"
The singletion global instance NN is the set of natural numbers 1, 2, 3, ...
"
Class {
	#name : #Naturals,
	#superclass : #Domain,
	#category : #'Mathematics-Sets'
}

{ #category : #initialization }
Naturals class >> initialize [
	super initialize.
	Smalltalk at: #NN put: self new
]

{ #category : #comparing }
Naturals >> = anObject [
	^ self class == anObject class
]

{ #category : #random }
Naturals >> atRandom: aRandom bits: bitSize [
	^ (aRandom nextBits: bitSize truncated) + 1
]

{ #category : #enumerating }
Naturals >> do: aBlock [
	| n |
	n := 1.
	[aBlock value: n. n := n + 1] repeat
]

{ #category : #comparing }
Naturals >> hash [
	^ self class hash
]

{ #category : #accessing }
Naturals >> identity [
	^ 1
]

{ #category : #testing }
Naturals >> isCommutative [
	^ true
]

{ #category : #testing }
Naturals >> isFinite [
	^ false
]

{ #category : #testing }
Naturals >> isReal [
	^ true
]

{ #category : #printing }
Naturals >> printOn: aStream [
	aStream nextPut: Character NN
]

{ #category : #accessing }
Naturals >> size [
	^ Aleph new
]

{ #category : #morphisms }
Naturals >> to: aDomain evaluating: aBlock [
	"Answer a sequence with values in aDomain."
	^ Sequence to: aDomain evaluating: aBlock
]
