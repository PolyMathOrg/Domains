"
Free groups on a given set of symbols. Their elements are (noncommutative) words on the set of symbols (see Word).
"
Class {
	#name : #FreeGroup,
	#superclass : #Group,
	#instVars : [
		'symbols'
	],
	#category : #'Mathematics-Groups'
}

{ #category : #'instance creation' }
FreeGroup class >> new: anInteger [
	^ self on: (1 to: anInteger)
]

{ #category : #'instance creation' }
FreeGroup class >> on: aCollection [
	^ self new symbols: aCollection
]

{ #category : #random }
FreeGroup >> atRandom: aRandom bits: bitSize [
	| answer |
	answer := self identity.
	bitSize // symbols size highBit
		timesRepeat:
			[answer := (Word x: (symbols atRandom: aRandom) to: (#(-1 1) atRandom: aRandom)) * answer].
	^ answer
]

{ #category : #accessing }
FreeGroup >> generators [
	^ symbols collect: [:each| Word x: each]
]

{ #category : #accessing }
FreeGroup >> identity [
	^ Word empty
]

{ #category : #testing }
FreeGroup >> includes: aWord [
	aWord do: [:i :exp| (symbols includes: i) ifFalse: [^ false]].
	^ true
]

{ #category : #testing }
FreeGroup >> isCommutative [
	^ symbols size <= 1
]

{ #category : #testing }
FreeGroup >> isFinitelyGenerated [
	^ true
]

{ #category : #accessing }
FreeGroup >> presentation [
	^ GroupPresentation free: self generators
]

{ #category : #printing }
FreeGroup >> printOn: aStream [
	aStream nextPutAll: 'F('; print: symbols; nextPut: $)
]

{ #category : #accessing }
FreeGroup >> rank [
	^ symbols size
]

{ #category : #accessing }
FreeGroup >> size [
	^ symbols size > 0 ifTrue: [Aleph new] ifFalse: [1]
]

{ #category : #accessing }
FreeGroup >> symbols [
	^ symbols
]

{ #category : #'accessing-private' }
FreeGroup >> symbols: aCollection [
	symbols := aCollection
]

{ #category : #comparing }
FreeGroup >> ~ aFreeGroup [
	"Answer true if the receiver is isomorphic to the argument."
	^ ((aFreeGroup isKindOf: FreeGroup) and: [self rank = aFreeGroup rank]) or: [super ~ aFreeGroup]
]
