"
Ambient modules (or vector spaces) of n-tuples over a given ring (or field).
"
Class {
	#name : #TupleModule,
	#superclass : #FreeModule,
	#instVars : [
		'scalars',
		'rank'
	],
	#category : #'Mathematics-Modules-Tuples'
}

{ #category : #'instance creation' }
TupleModule class >> new: anInteger over: aRing [
	^ self new rank: anInteger; scalars: aRing
]

{ #category : #elements }
TupleModule >> ! anArray [
	^ scalars tuple: anArray
]

{ #category : #comparing }
TupleModule >> = anObject [
	self == anObject ifTrue: [^ true].
	(anObject isKindOf: TupleModule)
		ifTrue: [^ anObject scalars = self scalars and: [self rank = anObject rank]].
	^ super = anObject
]

{ #category : #random }
TupleModule >> atRandom: aRandom [
	^ scalars tuple: self rank evaluating: [:i| scalars atRandom: aRandom]
]

{ #category : #random }
TupleModule >> atRandom: aRandom bits: bitSize [
	| n |
	self isTrivial ifTrue: [^ self zero].
	n := bitSize / self rank.
	^ scalars tuple: self rank evaluating: [:i| scalars atRandom: aRandom bits: n]
]

{ #category : #basis }
TupleModule >> coordinatesOf: aTuple [
	^ aTuple scalars == scalars ifTrue: [aTuple] ifFalse: [scalars tuple: aTuple]
]

{ #category : #enumerating }
TupleModule >> do: aBlock [
	self upTo: scalars size rank: rank do: aBlock
]

{ #category : #basis }
TupleModule >> e: anInteger [
	^ self scalars tuple: rank evaluating: [:k| k = anInteger ifTrue: [scalars one] ifFalse: [scalars zero]]
]

{ #category : #basis }
TupleModule >> elementAt: aTuple [
	"Answer the vector with coordinates aTuple in the canonical basis (i.e, the standard basis)."
	^ aTuple scalars == scalars ifTrue: [aTuple] ifFalse: [scalars tuple: aTuple]
]

{ #category : #morphisms }
TupleModule >> embedding: i [
	^ (self scalars asSelfModule to: self evaluating: [:x|
			self scalars tuple: rank evaluating: [:k|
				k = i ifTrue: [x] ifFalse: [scalars zero]]]) name: 'i', i printText sub
]

{ #category : #elements }
TupleModule >> evaluating: aBlock [
	^ scalars tuple: rank evaluating: aBlock
]

{ #category : #testing }
TupleModule >> includes: anObject [
	^ anObject isTuple and: [anObject size = self rank and: [anObject scalars <= self scalars]]
]

{ #category : #testing }
TupleModule >> isFinite [
	^ scalars isFinite
]

{ #category : #converting }
TupleModule >> over: aRing [
	^ self copy scalars: aRing
]

{ #category : #printing }
TupleModule >> printOn: aStream [
	aStream print: self scalars.
	aStream isText
		ifTrue: [aStream nextPutAll: self rank printString super]
		ifFalse: [aStream nextPutAll: '^'; print: self rank]
]

{ #category : #morphisms }
TupleModule >> projection: i [
	^ self ambient dual evaluating: [:x| x at: i]
]

{ #category : #basis }
TupleModule >> rank [
	^ rank
]

{ #category : #'accessing-private' }
TupleModule >> rank: n [
	rank := n
]

{ #category : #accessing }
TupleModule >> scalars [
	^ scalars
]

{ #category : #'accessing-private' }
TupleModule >> scalars: aRing [
	scalars := aRing
]

{ #category : #enumerating }
TupleModule >> upTo: max rank: n do: aBlock [
	| k |
	n = 0 ifTrue: [^ aBlock value: (scalars tuple: #())].
	k := 1.
	scalars upTo: max do: [:s|
		self upTo: k rank: n-1 do: [:p|
			aBlock value: (p copyWith: s).
			(p includes: s) ifTrue: [scalars upTo: k-1 do: [:t| aBlock value: (p copyWith: t)]]].
		k := k + 1]
]

{ #category : #elements }
TupleModule >> zero [
	| contents |
	contents := Array new: self rank.
	contents atAllPut: self scalars zero.
	^ scalars tuple: contents
]
