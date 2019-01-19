"
The Grassmannian Gr(r,V) is the set of r-dimensional subspaces of the vector space V.
"
Class {
	#name : #Grassmannian,
	#superclass : #Scheme,
	#instVars : [
		'space',
		'rank'
	],
	#category : #'Mathematics-Modules-Free'
}

{ #category : #'instance creation' }
Grassmannian class >> new: anInteger over: aSpace [
	^ self new space: aSpace; rank: anInteger
]

{ #category : #comparing }
Grassmannian >> = aGrassmannian [
	^ (aGrassmannian isKindOf: Grassmannian) and: [aGrassmannian space = self space]
]

{ #category : #random }
Grassmannian >> atRandom: aRandom bits: bits [
	| S |
	S := space null.
	[S rank < rank]
		whileTrue:
			[ | v |
			"take max the rank of the space, otherwise it might give always 0 and loop forever:"
			[v := space atRandom: aRandom bits: (bits / rank max: space rank).
			S contains: v] whileTrue.
			S := S + (space span: {v})].
	^ S
]

{ #category : #testing }
Grassmannian >> contains: aSubspace [
	^ space >= aSubspace and: [aSubspace rank = rank]
]

{ #category : #accessing }
Grassmannian >> dimension [
	^ rank * (space rank - rank)
]

{ #category : #morphisms }
Grassmannian >> dual [
	^ space dual grassmannian: space dimension - rank
]

{ #category : #testing }
Grassmannian >> includes: aSubspace [
	^ aSubspace isFreeModule and: [self contains: aSubspace]
]

{ #category : #morphisms }
Grassmannian >> pluckerEmbedding [
	"Answer the Plucker embedding, a natural embedding of the Grassmannian into a projective space."
	^ self notYetImplemented "need to implement the wedge product"
]

{ #category : #printing }
Grassmannian >> printOn: aStream [
	aStream nextPutAll: 'Gr('; print: rank; nextPut: $,; print: space; nextPut: $)
]

{ #category : #accessing }
Grassmannian >> rank [
	^ rank
]

{ #category : #private }
Grassmannian >> rank: anInteger [
	rank := anInteger
]

{ #category : #accessing }
Grassmannian >> size [
	self space isFinite ifFalse: [^ self space size].
	^ self space dimension choose: self rank q: self space scalars size
]

{ #category : #accessing }
Grassmannian >> space [
	^ space
]

{ #category : #private }
Grassmannian >> space: aVectorSpace [
	space := aVectorSpace
]
