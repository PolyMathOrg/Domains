"
Module cosets or affine subspaces contained in a given vector space or module, i.e. flats, or linear varieties, linear manifolds, or translated subspaces/submodules (cosets).

They appear when considering the solutions of non-homogeneous linear systems, or the set of all the vectors in the domain of a linear map that are mapped to a given vector in the codomain of the transformation (the 'fiber' of the vector). They are also the elements of quotient spaces or quotient modules.

"
Class {
	#name : #AffineSubspace,
	#superclass : #Domain,
	#instVars : [
		'direction',
		'representative'
	],
	#category : #'Mathematics-Modules-Free'
}

{ #category : #examples }
AffineSubspace class >> example1 [
	"Make an affine subspace by translating a subspace by a vector."
	| V S |
	V := QQ raiseTo: 3.
	S := V span: {(1,2,3)}.
	^ S + (1,1,1)
]

{ #category : #examples }
AffineSubspace class >> example2 [
	"The fiber (or inverse image) of a linear map is an affine subspace."
	| V f |
	V := QQ raiseTo: 3.
	f := V endomorphisms evaluatingWithArguments: [:x :y :z| (x+z, (y+z), z)].
	"The fiber at (1,2,3) is the set of all vectors that f sends to (1,2,3):"
	^ f fiberAt: (1,2,3)
]

{ #category : #'instance creation' }
AffineSubspace class >> representative: aVector direction: aSubspace [
"	(aSubspace contains: aVector) ifTrue: [^ AffineLinearSpace on: aSubspace]."
	^ self new direction: aSubspace; representative: aVector
]

{ #category : #operations }
AffineSubspace >> * aScalar [
	(self scalars includes: aScalar)
		ifTrue: [^ self class representative: representative * aScalar direction: direction].
	^ super * aScalar "if it's not a scalar"
]

{ #category : #operations }
AffineSubspace >> + anObject [
	(anObject isKindOf: AffineSubspace)
		ifTrue: [^ self class representative: representative + anObject representative direction: direction + anObject direction].
	(anObject isKindOf: FreeModule)
		ifTrue: [^ self class representative: representative direction: direction + anObject].
	(direction ambient includes: anObject)
		ifTrue: [^ self class representative: representative + anObject direction: direction].
	DomainError signal
]

{ #category : #operations }
AffineSubspace >> - anObject [
	^ self + anObject negated
]

{ #category : #operations }
AffineSubspace >> / aScalar [
	^ self * aScalar reciprocal
]

{ #category : #operations }
AffineSubspace >> /\ anAffineSubspace [
	"Meet."
	^ self ï anAffineSubspace
]

{ #category : #comparing }
AffineSubspace >> < anAffineSubspace [
	"Answer true if the receiver is strictly included in the argument."
	^ self dimension < anAffineSubspace dimension and: [self <= anAffineSubspace]
]

{ #category : #comparing }
AffineSubspace >> <= anAffineSubspace [
	"Answer true if the receiver is included in the argument."
	self == anAffineSubspace ifTrue: [^ true].
	self dimension <= anAffineSubspace dimension ifFalse: [^ false].
	self isEmpty ifTrue: [^ true].
	^ (anAffineSubspace includes: representative) and: [direction <= anAffineSubspace direction]
]

{ #category : #comparing }
AffineSubspace >> = anObject [
	self == anObject ifTrue: [^ true].
	(anObject isKindOf: AffineSubspace) ifFalse: [^ false].
	self isEmpty ifTrue: [^ anObject isEmpty].
	^ direction = anObject direction and: [anObject includes: representative]
]

{ #category : #operations }
AffineSubspace >> \/ anAffineSubspace [
	"Join."
	^ self + anAffineSubspace
]

{ #category : #accessing }
AffineSubspace >> ambient [
	^ direction ambient
]

{ #category : #morphisms }
AffineSubspace >> apply: aMap [
	"Answer the receiver transformed by anAffineMap."
	(aMap isKindOf: AffineMap)
		ifTrue: [^ self species representative: (aMap value: representative) direction: (direction apply: aMap linearMap)].
	^ self species representative: (aMap value: representative) direction: (direction apply: aMap)
]

{ #category : #random }
AffineSubspace >> atRandom: aRandom [
	^ (direction atRandom: aRandom) + representative
]

{ #category : #random }
AffineSubspace >> atRandom: aRandom bits: bitSize [
	^ (direction atRandom: aRandom bits: bitSize) + representative
]

{ #category : #operations }
AffineSubspace >> catProd: anAffineSubspace [ "◊ "
	^ self class on: (direction ê anAffineSubspace direction)
]

{ #category : #accessing }
AffineSubspace >> codimension [
	^ direction codimension
]

{ #category : #testing }
AffineSubspace >> contains: anObject [
	^ self isEmpty not and: [direction contains: anObject - representative]
]

{ #category : #accessing }
AffineSubspace >> dimension [
	^ representative isNil ifTrue: [-1] ifFalse: [direction dimension]
]

{ #category : #accessing }
AffineSubspace >> direction [
	"Answer the 'difference space' or 'direction', a linear subspace parallel to the receiver."
	^ direction
]

{ #category : #'accessing-private' }
AffineSubspace >> direction: aVectorSpace [
	direction := aVectorSpace
]

{ #category : #enumerating }
AffineSubspace >> do: aBlock [
	direction do: [:each| aBlock value: each + representative]
]

{ #category : #operations }
AffineSubspace >> dot: anAffineSubspace [
	"Answer the intersection of the receiver and the argument."
	| system |
	self isEmpty ifTrue: [^ self].
	anAffineSubspace isEmpty ifTrue: [^ anAffineSubspace].
	system := self equations copy.
	anAffineSubspace equations do: [ :each | system add: each].
	^ system solutions
]

{ #category : #comparing }
AffineSubspace >> hash [
	^ self isEmpty ifTrue: [0] ifFalse: [direction hash]
]

{ #category : #testing }
AffineSubspace >> includes: anObject [
	^ (self ambient includes: anObject) and: [self contains: anObject]
]

{ #category : #testing }
AffineSubspace >> isEmpty [
	^ self dimension = -1
]

{ #category : #testing }
AffineSubspace >> isHyperplane [
	^ self codimension = 1
]

{ #category : #testing }
AffineSubspace >> isLine [
	^ self dimension = 1
]

{ #category : #testing }
AffineSubspace >> isPlane [
	^ self dimension = 2
]

{ #category : #testing }
AffineSubspace >> isPoint [
	^ self dimension = 0
]

{ #category : #testing }
AffineSubspace >> isZero [
	^ direction includes: representative
]

{ #category : #operations }
AffineSubspace >> negated [
	^ self class representative: representative negated direction: direction
]

{ #category : #printing }
AffineSubspace >> printOn: aStream [
"	self isEmpty ifTrue: [aStream nextPut: Character emptySet. ^ self].
	self dimension = 0 ifTrue: [aStream nextPut: ${; print: representative; nextPut: $}. ^ self].
	aStream nextPut: $[.
	representative isTuple ifTrue: [representative printCoefficientsOn: aStream] ifFalse: [aStream print: representative].
	aStream nextPut: $]

alternative:"
	direction isEmbedded ifFalse: [aStream print: direction. ^ self].
	self isEmpty ifTrue: [aStream nextPut: Character emptySet. ^ self].
	self dimension = 0 ifTrue: [aStream nextPut: ${; print: representative; nextPut: $}. ^ self].
	aStream print: representative; nextPutAll: ' + '; print: direction
]

{ #category : #accessing }
AffineSubspace >> representative [
	^ representative
]

{ #category : #'accessing-private' }
AffineSubspace >> representative: aPoint [
	representative := aPoint
]

{ #category : #accessing }
AffineSubspace >> scalars [
	^ direction scalars
]

{ #category : #operations }
AffineSubspace >> span [
	"Answer the linear span of the receiver."
	(direction includes: representative) ifTrue: [^ direction].
	^ (direction basis copyWith: representative) span
]

{ #category : #operations }
AffineSubspace >> span: aCollection [
	"Answer the subspace spanned by the points in aCollection."
	| p |
	p := aCollection anyOne.
	^ self class representative: p direction: (direction span: ((aCollection copyWithout: p) collect: [:each| each - p]))
]

{ #category : #private }
AffineSubspace >> species [
	^ AffineSubspace
]

{ #category : #accessing }
AffineSubspace >> substraction [
	"Answer the substraction map on the receiver."
	^ (self, self) to: self direction evaluatingWithArguments: [:a :b| a - b]
]

{ #category : #accessing }
AffineSubspace >> translation [
	"Answer the translation map on the receiver."
	^ (self, self direction) to: self evaluatingWithArguments: [:a :v| a + v]
]

{ #category : #testing }
AffineSubspace >> || anAffineSubspace [
	"Answer true if the receiver and the argument are parallel."
	^ direction <= anAffineSubspace direction or: [direction >= anAffineSubspace direction]
]
