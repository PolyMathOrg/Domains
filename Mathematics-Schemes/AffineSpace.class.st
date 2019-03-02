"
Affine spaces R^n as schemes, i.e. Spec R[x1,...,xn] for some commutative ring R.

Note that affine spaces defined as schemes differ from the classical affine spaces defined as 'vector spaces that have forgotten the origin'. The morphisms of this affine space are of course morphisms of schemes, not just the classical (linear) affine transformations.

Note also that the dimension of an affine space as scheme is the Krull dimension of its coordinate ring, and this can be bigger than the number of indeterminates (see >>dimension and >>rank). For affine spaces over fields, the dimension and the rank are equal (because fields have Krull dimension 0).
"
Class {
	#name : #AffineSpace,
	#superclass : #AffineVariety,
	#category : #'Mathematics-Schemes-Affine'
}

{ #category : #examples }
AffineSpace class >> example1 [
	"The rational affine plane:"
	^ AffineSpace new: 2 over: QQ
]

{ #category : #examples }
AffineSpace class >> example2 [
	"Or assigning names to the indeterminates of the coordinate ring:"
	^ AffineSpace new: #(x y) over: QQ
]

{ #category : #examples }
AffineSpace class >> example3 [
	"And equivalently:"
	^ (QQ polynomialsIn: #(x y)) spec
]

{ #category : #'instance creation' }
AffineSpace class >> new: rank over: aRing [
	^ self coordinateRing: (aRing polynomialsIn: rank)
]

{ #category : #accessing }
AffineSpace >> ambient [
	^ self
]

{ #category : #operations }
AffineSpace >> cartesianProduct: anAffineSpace [
	"◊ "

	"Answer the cartesian product of the receiver and the argument."

	(anAffineSpace isKindOf: AffineSpace)
		ifFalse: [ ^ ' super ◊ anAffineSpace' ].
	^ ProductAffineSpace
		components:
			{self.
			anAffineSpace}
]

{ #category : #accessing }
AffineSpace >> ideal [
	"Answer the defining ideal of the receiver, considered as a subscheme of itself."
	^ self coordinateRing zeroIdeal
]

{ #category : #testing }
AffineSpace >> isPlane [
	^ self rank = 2
]

{ #category : #points }
AffineSpace >> origin [
	^ self pointAt: (self scalars zeroTuple: self rank)
]

{ #category : #points }
AffineSpace >> pointsCountOver: aRing [
	^ 'aRing size ^ self rank'
]

{ #category : #points }
AffineSpace >> pointsOver: aRing do: aBlock [
	^ 'aRing ^ self rank do: [:each| aBlock value: (self pointAt: each)]'
]

{ #category : #printing }
AffineSpace >> printOn: aStream [
	aStream
		print: self scalars;
		nextPut:$^;
		print: self rank
]

{ #category : #morphisms }
AffineSpace >> projectiveEmbedding [
	| P map patches |
	self propertyAt: #projectiveEmbedding ifPresent: [:aRationalMap| ^ aRationalMap].
	P := ProjectiveSpace new: self rank over: self scalars.
	map := self to: P evaluating: [:x| x homogenizedIn: P rank].
	patches := Array new: P ambient rank.
	patches at: patches size put: self.
	P propertyAt: #affinePatches put: patches.
	^ self propertyAt: #projectiveEmbedding put: map
]

{ #category : #accessing }
AffineSpace >> rank [
	"Answer the number of affine coordinates, i.e. the number of indeterminates of the coordinate ring. This can be different from the Krull dimension, for example Spec Z[x] has rank 1 and Krull dimension 2."
	^ self coordinateRing rank
]

{ #category : #testing }
AffineSpace >> satisfies: aTuple [
	^ true
]

{ #category : #operations }
AffineSpace >> subscheme: anObject [
	| I |
	I := (anObject isKindOf: Ideal)
		ifTrue: [anObject] ifFalse: [self coordinateRing * anObject].
	^ (self coordinateRing / I) spec
		propertyAt: #ambient put: self; yourself
]
