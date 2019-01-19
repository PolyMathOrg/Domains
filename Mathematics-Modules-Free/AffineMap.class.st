"
Affine transformations (affine maps or affinities) defined over affine linear spaces (vector spaces considered as affine spaces by 'forgetting the origin').

Affine maps are defined by a linear map and a translation (a vector of the codomain).

References:
	https://en.wikipedia.org/wiki/Affine_transformation
"
Class {
	#name : #AffineMap,
	#superclass : #Function,
	#instVars : [
		'linearMap',
		'translation'
	],
	#category : #'Mathematics-Modules-Free'
}

{ #category : #'instance creation' }
AffineMap class >> from: aDomain to: aCodomain evaluating: aBlock [
	| linearMap translation |
	translation := aBlock value: aDomain zero.
	linearMap := LinearMap from: aDomain to: aCodomain evaluating: [:v| (aBlock value: v) - translation].
	^ self linearMap: linearMap translation: translation
]

{ #category : #'instance creation' }
AffineMap class >> from: anAffineFrame to: anotherAffineFrame matrix: aMatrix [
	^ self notYetImplemented
]

{ #category : #'instance creation' }
AffineMap class >> linearMap: aLinearMap translation: aVector [
	(aLinearMap codomain includes: aVector)
		ifFalse: [^ DomainError signal: 'translation vector is outside of the codomain'].
	^ self new linearMap: aLinearMap; translation: aVector
]

{ #category : #arithmetic }
AffineMap >> * aNumber [
	^ self class linearMap: linearMap * aNumber translation: translation * aNumber
]

{ #category : #arithmetic }
AffineMap >> + anObject [
	(anObject isKindOf: AffineMap)
		ifTrue:
			[^ self class linearMap: linearMap + anObject linearMap translation: translation + anObject translation].
	((anObject isKindOf: LinearMap) and: [linearMap domain = anObject domain and: [linearMap codomain = anObject codomain]])
		ifTrue:
			[^ self class linearMap: linearMap + anObject translation: translation].
	(self codomain includes: anObject)
		ifTrue: [^ self class linearMap: linearMap translation: translation + anObject].
	^ DomainError signal
]

{ #category : #comparing }
AffineMap >> = anAffineMap [
	^ (anAffineMap isKindOf: AffineMap) and: [linearMap = anAffineMap linearMap and: [translation = anAffineMap translation]]
]

{ #category : #converting }
AffineMap >> asPolynomial [
	^ linearMap asPolynomial + (linearMap codomain coordinatesOf: translation) first
]

{ #category : #converting }
AffineMap >> asRationalMap [
	^ linearMap asRationalMap + (linearMap codomain coordinatesOf: translation)
]

{ #category : #accessing }
AffineMap >> bitSize [
	^ linearMap bitSize + translation bitSize
]

{ #category : #accessing }
AffineMap >> codomain [
	^ linearMap codomain
]

{ #category : #accessing }
AffineMap >> domain [
	^ linearMap domain
]

{ #category : #operations }
AffineMap >> fiberAt: aPoint [
	^ linearMap fiberAt: aPoint - translation
]

{ #category : #comparing }
AffineMap >> hash [
	^ linearMap hash + translation hash hashMultiply
]

{ #category : #operations }
AffineMap >> image [
	^ AffineSubspace representative: translation direction: linearMap image
]

{ #category : #arithmetic }
AffineMap >> inverse [
	"Answer the inverse of the receiver. Answer nil if the receiver is not an isomorphism."
	^ self domain dimension = self codomain dimension ifTrue: [self leftInverse]
]

{ #category : #testing }
AffineMap >> isEuclidean [
	"Answer true if the receiver is an Euclidean motion, i.e. if it preserves distances.
	The Euclidean nitions of an affine space A form a group, the Euclidean group E(A) (sometimes called group of motions M(A) or group of isometries ISO(A))."
	^ self isIsometry
]

{ #category : #testing }
AffineMap >> isIdentity [
	^ translation isZero and: [linearMap isIdentity]
]

{ #category : #testing }
AffineMap >> isInjective [
	^ linearMap isInjective
]

{ #category : #testing }
AffineMap >> isIsometry [
	"Answer true if the receiver is an isometry, i.e. if it preserves distances.
	The isometries of an affine space A form a group, the Euclidean group E(A) (sometimes called group of Euclidean motions M(A) or group of isometries ISO(A))."
	^ linearMap isOrthogonal
]

{ #category : #testing }
AffineMap >> isSurjective [
	^ linearMap isSurjective
]

{ #category : #arithmetic }
AffineMap >> leftInverse [
	"Answer a left inverse (or retraction) of the receiver.
	Answer nil if the receiver is not a monomorphism."
	^ linearMap leftInverse ifNotNil: [:aLinearMap| self class linearMap: aLinearMap translation: (aLinearMap value: translation negated)]
]

{ #category : #'accessing-private' }
AffineMap >> linearMap [
	^ linearMap
]

{ #category : #'accessing-private' }
AffineMap >> linearMap: aLinearMap [
	linearMap := aLinearMap
]

{ #category : #accessing }
AffineMap >> matrix [
	| K zero A b |
	K := linearMap domain scalars.
	zero := K zero.
	A := linearMap matrix.
	b := linearMap codomain coordinatesOf: translation.
	^ K matrix: A extent + (1@1)
		evaluating: [:i :j|
			(i <= A height and: [j <= A width])
				ifTrue: [A at: i@j]
				ifFalse: [j = A width + 1
					ifTrue: [i <= b size ifTrue: [b at: i] ifFalse: [K one]]
					ifFalse: [zero]]]
]

{ #category : #'accessing-private' }
AffineMap >> matrix: aMatrix [
	matrix := aMatrix
]

{ #category : #arithmetic }
AffineMap >> negated [
	^ self class linearMap: linearMap negated translation: translation negated
]

{ #category : #printing }
AffineMap >> printOn: aStream [
	self isIdentity ifTrue: [aStream nextPutAll: 'id'. ^ self].
	self negated isIdentity ifTrue: [aStream nextPutAll: '-id'. ^ self].
	"aStream print: linearPart; nextPutAll: ' + '; print: self translation"
	aStream print: self asRationalMap
]

{ #category : #arithmetic }
AffineMap >> rightInverse [
	"Answer a right inverse (or section) of the receiver.
	Answer nil if the receiver is not an epimorphism."
	^ linearMap rightInverse ifNotNil: [:aLinearMap| self class linearMap: aLinearMap translation: (aLinearMap value: translation negated)]
]

{ #category : #'accessing-private' }
AffineMap >> translation [
	^ translation
]

{ #category : #'accessing-private' }
AffineMap >> translation: aVector [
	translation := aVector
]

{ #category : #operations }
AffineMap >> value: aPoint [
	^ (linearMap value: aPoint) + translation
]

{ #category : #arithmetic }
AffineMap >> î [ anAffineMap
	self domain >= anAffineMap codomain ifFalse: [^ DomainError signal: 'domains don''t match'].
	^ self class from: anAffineMap domain to: self codomain evaluating: [:x| self value: (anAffineMap value: x)]
]
