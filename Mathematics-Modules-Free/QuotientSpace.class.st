"
Quotient spaces V/S (read ""V mod S"") of a given vector space V modulo a subspace S.

The elements of a quotient space are cosets (affine subspaces, flats) S + x with x in V, and they form a vector space. See AffineSubspace.

See also QuotientModule.

References:
	https://en.wikipedia.org/wiki/Quotient_space_(linear_algebra)
"
Class {
	#name : #QuotientSpace,
	#superclass : #FreeModule,
	#category : #'Mathematics-Modules-Free'
}

{ #category : #'instance creation' }
QuotientSpace class >> mod: aSubspace [
	^ self new relations: aSubspace
]

{ #category : #accessing }
QuotientSpace >> base [
	^ self relations ambient
]

{ #category : #private }
QuotientSpace >> buildProjection [
	"Answer the quotient map, the canonical projection from the base vector space to the quotient space, i.e. the mapping pi:V->V/S that assigns to every v in V the affine subspace v+S."
	| answer |
	answer := self base to: self evaluating: [:each| self project: each].
	answer name: Character pi asString.
	answer properties
		at: #kernel put: self relations;
		at: #image put: self;
		at: #rightInverse put: (self to: self base evaluating: [:each| each representative]).
	^ answer
]

{ #category : #testing }
QuotientSpace >> contains: anAffineSubspace [
	^ anAffineSubspace direction = self relations
]

{ #category : #basis }
QuotientSpace >> coordinatesOf: anAffineSubspace [
	| v |
	v := anAffineSubspace representative.
	v := v - (self relations orthogonalProjection value: v).
	^ self relations perp coordinatesOf: v
]

{ #category : #basis }
QuotientSpace >> e: anInteger [
	^ AffineSubspace representative: (self relations perp e: anInteger) direction: self relations
]

{ #category : #testing }
QuotientSpace >> includes: anObject [
	^ (anObject isKindOf: AffineSubspace) and: [self contains: anObject]
]

{ #category : #testing }
QuotientSpace >> isQuotient [
	^ true
]

{ #category : #morphisms }
QuotientSpace >> lifting [
	"Answer the map from the receiver to the base space lifting the canonical projection."
	^ self projection section
]

{ #category : #printing }
QuotientSpace >> printOn: aStream [
	aStream print: self base; nextPut: $/; print: self relations
]

{ #category : #morphisms }
QuotientSpace >> project: anElement [
	^ AffineSubspace representative: anElement direction: self relations
]

{ #category : #morphisms }
QuotientSpace >> projection [
	"Answer the natural projection, or quotient map, or canonical homomorphism. This takes elements from the base module or vector space to the corresponding coset (an affine subspace) in the quotient."
	^ self propertyAt: #projection ifAbsentPut: [self buildProjection]
]

{ #category : #basis }
QuotientSpace >> rank [
	^ self relations corank
]

{ #category : #accessing }
QuotientSpace >> relation [
	^ EquivalenceRelation on: self base evaluating: [:x :y| self relations includes: x - y]
]

{ #category : #accessing }
QuotientSpace >> relations [
	^ self propertyAt: #relations
]

{ #category : #'accessing-private' }
QuotientSpace >> relations: aSubspace [
	self propertyAt: #relations put: aSubspace
]

{ #category : #accessing }
QuotientSpace >> relators [
	^ self relations generators
]

{ #category : #accessing }
QuotientSpace >> scalars [
	^ self relations scalars
]

{ #category : #elements }
QuotientSpace >> zero [
	^ self project: self base zero
]
