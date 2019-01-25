"
Quotient modules M/S (read ""M mod S"") of a given module M 'modulo' a submodule S, where both M and S are finite-rank free modules over a PID. These are the finitely-generated modules over a PID, presented as quotients of free modules.

The elements of a quotient module M/S are cosets S + x with x in M.

See QuotientSpace for quotients of vector spaces.

References:
	https://en.wikipedia.org/wiki/Quotient_module
	https://en.wikipedia.org/wiki/Quotient_space_(linear_algebra)
"
Class {
	#name : #QuotientModule,
	#superclass : #Module,
	#category : #'Mathematics-Modules'
}

{ #category : #'instance creation' }
QuotientModule class >> base: aModule relations: aSubmodule [
	^ self new base: aModule; relations: aSubmodule
]

{ #category : #'instance creation' }
QuotientModule class >> mod: aSubmodule [
	^ self new relations: aSubmodule
]

{ #category : #operations }
QuotientModule >> annihilator [
	"Answer the ideal of the scalars rings that annihilates all the elements in the receiver."
	self isFinite ifFalse: [^ self scalars zeroIdeal].
	^ self scalars * (self invariants inject: self scalars one into: [:result :each| result lcm: each])
]

{ #category : #accessing }
QuotientModule >> base [
	^ self propertyAt: #base ifAbsentPut: [self relations ambient]
]

{ #category : #'accessing-private' }
QuotientModule >> base: aModule [
	self propertyAt: #base put: aModule
]

{ #category : #private }
QuotientModule >> buildProjection [
	"Answer the quotient map, the canonical projection from the base module to the quotient module, i.e. the mapping pi:M->M/N that assigns to every x in M the coset x+N."
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
QuotientModule >> contains: anAffineSubspace [
	^ anAffineSubspace direction = self relations
]

{ #category : #accessing }
QuotientModule >> generators [
	^ self base generators collect: [:each| self project: each]
]

{ #category : #testing }
QuotientModule >> includes: anObject [
	^ (anObject isKindOf: AffineSubspace) and: [self contains: anObject]
]

{ #category : #accessing }
QuotientModule >> invariants [
	^ self matrix SNF
]

{ #category : #testing }
QuotientModule >> isFinite [
	^ (self invariants includes: 0) not and: [self invariants isEmpty not]
]

{ #category : #testing }
QuotientModule >> isNoetherian [
	"A module is called Noetherian if every submodule is finitely generated."
	^ self base isNoetherian
]

{ #category : #testing }
QuotientModule >> isQuotient [
	^ true
]

{ #category : #morphisms }
QuotientModule >> lifting [
	"Answer the map from the receiver to the base module lifting the canonical projection."
	^ self projection section
]

{ #category : #accessing }
QuotientModule >> matrix [
	"Answer the relative matrix of the receiver."
	^ Matrix rows: (self relations basis collect: [:each| (self base coordinatesOf: each) over: self scalars])
]

{ #category : #printing }
QuotientModule >> printOn: aStream [
	aStream print: self base; nextPut: $/; print: self relations
]

{ #category : #morphisms }
QuotientModule >> project: anElement [
	^ AffineSubspace representative: anElement direction: self relations
]

{ #category : #morphisms }
QuotientModule >> projection [
	"Answer the natural projection, or quotient map, or canonical homomorphism. This takes elements from the base module or vector space to the corresponding coset (an affine subspace) in the quotient."
	^ self propertyAt: #projection ifAbsentPut: [self buildProjection]
]

{ #category : #accessing }
QuotientModule >> relation [
	^ EquivalenceRelation
		on: self base
		evaluating: [ :x :y | self relations includes: x - y ]
]

{ #category : #accessing }
QuotientModule >> relations [
	^ self propertyAt: #relations
]

{ #category : #'accessing-private' }
QuotientModule >> relations: aSubmodule [
	self propertyAt: #relations put: aSubmodule
]

{ #category : #accessing }
QuotientModule >> relators [
	^ self relations generators
]

{ #category : #accessing }
QuotientModule >> scalars [
	^ self relations scalars
]

{ #category : #operations }
QuotientModule >> span: aCollection [
	"Answer the submodule spanned by the module elements in aCollection."
	^ (self base span: (aCollection apply: self lifting)) apply: self projection
]

{ #category : #operations }
QuotientModule >> span: aCollection over: aRing [
	"Answer the submodule spanned by the module elements in aCollection over aRing."
	aRing = self scalars ifFalse: [^ DomainError signal].
	^ self span: aCollection
]

{ #category : #elements }
QuotientModule >> zero [
	^ self project: self base zero
]
