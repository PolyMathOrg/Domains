"
Quotient rings (also called factor rings, difference rings or residue class rings). Their elements are residue classes (see ResidueClass and subclasses).

Given a commutative ring R and an ideal I of R, the quotient ring R/I (read 'R modulo I' or 'R mod I') is the set of cosets (residue clases) of I in R by the equivalence relation a ~ b if a - b is in I. If the ideal is maximal, the resulting quotient ring is a field. If it's only prime, the quotient ring is an integral domain.

The quotient ring R/I is equipped with the projection map that sends elements of R to their residue classes in R/I. The projection map is a canonical homomorphism of rings. See >>project: and >>projection.

References:
	https://en.wikipedia.org/wiki/Quotient_ring
"
Class {
	#name : #QuotientRing,
	#superclass : #Ring,
	#category : #'Mathematics-Rings'
}

{ #category : #examples }
QuotientRing class >> exampleZ6 [
	"The quotient ring of residue classes of integers modulo 6."
	| I |
	I := ZZ * 6.
	^ ZZ/I "alternatively, you can just write ZZ/6 or ZZ mod: 6."
]

{ #category : #examples }
QuotientRing class >> exampleZ6Elements [
	"The elements of the quotient ring of residue classes of integers modulo 6."
	^ (ZZ/6) elements
]

{ #category : #examples }
QuotientRing class >> exampleZ6Projection [
	"The canonical projection from the integers ring Z
	to the quotient ring of residue classes modulo 6."
	^ (ZZ/6) projection
]

{ #category : #'instance creation' }
QuotientRing class >> mod: anIdeal [
	^ self new relations: anIdeal
]

{ #category : #comparing }
QuotientRing >> = anObject [
	self == anObject
		ifTrue: [ ^ true ].
	(anObject isKindOf: QuotientRing)
		ifFalse: [ ^ false ].
	^ self relations = anObject relations 
]

{ #category : #random }
QuotientRing >> atRandom: aRandom [
	^ self project: (self relations remainderAtRandom: aRandom)
	"	^ self project: (self base atRandom: aRandom)" 
]

{ #category : #random }
QuotientRing >> atRandom: aRandom bits: bitSize [
	"	^ self atRandom: aRandom"

	^ self project: (self base atRandom: aRandom bits: bitSize) 
]

{ #category : #accessing }
QuotientRing >> base [
	^ self relations scalars 
]

{ #category : #private }
QuotientRing >> buildProjection [
	"Answer the natural projection, or quotient map, or canonical homomorphism. This takes elements from the base ring to the corresponding residue class in the quotient ring."
	| answer |
	answer := self base to: self evaluating: [:each| self project: each].
	answer name: 'Pi'.
	answer properties
		at: #kernel put: self relations;
		at: #image put: self;
		at: #rightInverse put: (self to: self base evaluating: [:each| each representative]).
	^ answer
]

{ #category : #accessing }
QuotientRing >> codimension [
	"Answer the Krull codimension of the receiver."

	^ self base dimension - self dimension
]

{ #category : #morphisms }
QuotientRing >> conjugation [
	"Answer the companion automorphism of the receiver, i.e. the Frobenius automorphism."

	^ self frobenius 
]

{ #category : #enumerating }
QuotientRing >> do: aBlock [
	| visited |
	self flag: #fix. "does this work in any ring? depends on ring|#do:"
	visited := Set new.
	self base do: [:each|
		| q |
		visited add: (q := self project: each) ifPresent: [^ self].
		aBlock value: q]
]

{ #category : #private }
QuotientRing >> elementClass [
	^ ResidueClass 
]

{ #category : #accessing }
QuotientRing >> generators [
	^ (self base generators ifNil: [ ^ nil ]) apply: self projection 
]

{ #category : #comparing }
QuotientRing >> hash [
	^ self relations hash 
]

{ #category : #private }
QuotientRing >> idealClass [
	^ QuotientIdeal
]

{ #category : #testing }
QuotientRing >> includes: anObject [
	(anObject class == #ResidueClass) ifFalse: [^ false].
	^ self base includes: anObject representative
]

{ #category : #morphisms }
QuotientRing >> inverseOf: anElement [
	^ self project: ((self relations inverseOf: anElement representative) ifNil: [^ nil])
]

{ #category : #testing }
QuotientRing >> isArtinian [
	"Answer true if the receiver is an Artinian ring, i.e. it satisfied the descending chain condition on ideals.
	In the non-commutative case, one should talk about 'left Artinian' or 'right Artinian' rings."
	self base isArtinian ifTrue: [^ true]. "only if commutative?"
	^ super isArtinian
]

{ #category : #testing }
QuotientRing >> isCommutative [
	self base isCommutative ifTrue: [^ true]. "if the ring is not commutative, we dont know if the quotient is or not"
	^ super isCommutative
]

{ #category : #testing }
QuotientRing >> isField [
	"Answer true if the receiver forms a residue field."

	^ self base isTrivial not
		and: [ self base isCommutative and: [ self relations isMaximal ] ]
]

{ #category : #testing }
QuotientRing >> isIntegralDomain [
	(self base isTrivial not and: [self base isCommutative])
		ifTrue: [^ self relations isPrime].
	self isIntegrallyClosedDomain
		ifTrue: [^ true].
	^ self notYetImplemented
]

{ #category : #testing }
QuotientRing >> isLocal [
	^ self base isLocal or: [super isLocal]
]

{ #category : #testing }
QuotientRing >> isNoetherian [
	^ self base isNoetherian or: [super isNoetherian]
]

{ #category : #testing }
QuotientRing >> isQuotient [
	^ true
]

{ #category : #testing }
QuotientRing >> isReduced [
	"Answer true if the receiver has no non-zero nilpotent elements, or equivalently if it has no non-zero elements with square zero, i.e. x^2 = 0 implies x = 0.
	A quotient ring is reduced iff the relations ideal is radical."
	^ self relations isRadical
]

{ #category : #testing }
QuotientRing >> isTrivial [
	"The trivial ring is the zero ring with a single element 0 = 1."
	^ self relations isOne
]

{ #category : #morphisms }
QuotientRing >> isUnit: anElement [
	"Answer true if the argument is invertible."
	^ (self inverseOf: anElement) notNil
]

{ #category : #morphisms }
QuotientRing >> lifting [
	"Answer the map from the receiver to the base ring lifting the canonical projection."

	^ self projection section
]

{ #category : #accessing }
QuotientRing >> maximalIdeal [
	"If the receiver is a local ring, answer the unique maximal ideal."
	self base isLocal ifTrue: [^ self base maximalIdeal apply: self projection].
	^ super maximalIdeal
]

{ #category : #accessing }
QuotientRing >> modulus [
	^ self relations generator
]

{ #category : #accessing }
QuotientRing >> one [
	^ self representative: self base one
]

{ #category : #converting }
QuotientRing >> over: aRing [
	^ (self relations over: aRing) quotientRing
]

{ #category : #enumerating }
QuotientRing >> primeIdealsDo: aBlock [
	self isField ifTrue: [aBlock value: self zeroIdeal. ^ self].
	self base primeIdealsDo: [:each| each >= self relations ifTrue: [aBlock value: (each apply: self projection)]]
]

{ #category : #printing }
QuotientRing >> printOn: aStream [
	(self base printString includes: $/)
		ifTrue: [ aStream
				nextPut: $(;
				print: self base;
				nextPut: $) ]
		ifFalse: [ aStream print: self base ].
	aStream
		nextPut: $/;
		print: self relations
]

{ #category : #morphisms }
QuotientRing >> project: anElement [
	^ self representative: (self relations reduce: anElement)
]

{ #category : #morphisms }
QuotientRing >> projection [
	"Answer the natural projection, or quotient map, or canonical homomorphism. This takes elements from the base ring to the corresponding residue class in the quotient ring."
	^ self propertyAt: #projection ifAbsentPut: [self buildProjection]
]

{ #category : #accessing }
QuotientRing >> relation [
	^ EquivalenceRelation
		on: self base
		evaluating: [ :a :b | self relations includes: a - b ]
]

{ #category : #accessing }
QuotientRing >> relations [
	^ self propertyAt: #relations
]

{ #category : #'accessing-private' }
QuotientRing >> relations: anIdeal [
	self propertyAt: #relations put: anIdeal
]

{ #category : #accessing }
QuotientRing >> relators [
	^ self relations generators
]

{ #category : #private }
QuotientRing >> representative: anElement [
	"Answer the residue class corresponding to the given representative (which is already reduced)."

	^ self elementClass in: self representative: anElement
]

{ #category : #accessing }
QuotientRing >> zero [
	^ self representative: self base zero
]
