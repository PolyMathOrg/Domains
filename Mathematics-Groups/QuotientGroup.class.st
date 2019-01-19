"
Quotient groups (or factor groups) G/N (read ""G mod N""), i.e. the quotient of a group G by a normal subgroup N. The elements are the cosets of N (see Coset).

References:
	https://en.wikipedia.org/wiki/Quotient_group
"
Class {
	#name : #QuotientGroup,
	#superclass : #Group,
	#category : #'Mathematics-Groups'
}

{ #category : #'instance creation' }
QuotientGroup class >> on: aGroup by: aNormalSubgroup [
	^ self new base: aGroup; relations: aNormalSubgroup
]

{ #category : #random }
QuotientGroup >> atRandom: aRandomGenerator bits: bitSize [
	^ self project: (self base atRandom: aRandomGenerator bits: bitSize)
]

{ #category : #accessing }
QuotientGroup >> base [
	^ self propertyAt: #base
]

{ #category : #'accessing-private' }
QuotientGroup >> base: aGroup [
	self propertyAt: #base put: aGroup
]

{ #category : #private }
QuotientGroup >> buildProjection [
	"Answer the natural projection, or quotient map, or canonical homomorphism. This takes elements from the base group to the corresponding coset in the quotient group."
	| answer |
	answer := self base to: self evaluating: [:each| self project: each].
	answer name: Character pi asString.
	answer properties
		at: #kernel put: self relations;
		at: #image put: self;
		at: #rightInverse put: (self to: self base evaluating: [:each| each representative]).
	^ answer
]

{ #category : #private }
QuotientGroup >> defaultInverseMap [
	^ self endomorphisms ! self base inverseMap
]

{ #category : #private }
QuotientGroup >> defaultOperation [
	^ ((self, self) hom: self) ! self base operation
]

{ #category : #enumerating }
QuotientGroup >> do: aBlock [
	| visited |
	visited := Set new.
	self base do: [:each| | x |
		visited add: (x := self project: each) ifAbsent: [aBlock value: x]]
]

{ #category : #accessing }
QuotientGroup >> identity [
	^ self project: self base identity
]

{ #category : #testing }
QuotientGroup >> isQuotient [
	^ true
]

{ #category : #morphisms }
QuotientGroup >> lifting [
	"Answer the map from the receiver to the base group lifting the canonical projection."
	^ self projection section
]

{ #category : #printing }
QuotientGroup >> printOn: aStream [
	(self base printString includes: $/)
		ifTrue: [aStream nextPut: $(; print: self base; nextPut: $)]
		ifFalse: [aStream print: self base].
	aStream nextPut: $/.
	(self relations printString includes: $/)
		ifTrue: [aStream nextPut: $(; print: self relations; nextPut: $)]
		ifFalse: [aStream print: self relations]

]

{ #category : #morphisms }
QuotientGroup >> project: anElement [
	^ LeftCoset on: self relations representative: anElement
]

{ #category : #morphisms }
QuotientGroup >> projection [
	"Answer the natural projection, or quotient map, or canonical homomorphism. This takes elements from the base group to the corresponding coset in the quotient group."
	^ self propertyAt: #projection ifAbsentPut: [self buildProjection]
]

{ #category : #accessing }
QuotientGroup >> relation [
	| inv op |
	op := self base operation.
	inv := self base inverseMap.
	^ EquivalenceRelation on: self base evaluating: [:x :y| self relations includes: (op value: {x. inv value: y})]
]

{ #category : #accessing }
QuotientGroup >> relations [
	"Answer the relations subgroup, i.e. the normal subgroup by which we quotient."
	^ self propertyAt: #relations
]

{ #category : #'accessing-private' }
QuotientGroup >> relations: aNormalSubgroup [
	self propertyAt: #relations put: aNormalSubgroup
]

{ #category : #accessing }
QuotientGroup >> relators [
	^ self relations generators
]

{ #category : #accessing }
QuotientGroup >> size [
	^ super size
"	^ properties at: #size ifAbsentPut: [base indexOf: subgroup]"
]
