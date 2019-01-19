"
(Commutative) monoids of monomials in n indeterminates. Elements are instances of Monomial.

The number of indeterminates is called the rank. The indeterminates are referred by index (positive integer numbers), and can be given names that are used when printing.

Monomials have an associated monomial ordering. See MonomialOrdering.

See also FreeMonoid, the non-commutative analog.

"
Class {
	#name : #FreeAbelianMonoid,
	#superclass : #Monoid,
	#instVars : [
		'rank',
		'ordering'
	],
	#category : #'Mathematics-Monomials'
}

{ #category : #examples }
FreeAbelianMonoid class >> example1 [
	"The free abelian monoid in 3 indeterminates:"
	^ FreeAbelianMonoid new: 3
]

{ #category : #examples }
FreeAbelianMonoid class >> example2 [
	"The free abelian monoid in 3 indeterminates with lexicographic monomial ordering:"
	^ FreeAbelianMonoid new: 3 ordering: #lex
]

{ #category : #'instance creation' }
FreeAbelianMonoid class >> new: anInteger [
	^ self new: anInteger ordering: #grevlex
]

{ #category : #'instance creation' }
FreeAbelianMonoid class >> new: anInteger ordering: aMonomialOrdering [
	^ self new rank: anInteger; ordering: aMonomialOrdering
]

{ #category : #elements }
FreeAbelianMonoid >> ! aMonomial [
	| exponents n |
	exponents := aMonomial exponents.
	(n := exponents size) = rank
		ifFalse:
			[n > rank
				ifTrue: [exponents := exponents copyFrom: 1 to: rank]
				ifFalse: [exponents := exponents, (ByteArray new: rank - n) "hack"]].
	^ self exponents: exponents
]

{ #category : #comparing }
FreeAbelianMonoid >> = anObject [
	^ (anObject isKindOf: FreeAbelianMonoid) and: [anObject rank = rank]
]

{ #category : #enumerating }
FreeAbelianMonoid >> allMonomialsOfDegree: anInteger [
	| answer |
	answer := Set new.
	anInteger partitionsDo: [:partition|
		partition size <= self rank
			ifTrue:
				[(1 to: self rank) combinations: partition size atATimeDo: [:variables|
					partition permutationsDo: [:exponents|
						| monomial |
						monomial := self identity.
						variables with: exponents do: [:i :r| monomial := monomial * (self x: i to: r)].
						answer add: monomial]]]].
	^ answer asArray sort reverse
]

{ #category : #random }
FreeAbelianMonoid >> atRandom: aRandom bits: bitSize [
	^ self exponents: (('NN ^ self rank atRandom: aRandom bits: bitSize') collect: [:x| x - 1]) asArray
]

{ #category : #enumerating }
FreeAbelianMonoid >> do: aBlock [
	'NN ^ self rank do: [:each| aBlock value: (self exponents: (each collect: [:x| x - 1]) asArray)]'
]

{ #category : #elements }
FreeAbelianMonoid >> exponents: anArray [
	anArray size = rank ifFalse: [self error: 'exponents size doesn''t match rank'].
	^ (Monomial exponents: anArray) parent: self
]

{ #category : #accessing }
FreeAbelianMonoid >> generators [
	^ (1 to: rank) collect: [:i| self x: i]
]

{ #category : #comparing }
FreeAbelianMonoid >> hash [
	^ self rank + self class hash
]

{ #category : #accessing }
FreeAbelianMonoid >> identity [
	^ (Monomial new: rank) parent: self
]

{ #category : #testing }
FreeAbelianMonoid >> includes: aMonomial [
	^ (aMonomial isKindOf: Monomial) and: [aMonomial lastIndeterminate <= rank]
]

{ #category : #accessing }
FreeAbelianMonoid >> indeterminates [
	^ 1 to: rank
]

{ #category : #testing }
FreeAbelianMonoid >> isCommutative [
	^ true
]

{ #category : #testing }
FreeAbelianMonoid >> isFinite [
	^ false
]

{ #category : #testing }
FreeAbelianMonoid >> isUnivariate [
	^ self rank = 1
]

{ #category : #accessing }
FreeAbelianMonoid >> names [
	"Answer the indeterminate names to use when printing monomials."
	^ self propertyAt: #names ifAbsent: [self isUnivariate ifTrue: [#(x)]]
]

{ #category : #'accessing-private' }
FreeAbelianMonoid >> names: anArray [
	"Set indeterminate names to use when printing monomials."
	self propertyAt: #names put: anArray
]

{ #category : #converting }
FreeAbelianMonoid >> orderedBy: aMonomialOrdering [
	^ self copy ordering: aMonomialOrdering
]

{ #category : #accessing }
FreeAbelianMonoid >> ordering [
	^ ordering
]

{ #category : #'accessing-private' }
FreeAbelianMonoid >> ordering: aMonomialOrdering [
	ordering := aMonomialOrdering isSymbol
		ifTrue: [MonomialOrdering perform: (aMonomialOrdering,':') asSymbol with: (1 to: self rank)]
		ifFalse: [aMonomialOrdering]
]

{ #category : #printing }
FreeAbelianMonoid >> printOn: aStream [
	aStream nextPut: $[.
	self indeterminates
		do: [:i| aStream print: (self x: i)]
		separatedBy: [aStream nextPut: $,].
	aStream nextPutAll: ']*'
]

{ #category : #accessing }
FreeAbelianMonoid >> rank [
	^ rank
]

{ #category : #'accessing-private' }
FreeAbelianMonoid >> rank: anInteger [
	rank := anInteger
]

{ #category : #accessing }
FreeAbelianMonoid >> size [
	^ self rank > 0 ifTrue: [Aleph new] ifFalse: [1]
]

{ #category : #elements }
FreeAbelianMonoid >> x: anInteger [
	^ self x: anInteger to: 1
]

{ #category : #elements }
FreeAbelianMonoid >> x: anInteger to: exponent [
	^ (Monomial new: rank x: anInteger to: exponent) parent: self
]
