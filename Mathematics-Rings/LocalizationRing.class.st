"
Localizations of a given commutative ring R at a given prime ideal P. The elements are fractions a / b with a in R and b in R \ P.
"
Class {
	#name : #LocalizationRing,
	#superclass : #Ring,
	#category : #'Mathematics-Rings'
}

{ #category : #'instance creation' }
LocalizationRing class >> at: anIdeal [
	^ self new propertyAt: #ideal put: anIdeal; yourself
]

{ #category : #examples }
LocalizationRing class >> exampleZZLocalizedAt2 [
	"Answer the localization of the integers at <2>.
	This is the ring of fractions with odd denominator."
	^ ZZ localizationAt: 2
]

{ #category : #elements }
LocalizationRing >> ! anObject [
	(self integers includes: anObject) ifTrue: [^ self embed: anObject].
	anObject isEvaluable ifTrue: [self integers ! anObject]. "assuming integral elements are the same objects as for the integers ring, just like Smalltalk Integer and Fraction."
	^ super ! anObject
]

{ #category : #comparing }
LocalizationRing >> < aRing [
	"Answer true if the receiver is strictly included in the argument."
	^ self ~= aRing and: [self <= aRing]
]

{ #category : #comparing }
LocalizationRing >> <= aRing [
	"Answer true if the receiver is included in the argument."
	self == aRing ifTrue: [^ true].
	(aRing isKindOf: Ring) ifFalse: [^ false].
	(aRing isKindOf: LocalizationRing)
		ifTrue: [^ self integers <= aRing integers and: [self ideal >= aRing ideal]].
	^ false
]

{ #category : #comparing }
LocalizationRing >> = anObject [
	self == anObject ifTrue: [^ true].
	^ (anObject isKindOf: LocalizationRing) and: [self ideal = anObject ideal]
]

{ #category : #comparing }
LocalizationRing >> >= aRing [
	"Answer true if the argument is included in the receiver."
	self == aRing ifTrue: [^ true].
	(aRing isKindOf: Ring) ifFalse: [^ false].
	(aRing isKindOf: LocalizationRing)
		ifTrue: [^ self integers >= aRing integers and: [self ideal <= aRing ideal]].
	^ self integers >= aRing
]

{ #category : #random }
LocalizationRing >> atRandom: aRandom [
	| a b |
	a := self integers atRandom: aRandom.
	[b := self integers atRandom: aRandom. self ideal includes: b] whileTrue.
	^ (self embed: a) / (self embed: b)
]

{ #category : #random }
LocalizationRing >> atRandom: aRandom bits: bitSize [
	| a b |
	bitSize < 2 ifTrue: [^ self embed: (self integers atRandom: aRandom bits: bitSize)].
	a := self integers atRandom: aRandom bits: bitSize/2.
	[b := self integers atRandom: aRandom bits: bitSize/2. self ideal includes: b] whileTrue.
	^ (self embed: a) / (self embed: b)
]

{ #category : #accessing }
LocalizationRing >> characteristic [
	^ self integers characteristic
]

{ #category : #morphisms }
LocalizationRing >> embed: anObject [
	^ anObject
]

{ #category : #morphisms }
LocalizationRing >> embedding [
	"Answer the embedding map from the integers ring into the receiver.
	This is also called the localization map."
	^ self propertyAt: #embedding ifAbsentPut: [(self integers to: self evaluating: [:x| self embed: x]) name: 'i']
]

{ #category : #operations }
LocalizationRing >> fractions [
	^ self integers fractions
]

{ #category : #morphisms }
LocalizationRing >> from: aDomain [
	"aDomain  self integers ifNotNil: [:aMorphism| ^ self embedding î aMorphism]."
	^ super from: aDomain
]

{ #category : #accessing }
LocalizationRing >> generators [
	^ (self integers generators ifNil: [^ nil]) apply: self embedding
]

{ #category : #comparing }
LocalizationRing >> hash [
	^ self ideal hash + self integers hash
]

{ #category : #accessing }
LocalizationRing >> ideal [
	^ self propertyAt: #ideal
]

{ #category : #'accessing-private' }
LocalizationRing >> ideal: anIdeal [
	self propertyAt: #ideal put: anIdeal
]

{ #category : #testing }
LocalizationRing >> includes: anObject [
	^ (self integers includes: anObject) or: [anObject isFractional and: [(self integers includes: anObject numerator) and: [(self ideal includes: anObject denominator) not]]]
]

{ #category : #accessing }
LocalizationRing >> integers [
	^ self ideal scalars
]

{ #category : #testing }
LocalizationRing >> isArtinian [
	"Answer true if the receiver is an Artinian ring, i.e. it satisfied the descending chain condition on ideals.
	In the non-commutative case, one should talk about 'left Artinian' or 'right Artinian' rings."
	self integers isArtinian ifTrue: [^ true]. "only if commutative?"
	^ super isArtinian
]

{ #category : #testing }
LocalizationRing >> isCommutative [
	^ true
]

{ #category : #testing }
LocalizationRing >> isEuclidean [
	"Answer true if the receiver is an Euclidean ring, i.e. it has division with remainder."
	self integers isEuclidean ifTrue: [^ true].
	^ super isEuclidean
]

{ #category : #testing }
LocalizationRing >> isField [
	^ self integers isIntegralDomain and: [self ideal isZero]
]

{ #category : #testing }
LocalizationRing >> isLocal [
	^ true
]

{ #category : #testing }
LocalizationRing >> isLocalization [
	^ true
]

{ #category : #testing }
LocalizationRing >> isNoetherian [
	self integers isNoetherian ifTrue: [^ true]. "is it iff?"
	^ super isNoetherian
]

{ #category : #testing }
LocalizationRing >> isReduced [
	"Answer true if the receiver has no non-zero nilpotent elements, or equivalently if it has no non-zero elements with square zero, i.e. x^2 = 0 implies x = 0."
	self integers isReduced ifTrue: [^ true]. "is it iff?"
	^ super isReduced
]

{ #category : #testing }
LocalizationRing >> isTrivial [
	^ self integers isTrivial "or: [self maximalIdeal includes: self zero]"
]

{ #category : #testing }
LocalizationRing >> isUnit: aFraction [
	"Answer true if the argument is invertible."
	^ (self ideal includes: aFraction numerator) not
]

{ #category : #accessing }
LocalizationRing >> maximalIdeal [
	"Answer the unique maximal ideal in the receiver."
	^ self * (self ideal generators collect: [:each| self embed: each])
]

{ #category : #accessing }
LocalizationRing >> one [
	^ self embed: self integers one
]

{ #category : #converting }
LocalizationRing >> over: aRing [
	"Change the base ring."
	^ self class at: (self ideal over: aRing)
]

{ #category : #printing }
LocalizationRing >> printOn: aStream [
	aStream print: self integers; nextPutAll: self maximalIdeal printString sub
]

{ #category : #accessing }
LocalizationRing >> x: anInteger [
	^ self embed: (self integers x: anInteger)
]

{ #category : #accessing }
LocalizationRing >> zero [
	^ self embed: self integers zero
]
