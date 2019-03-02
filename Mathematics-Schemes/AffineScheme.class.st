"
An affine scheme is the prime spectrum Spec(R) of a commutative ring R, equipped with a sheaf of local rings (which makes it a locally ringed space). As a set, their elements are the prime ideals of the associated coordinate ring R.

In scheme theory, affine schemes are the fundamental building blocks of general schemes. Any scheme can be constructed by gluing together finitely many affine schemes, and conversely schemes that are not affine can be covered by a finite number of affine patches.
"
Class {
	#name : #AffineScheme,
	#superclass : #Scheme,
	#category : #'Mathematics-Schemes'
}

{ #category : #'instance creation' }
AffineScheme class >> coordinateRing: aRing [
	^ self new coordinateRing: aRing
]

{ #category : #examples }
AffineScheme class >> example1 [
	"Spec(Z), the prime spectrum of the rational integers.
	This is the initial object in the category of schemes."

	^ ZZ spec
]

{ #category : #examples }
AffineScheme class >> example2 [
	"Spec(Z/6Z), the prime spectrum of the residue class ring
	of integers modulo 6, as a set it is the set of prime
	ideals of Z/6Z:"

	^ (ZZ / 6) spec asSet
]

{ #category : #comparing }
AffineScheme >> < aScheme [
	^ self ideal > aScheme ideal
]

{ #category : #comparing }
AffineScheme >> <= aScheme [
	^ self ideal >= aScheme ideal
]

{ #category : #comparing }
AffineScheme >> = anObject [
	^ (anObject isKindOf: self species) and: [self coordinateRing = anObject coordinateRing]
]

{ #category : #accessing }
AffineScheme >> ambient [
	^ self propertyAt: #ambient ifAbsent: [self coordinateRing isQuotient ifTrue: [self coordinateRing base spec] ifFalse: [self]]
]

{ #category : #accessing }
AffineScheme >> base [
	"Answer the base scheme of the receiver."
	^ self scalars spec
]

{ #category : #testing }
AffineScheme >> contains: anIdeal [
	"Answer true if the receiver contains the given point (a prime ideal of its coordinate ring)."
	^ true
]

{ #category : #accessing }
AffineScheme >> coordinateRing [
	"Answer the affine coordinate ring."
	^ self propertyAt: #coordinateRing
]

{ #category : #'accessing-private' }
AffineScheme >> coordinateRing: aCommutativeRing [
	self propertyAt: #coordinateRing put: aCommutativeRing
]

{ #category : #accessing }
AffineScheme >> dimension [
	"Answer the dimension of the highest dimensional component of the receiver.
	This is the Krull dimension of the coordinate ring."
	^ self coordinateRing dimension
]

{ #category : #enumerating }
AffineScheme >> do: aBlock [
	self coordinateRing primeIdealsDo: aBlock
]

{ #category : #operations }
AffineScheme >> dot: aScheme [ "ï "
	"Answer the intersection of the receiver and the argument."
	self ambient = aScheme ambient ifFalse: [^ DomainError signal: 'ambients don''t match'].
	^ self ambient subscheme: self ideal + aScheme ideal
]

{ #category : #accessing }
AffineScheme >> functionField [
	"Answer the function field (or field of rational functions) of the receiver. This is the fractions field of the coordinate ring and it's noted K(V) (analogous to the coordinate ring noted K[V]).
	This assumes the receiver is reduced (or equivalently, that the coordinate ring R is an integral domain). The definition of function field can be extended to the case of non-reduced schemes as Frac(R/N) where N is the nilradical of R."
	^ self coordinateRing fractions
]

{ #category : #comparing }
AffineScheme >> hash [
	^ self coordinateRing hash
]

{ #category : #accessing }
AffineScheme >> ideal [
	"Answer the defining ideal of the receiver."
	^ self coordinateRing isQuotient ifTrue: [self coordinateRing relations] ifFalse: [self coordinateRing zeroIdeal]
]

{ #category : #testing }
AffineScheme >> includes: anObject [
	^ (anObject isKindOf: Ideal) and: [anObject scalars = self coordinateRing and: [anObject isPrime]]
]

{ #category : #testing }
AffineScheme >> isAffine [
	^ true
]

{ #category : #testing }
AffineScheme >> isInitial [
	^ self coordinateRing isTerminal
]

{ #category : #testing }
AffineScheme >> isIrreducible [
	^ self coordinateRing isIntegralDomain
]

{ #category : #testing }
AffineScheme >> isNoetherian [
	^ self coordinateRing isNoetherian
]

{ #category : #testing }
AffineScheme >> isReduced [
	^ self coordinateRing isReduced
]

{ #category : #testing }
AffineScheme >> isTerminal [
	^ self coordinateRing isInitial
]

{ #category : #converting }
AffineScheme >> over: aRing [
	^ self class coordinateRing: (self coordinateRing over: aRing)
]

{ #category : #printing }
AffineScheme >> printOn: aStream [
	aStream
		nextPutAll: 'Spec ';
		print: self coordinateRing
]

{ #category : #accessing }
AffineScheme >> scalars [
	"Answer the base ring of the receiver."
	^ self coordinateRing scalars
]

{ #category : #private }
AffineScheme >> species [
	^ AffineScheme
]

{ #category : #operations }
AffineScheme >> subscheme: anObject [
	"Answer the subscheme defined by anObject, as subscheme of the ambient space.
	This makes sense, for example, for closed subschemes of affine or projective space, and anObject can be an element or an ideal of the coordinate ring."
	| I |
	self isEmbedded ifTrue: [^ self dot: (self ambient subscheme: anObject)].
	I := (anObject isKindOf: Ideal)
		ifTrue: [anObject] ifFalse: [self coordinateRing * anObject].
	^ (self coordinateRing / I) spec
		propertyAt: #ambient put: self; yourself
]

{ #category : #operations }
AffineScheme >> union: aScheme [
	"Answer the union of the receiver and the argument."
	self ambient = aScheme ambient ifFalse: [^ DomainError signal: 'ambients don''t match'].
	^ 'self ambient subscheme: self ideal ï aScheme ideal'

"alternatively:
	^ self class on: self ambient ideal: ideal * aScheme ideal
although the intersection is harder to compute, it behaves better with radicalization, because the intersection of two radical ideals is radical and we don't need to compute radicals again"
]
