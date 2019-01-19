"
Residue class rings Z/(p^n)Z of integers modulo p^n.

These are the simplest examples of Galois rings, GR(p^n,1). They are local rings with maximal ideal <p>, and <p> is also the set of zero-divisors as well as nilpotent elements. Other Galois rings are constructed by finite algebraic extensions (see GaloisRing).

These are also the simplest examples of 'chain rings', rings whose ideals form a chain under inclusion. A finite chain ring is a principal ideal ring, and its maximal ideal is the nilradical (the set of nilpotent elements).

There are canonical projections from Z/(p^n)Z to Z/(p^m)Z for any 1 <= m <= n.
"
Class {
	#name : #PrimeRing,
	#superclass : #ModularIntegerRing,
	#category : #'Mathematics-Rings-Finite'
}

{ #category : #examples }
PrimeRing class >> example1 [
	"The Galois ring Z/<5^3>:"
	^ PrimeRing new: 5 to: 3
]

{ #category : #examples }
PrimeRing class >> example2 [
	"Another way to create the Galois ring Z/<5^3>.
	This is less efficient because internally it performs a factorization."
	^ 'ZZ/(5^3)'
]

{ #category : #examples }
PrimeRing class >> example3 [
	"The canonical ring homomorphism from a prime ring Z/(p^n)Z to Z/pZ:"
	^ 'ZZ/(5^3)  (ZZ/5)'
]

{ #category : #'instance creation' }
PrimeRing class >> new: p to: n [
	n = 1 ifTrue: [^ PrimeField new: p].
	^ self new p: p to: n
]

{ #category : #accessing }
PrimeRing >> degree [
	"Answer the degree of the receiver as an algebraic extension (as a Galois ring)."
	^ 1
]

{ #category : #accessing }
PrimeRing >> exponent [
	^ self propertyAt: #exponent ifAbsentPut: [self modulusFactors size]
]

{ #category : #operations }
PrimeRing >> extension: aPolynomial [
	"Answer the Galois overring of the receiver defined by the given irreducible polynomial."
	aPolynomial scalars = self ifFalse: [DomainError signal: 'polynomial coefficients not from this ring'].
	aPolynomial parent isUnivariate ifFalse: [DomainError signal: 'not univariate poylnomial'].
	^ GaloisRing polynomial: aPolynomial
]

{ #category : #enumerating }
PrimeRing >> idealsDo: aBlock [
	"The ideals of Z/(p^n)Z are {0} and <p^i> for 0 <= i < n-1."
	| a |
	aBlock value: self * 0.
	a := self one.
	self exponent timesRepeat:
		[aBlock value: self * a.
		a := a * self p]
]

{ #category : #testing }
PrimeRing >> isChainRing [
	"A chain ring is a ring whose ideals form a chain under inclusion.
	Prime rings, and more generally Galois rings, are chain rings."
	^ true
]

{ #category : #testing }
PrimeRing >> isEuclidean [
	"Galois rings are euclidean."
	^ true
]

{ #category : #testing }
PrimeRing >> isField [
	^ self exponent = 1
]

{ #category : #testing }
PrimeRing >> isGaloisRing [
	^ true
]

{ #category : #testing }
PrimeRing >> isLocal [
	^ true
]

{ #category : #testing }
PrimeRing >> isNilpotent: anElement [
	"Answer true if anElement^n = 0 for some integer n >= 1."
	^ self isZeroDivisor: anElement
]

{ #category : #testing }
PrimeRing >> isPIR [
	"All nontrivial ideals are of the form <p^i>."
	^ true
]

{ #category : #testing }
PrimeRing >> isUnit: anElement [
	"Answer true if the argument is invertible."
	^ (self p | anElement representative) not
]

{ #category : #testing }
PrimeRing >> isZeroDivisor: anElement [
	"Answer true if there exists a nonzero element that multiplied by the argument is zero."
	^ self p | anElement representative
]

{ #category : #accessing }
PrimeRing >> maximalIdeal [
	^ self * self p
]

{ #category : #operations }
PrimeRing >> nilradical [
	"Answer the ideal consisting of all nilpotent elements, i.e. all x such that there exists some n with x^n = 0. It is the intersection of all prime ideals.
	A finite ring is a Galois ring iff its nilradical is of the form <p> for some prime p. This is also the unique maximal ideal."
	^ self maximalIdeal
]

{ #category : #accessing }
PrimeRing >> p [
	^ self propertyAt: #p ifAbsentPut: [self modulusFactors anyOne]
]

{ #category : #'accessing-private' }
PrimeRing >> p: aPrime to: anInteger [
	self modulus: 'aPrime^anInteger'.
	self propertyAt: #modulusFactors put: (Bag new add: aPrime withOccurrences: anInteger; yourself)
]

{ #category : #accessing }
PrimeRing >> primeSubfield [
	^ self propertyAt: #primeSubfield ifAbsentPut: [PrimeField new: self p]
]

{ #category : #printing }
PrimeRing >> printOn: aStream [
	aStream print: self base; nextPut: $/; print: self p; nextPutAll: self exponent printString super; print: self base
]

{ #category : #morphisms }
PrimeRing >> to: aCodomain [
	"Cannonical projection from Z/(p^n)Z to Z/(p^m)Z, 1 <= m <= n."
	((aCodomain isKindOf: PrimeRing) and: [aCodomain p = self p and: [aCodomain exponent < self exponent]])
		ifTrue: [^ self to: aCodomain evaluating: [:x| aCodomain project: x representative]].
	^ super to: aCodomain
]

{ #category : #operations }
PrimeRing >> zeroDivisors [
	"The zero-divisors of a Galois ring Z/<p^k> constitute the unique maximal ideal <p>."
	^ self maximalIdeal
]
