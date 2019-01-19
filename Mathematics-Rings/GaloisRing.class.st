"
The Galois ring GR(p^n,m) is a Galois extension of degree m of the ring Z/(p^n)Z of characteristic p^n. This is the unique (up to isomorphism) extension of degree m of the ring Z/(p^n)Z of integers modulo p^n (see PrimeRing). When n=1 they are fields (see GaloisField).

Galois rings GR(p^n,m) are local rings with maximal ideal <p>, and <p> is also the set of zero-divisors.

The subrings of GR(p^n,m) correspond to the positive divisors of m.

More generally, any finite local ring can be constructed as a finitely-generated GR(p^n,m)-algebra, i.e. a quotient of a polynomial ring (in a number of indeterminates) with coefficients in a Galois ring modulo a primary ideal of the polynomial ring (see AffineRing).
"
Class {
	#name : #GaloisRing,
	#superclass : #AlgebraicExtension,
	#category : #'Mathematics-Rings-Finite'
}

{ #category : #examples }
GaloisRing class >> example1 [
	"The Galois ring of characteristic 2^3 and order 2^6."
	^ GaloisRing new: 2 to: 3 to: 6
]

{ #category : #'instance creation' }
GaloisRing class >> new: q to: m [
	"Answer the Galois ring of characteristic q and order q^m."
	| factors n p |
	factors := q factors.
	factors asSet size = 1 ifFalse: [^ self error: 'not power of a prime'].
	n := factors size.
	p := factors anyOne.
	^ self new: p to: n to: m
]

{ #category : #'instance creation' }
GaloisRing class >> new: p to: n to: m [
	"Answer the Galois ring of characteristic p^n and order p^(n*m)."
	| F Fp f |
	n = 1 ifTrue: [^ GaloisField new: p to: m].
	F := PrimeRing new: p to: n.
	m = 1 ifTrue: [^ F].
	Fp := PrimeField new: p.
	f := Fp polynomials findIrreducibleOfDegree: m.
	"Hensel lift to F"
	f := f lift apply: F projection.
	^ self polynomial: f
]

{ #category : #enumerating }
GaloisRing >> idealsDo: aBlock [
	| a |
	aBlock value: self * 0.
	a := self one.
	self exponent timesRepeat:
		[aBlock value: self * a.
		a := a * self p]
]

{ #category : #testing }
GaloisRing >> isChainRing [
	"A chain ring is a ring whose ideals form a chain under inclusion.
	Galois rings are chain rings."
	^ true
]

{ #category : #testing }
GaloisRing >> isEuclidean [
	"Galois rings are euclidean."
	^ true
]

{ #category : #testing }
GaloisRing >> isFinite [
	^ true
]

{ #category : #testing }
GaloisRing >> isGaloisExtension [
	^ true
]

{ #category : #testing }
GaloisRing >> isGaloisRing [
	^ true
]

{ #category : #testing }
GaloisRing >> isLocal [
	^ true
]

{ #category : #operations }
GaloisRing >> isUnit: anElement [
	"Answer true if the argument is invertible."
	^ (self maximalIdeal contains: anElement) not
]

{ #category : #operations }
GaloisRing >> isZeroDivisor: anElement [
	"Answer true if there exists a nonzero element that multiplied by the argument is zero."
	^ self maximalIdeal contains: anElement
]

{ #category : #accessing }
GaloisRing >> maximalIdeal [
	^ self * self scalars p
]

{ #category : #operations }
GaloisRing >> nilradical [
	"Answer the ideal consisting of all nilpotent elements, i.e. all x such that there exists some n with x^n = 0. It is the intersection of all prime ideals.
	A finite ring is a Galois ring iff its nilradical is of the form <p> for some prime p. This is also the unique maximal ideal."
	^ self maximalIdeal
]

{ #category : #accessing }
GaloisRing >> p [
	^ self scalars p
]

{ #category : #accessing }
GaloisRing >> primitiveRoot [
	"Answer a primitive root (or basic primitive element) of the receiver.
	For GR(p^n,r), a basic primitive element is an element of multiplicative order p^r - 1, which is a root of a basic primitive polynomial of degree r over Z/(p^n)Z and dividing x^(p^r - 1) - 1 in Z/(p^n)Z[x]. Powers of this element form a Teichmuller set."
	^ self notYetImplemented
]

{ #category : #printing }
GaloisRing >> printOn: aStream [
	aStream nextPutAll: 'GR('; print: self scalars p; nextPutAll: self scalars exponent printString super; nextPut: $,; print: self degree; nextPut: $)
]

{ #category : #accessing }
GaloisRing >> teichmuller [
	"Answer a Teichmuller set of the receiver.
	Any element of GR(p^n,r) can be written as a polynomial in p with coefficients in the Teichmuller set."
	| answer w |
	answer := OrderedCollection new: self characteristic.
	answer add: self zero; add: self one.
	w := self primitiveRoot.
	self characteristic - 2 timesRepeat: [answer add: (answer last * w)].
	^ answer
]

{ #category : #morphisms }
GaloisRing >> to: aCodomain [
	aCodomain isGaloisRing ifFalse: [^ super to: aCodomain].
	"The subrings of GR(p^n,m) correspond to the positive divisors of m. If aCodomain is a suitable overring, answer an embedding of the receiver into the overring."
	'(self characteristic = aCodomain characteristic and: [self degree | aCodomain degree])
			ifTrue: [^ self into: aCodomain evaluating: [:x| aCodomain project: (x representative ^ (self p ^ (aCodomain degree / self degree)))]]'.
	"Given GR(p^n,r), there's a projection to GR(p^m,r) for all m<=n, with kernel <p^m>. This accounts for all ideals."
	(self p = aCodomain p and: [self degree = aCodomain degree])
		ifTrue: ['self scalars ' aCodomain scalars ifNotNil: [:aMorphism| ^ self to: aCodomain evaluating: [:x| aCodomain project: (x representative apply: aMorphism)]]].
	^ super to: aCodomain
]

{ #category : #operations }
GaloisRing >> zeroDivisors [
	^ self maximalIdeal
]
