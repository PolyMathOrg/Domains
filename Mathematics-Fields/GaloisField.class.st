"
Finite nonprime fields, i.e. fields GF(p^r) with r>1. These are finite algebraic extensions of prime fields. See also PrimeField.
"
Class {
	#name : #GaloisField,
	#superclass : #GaloisRing,
	#category : #'Mathematics-Fields-Finite'
}

{ #category : #examples }
GaloisField class >> example1 [
	"The Galois field of order 2^3."
	^ GaloisField new: 8
]

{ #category : #examples }
GaloisField class >> example2 [
	"The Galois field of order 5^3."
	^ GaloisField new: 5 to: 3
]

{ #category : #'instance creation' }
GaloisField class >> new: q [
	"Answer the Galois field of order q = p^n."
	| factors n p |
	factors := q factors.
	factors asSet size = 1 ifFalse: [^ self error: 'not power of a prime'].
	n := factors size.
	p := factors anyOne.
	^ self new: p to: n
]

{ #category : #'instance creation' }
GaloisField class >> new: p to: n [
	"Answer the Galois field of order q = p^n."
	| F |
	F := PrimeField new: p.
	n = 1 ifTrue: [^ F].
	^ self polynomial: (F polynomials findIrreducibleOfDegree: n)
]

{ #category : #morphisms }
GaloisField >> automorphisms [
	"Answer the Galous group of the receiver."
	^ TransformationGroup new generators: {self frobenius}
]

{ #category : #testing }
GaloisField >> isAbelianExtension [
	"Galois fields are Abelian extensions."
	^ true
]

{ #category : #testing }
GaloisField >> isGaloisField [
	^ true
]

{ #category : #printing }
GaloisField >> printOn: aStream [
	aStream nextPut: Character FF; nextPutAll: self size printString sub
"	aStream nextPutAll: 'GF('; print: self characteristic; nextPutAll: self degree printString super; nextPut: $)"
]

{ #category : #accessing }
GaloisField >> universalPolynomial [
	"Answer the universal polynomial of which all elements of the receiver are roots."
	^ ZZ polynomials ! [:x| 'x^self size - x']
]

{ #category : #comparing }
GaloisField >> ~ aRing [
	"Any two finite fields of the same cardinality are isomorphic."
	^ aRing isField and: [self size = aRing size]
]
