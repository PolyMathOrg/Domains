"
In coding theory, a polynomial code is a type of linear code whose set of valid codewords consists of those polynomials (usually of some fixed length) that are divisible by some fixed polynomial (of shorter length, called the generator polynomial).

References:
	https://en.wikipedia.org/wiki/Polynomial_code

"
Class {
	#name : #PolynomialCode,
	#superclass : #LinearCode,
	#instVars : [
		'generator'
	],
	#category : #'Mathematics-Codes'
}

{ #category : #examples }
PolynomialCode class >> G23 [
	"Answer the perfect binary Golay code [23,12,7]."

	| g |
	g := (ZZ/2) polynomials ! [:x| (x raisedTo: 11) + (x raisedTo: 10) + (x raisedTo: 6) + (x raisedTo: 5) + (x raisedTo: 4) + (x raisedTo: 2) + 1].
	^ self new: 23 generator: g
]

{ #category : #examples }
PolynomialCode class >> H7 [
	"Answer the Hamming code [7,4,3]."

	^ self new: 7 generator: (ZZ/2) polynomials ! [:x| (x raisedTo: 3) + x + 1]
]

{ #category : #'instance creation' }
PolynomialCode class >> generator: aPolynomial [
	^ self new: aPolynomial degree generator: aPolynomial
]

{ #category : #'instance creation' }
PolynomialCode class >> new: n generator: aPolynomial [
	| V W subspace | 
	V := aPolynomial parent filtrationAt: n - 1.
	W := aPolynomial parent filtrationAt: n - aPolynomial degree - 1.
	subspace := V span: (W asArray collect: [ :f | aPolynomial * f ]).
	^ (self subspace: subspace) generator: aPolynomial
]

{ #category : #'encoding/decoding' }
PolynomialCode >> decode: aPolynomial [
	self flag: #fix. "add error-detection and correction"
	^ aPolynomial // generator
]

{ #category : #'encoding/decoding' }
PolynomialCode >> encode: aPolynomial [
	| f |
	f := aPolynomial shift: generator degree.
	^ f - (f \\ generator)
]

{ #category : #accessing }
PolynomialCode >> generator [
	^ generator
]

{ #category : #'accessing-private' }
PolynomialCode >> generator: aPolynomial [
	generator := aPolynomial
]

{ #category : #testing }
PolynomialCode >> includes: aCodeword [
	^ aCodeword | generator
]

{ #category : #testing }
PolynomialCode >> isCyclic [
	| n x |
	n := self length.
	x := generator parent x.
	^ 'generator | (x ^ n - x parent one)'
]

{ #category : #accessing }
PolynomialCode >> rank [
	^ self length - generator degree
]

{ #category : #accessing }
PolynomialCode >> size [
	^ 'generator parent scalars size ^ (self length - generator degree)'
]
