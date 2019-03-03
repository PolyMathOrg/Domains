"
Number Theoretic Transforms, the analog of DFTs for the field of integers modulo a prime p. Special cases are the Fermat Number Transform (p = 2^k + 1) and the Mersenne Number Transform (p = 2^k - 1).

The (pseudo) number theoretic transform may be meaningful in the ring Z/<m> even when the modulo m is not prime, provided a principal root of order n exists.
"
Class {
	#name : #NTT,
	#superclass : #Object,
	#instVars : [
		'modulus',
		'primitive'
	],
	#category : #'Mathematics-Algorithms'
}

{ #category : #'instance creation' }
NTT class >> modulo: anInteger [
	"anInteger must be prime"
	^ self new modulus: anInteger
]

{ #category : #running }
NTT >> inverseValue: input [
	"naive algorithm, O(n^2)"

^ (1 to: input size) collect: [:i| ((1 to: input size) sum: [:j| (primitive negated raisedTo: i*j modulo: modulus) * (input at: j) \\ modulus]) \\ 7]

]

{ #category : #accessing }
NTT >> modulus [
	^ modulus
]

{ #category : #initialization }
NTT >> modulus: anInteger [
	self modulus: anInteger primitive: anInteger primitiveRoot
]

{ #category : #initialization }
NTT >> modulus: anInteger primitive: anotherInteger [
	modulus := anInteger.
	primitive := anotherInteger
]

{ #category : #accessing }
NTT >> primitive [
	^ primitive
]

{ #category : #running }
NTT >> value: input [
	"naive algorithm, O(n^2)"

	^ (1 to: input size) collect: [:i| ((1 to: input size )sum: [:j| (primitive raisedTo: i*j modulo: modulus) * (input at: j) \\ modulus] ) \\ 7]
]
