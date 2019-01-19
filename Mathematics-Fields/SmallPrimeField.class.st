"
Prime fields Z/pZ for small primes p, such that it is feasable to build exponentiation and logarithmic tables and accelerate arithmetic through table lookups.

The initialization of the tables is very fast. The main concern is memory usage. For a field Z/pZ, each of the two tables have p-1 elements. They are WordArrays (32 bits per entry), so a field Z/pZ uses about 8*(p-1) bytes of memory. For example, Z/65537 uses 524K of memory, and Z/1048583 (a 20-bits modulus) uses about 8M.

"
Class {
	#name : #SmallPrimeField,
	#superclass : #PrimeField,
	#instVars : [
		'expTable',
		'logTable'
	],
	#category : #'Mathematics-Fields-Finite'
}

{ #category : #private }
SmallPrimeField >> computeTables [
	| g x |
	expTable := WordArray new: modulus - 1. "n -> g^n"
	logTable := WordArray new: modulus - 1. "g^n -> n"
	g := self primitiveRoot representative.
	x := 1.
	1 to: modulus - 1 do: [:i|
		"g^n -> n:"
		logTable at: x put: i - 1.
		x := x * g \\ modulus.
		"n -> g^n:"
		expTable at: i put: x]
]

{ #category : #private }
SmallPrimeField >> elementClass [
	^ SmallPrimeFieldElement
]

{ #category : #accessing }
SmallPrimeField >> expTable [
	^ expTable
]

{ #category : #private }
SmallPrimeField >> inverseOfRepresentative: anInteger [
	anInteger == 0 ifTrue: [^ nil].
	anInteger == 1 ifTrue: [^ 1].
	^ expTable at: modulus - 1 - (logTable at: anInteger)
]

{ #category : #accessing }
SmallPrimeField >> logTable [
	^ logTable
]

{ #category : #'accessing-private' }
SmallPrimeField >> modulus: anInteger [
	super modulus: anInteger.
	self computeTables
]
