"
This is the Chinese Remainder Theorem. My instances find solutions to systems of linear Diophantine equations x = x_i (mod m_i). The algorithm works on any Euclidean domain.

Input: x_1...x_k, k elements in an Euclidean domain, and m_1,...,m_k pairwise coprime, defining the Diophantine system x = x_i (mod m_i);
Output: x such that x = x_i (mod m_i) for 1<=i<=k.

"
Class {
	#name : #CRT,
	#superclass : #Object,
	#instVars : [
		'moduli',
		'C'
	],
	#category : #'Mathematics-Algorithms'
}

{ #category : #'instance creation' }
CRT class >> mod: anArray [
	^ self new moduli: anArray
]

{ #category : #'instance creation' }
CRT class >> solve: aCollection [
	| x m |
	x := aCollection first.
	m := x modulus.
	aCollection allButFirstDo: [:each| | xi mi bezout |
		xi := each.
		mi := xi modulus.
		bezout := (ExtendedEuclid on: {m. mi}) bezout.
		x := bezout first * m * xi representative + (bezout second * mi * x representative).
		m := m*mi.
		x := x % m].
	^ x
]

{ #category : #initialization }
CRT >> moduli: anArray [
	| one k mj p euclid d |
	moduli := anArray.
	"Precomputations:"
	one := moduli first one.
	k := moduli size.
	C := Array new: k.
	C at: 1 put: one.
	2 to: k do: [:j|
		mj := moduli at: j.
		p := one. 1 to: j-1 do: [:i| p := p * (moduli at: i) \\ mj].
		euclid := ExtendedEuclid on: {p. mj}.
		d := euclid gcd.
		d ~= one ifTrue: [^ self error: 'the moduli are not coprime'].
		euclid verify ifFalse: [self error: 'failed'].
		C at: j put: euclid bezout first]
]

{ #category : #computing }
CRT >> solve: remainders [
	| k mj y yj x |
	k := moduli size.
	y := Array new: k.
	y at: 1 put: (remainders at: 1) \\ (moduli at: 1).
	2 to: k do: [:j|
		mj := moduli at: j.
		yj := y at: j-1.
		j-2 to: 1 by: -1 do: [:i| yj := yj * (moduli at: i) + (y at: i) \\ mj].
		yj := ((remainders at: j) - yj) * (C at: j) \\ mj.
		y at: j put: yj].
	x := y at: k.
	k-1 to: 1 by: -1 do: [:i| x := x * (moduli at: i) + (y at: i)].
	"it would be more correct to return the residue class mod m1*m2*..*mk"
	^ x
]
