"
This is the extended Euclidean algorithm.

Input: an array of two elements in an Euclidean domain {a. b}
Output: the GCD of a with b, and a pair of Bezout coefficients {u. v} such that a*u + b*v = (a,b).

In the case of integers, if |a|<=|b| the output |u| and |v| are unique and satisfy:
	-|a| / d < v*sign(b) <= 0.
	1 <= u*sign(a) <= |b| / d
where d = gcd(a,b).

For integers, the algorithm takes time O(ln^3 N) where |a|,|b| <= N. For polynomials of degree n, it is O(n^3).
"
Class {
	#name : #ExtendedEuclid,
	#superclass : #Object,
	#instVars : [
		'elements',
		'gcd',
		'bezout'
	],
	#category : #'Mathematics-Algorithms'
}

{ #category : #'instance creation' }
ExtendedEuclid class >> on: anArray [
	^ self new elements: anArray
]

{ #category : #accessing }
ExtendedEuclid >> bezout [
	"Answer a tuple of Bezout coefficients for the receiver."
	bezout isNil ifTrue: [self run].
	^ bezout
]

{ #category : #'accessing-private' }
ExtendedEuclid >> elements: anArray [
	elements := anArray
]

{ #category : #accessing }
ExtendedEuclid >> gcd [
	gcd isNil ifTrue: [self run].
	^ gcd
]

{ #category : #printing }
ExtendedEuclid >> printOn: aStream [
	(1 to: elements size)
		do: [:i| aStream print: (elements at: i); nextPut: $*; print: (self bezout at: i)]
		separatedBy: [aStream nextPutAll: ' + '].
	aStream nextPutAll: ' = '; print: self gcd.
	self verify ifFalse: [aStream nextPutAll: ' (broken)'].
	self verifyMinimal ifFalse: [aStream nextPutAll: ' (not minimal)']
]

{ #category : #private }
ExtendedEuclid >> run [
	| a b zero one s1 t1 s t r1 r |
	self assert: elements size = 2.
	a := elements first. b := elements second.
	zero := a zero. one := a one.
	s1 := zero. s := one.
	t1 := one. t := zero.
	a isInteger
		ifTrue: [r1 := a abs. r := b abs]
		ifFalse: [r1 := a. r := b].
	[r1 isZero]
		whileFalse:
			[ | q temp |
			q := r // r1.
			temp := r1. r1 := r - (q * r1). r := temp.
			temp := s1. s1 := s - (q * s1). s := temp.
			temp := t1. t1 := t - (q * t1). t := temp].
	gcd := r.
	a isInteger ifTrue: [s := s * b sign. t := t * a sign].
	(gcd isKindOf: Polynomial) "make the gcd monic, otherwise it's not unique"
		ifTrue:
			[| lc |
			lc := gcd leadingCoefficient.
			s := s / lc.
			t := t / lc.
			gcd := gcd / gcd leadingCoefficient].
	bezout := {t. s}
]

{ #category : #private }
ExtendedEuclid >> verify [
	^ (elements * self bezout) sum = self gcd
]

{ #category : #private }
ExtendedEuclid >> verify2 [
	| a b d u v |
	a := elements at: 1.
	b := elements at: 2.
	u := self bezout at: 1.
	v := self bezout at: 2.
	d := self gcd.
	(a abs negated / d < (v * b sign) and: [v * b sign <= 0])
		ifFalse: [^ false].
	b = 0 ifTrue: [^ true].
	(1 <= (u * a sign) and: [u * a sign <= (b abs / d)])
		ifFalse: [^ false].
	^ true
]

{ #category : #private }
ExtendedEuclid >> verifyMinimal [
	| a b d u v |
	(elements allSatisfy: [:each| each isInteger]) ifFalse: [^ true].
	a := elements first.
	b := elements second.
	d := self gcd.
	u := self bezout first.
	v := self bezout last.
	a abs / d negated < (v * b sign) ifFalse: [^ false].
	v * b sign <= 0 ifFalse: [^ false].
	1 <= (u * a sign) ifFalse: [^ false].
	u * a sign <= (b abs / d) ifFalse: [^ false].
	^ true
]
