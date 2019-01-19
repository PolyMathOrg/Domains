"
Rational functions are fractions of polynomials. They are elements of the field of fractions of a polynomial ring over a field (see RationalFunctionField).
"
Class {
	#name : #RationalFunction,
	#superclass : #FormalFraction,
	#category : #'Mathematics-Polynomials'
}

{ #category : #'instance creation' }
RationalFunction class >> numerator: aPolynomial denominator: anotherPolynomial [
	| numerator denominator gcd c |
	(numerator := aPolynomial) isZero ifTrue: [^ numerator].
	denominator := anotherPolynomial.
	gcd := numerator gcd: denominator.
	numerator := numerator /// gcd.
	denominator := denominator /// gcd.
	"make the denominator monic:"
	c := denominator leadingCoefficient reciprocal.
	numerator := numerator * c.
	denominator := denominator * c.
	denominator = denominator one ifTrue: [^ numerator].
	^ self reducedNumerator: numerator denominator: denominator
]

{ #category : #converting }
RationalFunction >> adaptToNumber: rcvr andSend: selector [
	"If I am involved in arithmetic with an Number, convert it to a RationalFunction."
	^ (self one * rcvr) perform: selector with: self
]

{ #category : #'roots and poles' }
RationalFunction >> allPoles [
	^ denominator allRoots
]

{ #category : #'roots and poles' }
RationalFunction >> allPolesIn: aRing [
	^ denominator allRootsIn: aRing
]

{ #category : #'roots and poles' }
RationalFunction >> allRoots [
	^ numerator allRoots
]

{ #category : #'roots and poles' }
RationalFunction >> allRootsIn: aRing [
	"Answer the roots (counted with multiplicity) in the given domain."
	^ numerator allRootsIn: aRing
]

{ #category : #operations }
RationalFunction >> degree [
	^ numerator degree - denominator degree
]

{ #category : #operations }
RationalFunction >> derivative [
	"Answer the derivative of the receiver."

	| num gcd |
	num := denominator * numerator derivative - (numerator * denominator derivative).
	gcd := denominator gcd: num.
	^ self class numerator: num // gcd denominator: (denominator // gcd) squared * gcd
]

{ #category : #operations }
RationalFunction >> homogenized [
	"Answer the homogenization of the receiver introducing a new indeterminate."
	| R S |
	R := numerator parent.
	S := R scalars polynomialsIn: R rank + 1.
	^ self class numerator: (S ! numerator homogenizedIn: S rank) denominator: (S ! denominator homogenizedIn: S rank)
]

{ #category : #operations }
RationalFunction >> homogenizedIn: anIndeterminate [
	"Answer the homogenization of the receiver in the given indeterminate."
	^ self class numerator: (numerator homogenizedIn: anIndeterminate) denominator: (denominator homogenizedIn: anIndeterminate)
]

{ #category : #accessing }
RationalFunction >> indeterminates [
	^ Set new addAll: numerator indeterminates; addAll: denominator indeterminates; yourself
]

{ #category : #testing }
RationalFunction >> isAffineLinear [
	^ denominator isAffineLinear and: [denominator isConstant]
]

{ #category : #testing }
RationalFunction >> isHomogeneous [
	^ self numerator isHomogeneous and: [self denominator isHomogeneous]
]

{ #category : #testing }
RationalFunction >> isLinear [
	^ denominator isLinear and: [denominator isConstant]
]

{ #category : #'roots and poles' }
RationalFunction >> orderAt: aNumber [
	^ (numerator multiplicityAt: aNumber) - (denominator multiplicityAt: aNumber)
]

{ #category : #'roots and poles' }
RationalFunction >> poles [
	^ denominator roots
]

{ #category : #'roots and poles' }
RationalFunction >> polesIn: aRing [
	^ denominator rootsIn: aRing
]

{ #category : #printing }
RationalFunction >> printOn: aStream [
	denominator = denominator one ifTrue: [aStream print: numerator. ^ self].
	numerator terms size > 1
		ifTrue: [aStream nextPut: $(; print: numerator; nextPut: $)]
		ifFalse: [aStream print: numerator].
	aStream nextPutAll: ' / '.
	denominator terms size > 1
		ifTrue: [aStream nextPut: $(; print: denominator; nextPut: $)]
		ifFalse: [aStream print: denominator]
]

{ #category : #arithmetic }
RationalFunction >> reciprocal [ 
	"Answer the multiplicative inverse of the receiver."

	| mult |
	mult := numerator leadingCoefficient reciprocal.
"	numerator isConstant ifTrue: [^ denominator * mult]."
	^ self class reducedNumerator: denominator * mult denominator: numerator * mult
]

{ #category : #private }
RationalFunction >> reduce [
	"Reduce the receiver dividing the numerator and the denominator
	by their GCD and making the denominator monic."
	| gcd mult num den |
	(num := numerator) isZero ifTrue: [denominator := num one. ^ self].
	den := denominator.
	gcd := num gcd: den.
	num := num /// gcd.
	den := den /// gcd.
	mult := den leadingCoefficient reciprocal.
	numerator := num * mult.
	denominator := den * mult
]

{ #category : #'roots and poles' }
RationalFunction >> roots [
	^ numerator roots
]

{ #category : #'roots and poles' }
RationalFunction >> rootsIn: aRing [
	^ numerator rootsIn: aRing
]

{ #category : #accessing }
RationalFunction >> scalars [
	^ numerator scalars
]

{ #category : #'as yet unclassified' }
RationalFunction >> setNumerator: f denominator: g [
"	g parent isLocal ifFalse: [self halt]."
	super setNumerator: f denominator: g
]

{ #category : #operations }
RationalFunction >> value: anObject [
	^ (numerator value: anObject) / (denominator value: anObject)
]

{ #category : #operations }
RationalFunction >> valueWithArguments: anArray [
	^ self value: anArray
]
