"
This is the long division algorithm for univariate polynomials over a field.

Input: dividend and divisor polynomials f,g in K[x], where K is a field;
Output: quotient and remainder polynomials q,r in K[x] such that f = q*g + r, deg(r) < deg(g).

The algorithm performs O(n^2) arithmetic operations for dense polynomials of degree n.
"
Class {
	#name : #PolynomialDivision,
	#superclass : #Object,
	#instVars : [
		'dividend',
		'divisor',
		'quotient',
		'remainder'
	],
	#category : #'Mathematics-Polynomials-Algorithms'
}

{ #category : #'instance creation' }
PolynomialDivision class >> divide: aPolynomial by: anotherPolynomial [
	"Answer a division algorithm to divide aPolynomial by anotherPolynomial."

	^ self new divide: aPolynomial by: anotherPolynomial
]

{ #category : #private }
PolynomialDivision >> divide [
	"Compute the quotient and the remainder polynomials."
	| quo rem lc n m term |
	divisor isZero ifTrue: [^ (ZeroDivide dividend: dividend) signal].
	(m := divisor degree) = 0
		ifTrue: [quotient := dividend * divisor leadingCoefficient reciprocal.
					remainder := dividend zero.
					^ self].
	dividend degree < m
		ifTrue: [quotient := dividend zero. remainder := dividend.
					^ self].
"	indeterminate := divisor leadingIndeterminate."
	quo := dividend parent zero.
	rem := dividend copy.
	lc := divisor leadingCoefficient.
	[(n := rem degree) >= m]
		whileTrue:
			[term := dividend parent coefficient: rem leadingCoefficient / lc degree: n-m.
			rem := rem + (divisor * term negated).
			"or optimized as:
			divisor monomialsAndCoefficientsDo: [:key :value|
				rem coefficientAt: key * monomial add: value * minusC]."
			quo := quo + term.
			" or optimized as:
			quo coefficientAt: monomial add: c"].
	quotient := quo. remainder := rem
]

{ #category : #initialization }
PolynomialDivision >> divide: aPolynomial by: anotherPolynomial [
	dividend := aPolynomial.
	divisor := anotherPolynomial
]

{ #category : #private }
PolynomialDivision >> divideNoQuotient [
	"Compute the remainder polynomial."
	| rem lc n m term |
	divisor isZero ifTrue: [^ (ZeroDivide dividend: dividend) signal].
	(m := divisor degree) = 0
		ifTrue: [quotient := dividend * divisor leadingCoefficient reciprocal.
					remainder := dividend zero.
					^ self].
	dividend degree < m
		ifTrue: [quotient := dividend zero. remainder := dividend.
					^ self].
"	indeterminate := divisor leadingIndeterminate."
	rem := dividend copy.
	lc := divisor leadingCoefficient.
	[(n := rem degree) >= m]
		whileTrue:
			[term := dividend parent coefficient: rem leadingCoefficient / lc degree: n-m.
			rem := rem + (divisor * term negated).
			"or optimized as:
			divisor monomialsAndCoefficientsDo: [:key :value|
				rem coefficientAt: key * monomial add: value * minusC]."].
	remainder := rem
]

{ #category : #accessing }
PolynomialDivision >> dividend [
	^ dividend
]

{ #category : #accessing }
PolynomialDivision >> divisor [
	^ divisor
]

{ #category : #accessing }
PolynomialDivision >> exactQuotient [
	self remainder isZero ifFalse: [self error: 'not an exact division'].
	^ self quotient
]

{ #category : #printing }
PolynomialDivision >> printOn: aStream [
	"Print a representation of the receiver on the stream aStream."

	aStream
		print: self dividend;
		nextPutAll: ' = (';
		print: self quotient;
		nextPutAll: ')(';
		print: self divisor;
		nextPutAll: ') + ';
		print: self remainder
]

{ #category : #accessing }
PolynomialDivision >> quotient [
	quotient isNil ifTrue: [self divide].
	^ quotient
]

{ #category : #accessing }
PolynomialDivision >> remainder [
	remainder isNil ifTrue: [self divideNoQuotient].
	^ remainder
]
