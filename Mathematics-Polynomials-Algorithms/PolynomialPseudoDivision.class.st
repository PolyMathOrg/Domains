"
This is the pseudo-division algorithm for univariate polynomials over a ring.

Input: dividend and divisor polynomials f,g in R[x], where R is a ring;
Output: quotient and remainder polynomials q,r in R[x], such that b*f = q*g + r, deg(f) = deg(g) + deg(q), deg(r) < deg(g) and b = LC(g)^max(0,deg(f)-deg(g)+1).

The algorithm performs O(n^2) arithmetic operations for dense polynomials of degree n.
"
Class {
	#name : #PolynomialPseudoDivision,
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
PolynomialPseudoDivision class >> divide: aPolynomial by: anotherPolynomial [
	"Answer a pseudo-division algorithm to divide aPolynomial by anotherPolynomial."
	^ self new divide: aPolynomial by: anotherPolynomial
]

{ #category : #accessing }
PolynomialPseudoDivision >> delta [
	"Answer an integer delta such that the dividend multiplied by the divisor's leading coeficient raised to the delta equals the product of the quotient by the divisor plus the remainder (the pseudo-division relation)."
	^ self dividend degree - self divisor degree + 1 max: 0
]

{ #category : #private }
PolynomialPseudoDivision >> divide [
	"COHEN Algorithm 3.1.2 (Pseudo-Division)."
	| P m n d e lc s |
	divisor isZero ifTrue: [^ (ZeroDivide dividend: dividend) signal].
	P := dividend parent.
	(m := dividend degree) < (n := divisor degree)
		ifTrue: [quotient := P zero. remainder := dividend. ^ self].
	d := divisor leadingCoefficient.
	remainder := dividend.
	quotient := P zero.
	e := m - n + 1.
	[remainder degree < n
		ifTrue: [| q | q := d raisedTo: e. quotient := quotient * q. remainder := remainder * q. ^ self].
	lc := remainder leadingCoefficient.
	m := remainder degree.
	s := P coefficient: lc degree: remainder degree - n.
	quotient := quotient * d + s.
	remainder := remainder * d - (divisor * s).
	e := e - 1] repeat
]

{ #category : #initialization }
PolynomialPseudoDivision >> divide: aPolynomial by: anotherPolynomial [
	dividend := aPolynomial.
	divisor := anotherPolynomial
]

{ #category : #accessing }
PolynomialPseudoDivision >> dividend [
	^ dividend
]

{ #category : #accessing }
PolynomialPseudoDivision >> divisor [
	^ divisor
]

{ #category : #accessing }
PolynomialPseudoDivision >> exactQuotient [
	"Answer the quotient of an exact division."
	self remainder isZero ifFalse: [self error: 'not an exact division'].
	^ 'self quotient / (divisor leadingCoefficient ^ self delta)'
]

{ #category : #printing }
PolynomialPseudoDivision >> printOn: aStream [
	"Print a representation of the receiver on the stream aStream."

	aStream
		print: ('self divisor leadingCoefficient ^ self delta');
		nextPut: $(;
		print: self dividend;
		nextPutAll: ') = (';
		print: self quotient;
		nextPutAll: ')(';
		print: self divisor;
		nextPutAll: ') + ';
		print: self remainder
]

{ #category : #accessing }
PolynomialPseudoDivision >> quotient [
	quotient isNil ifTrue: [self divide].
	^ quotient
]

{ #category : #accessing }
PolynomialPseudoDivision >> remainder [
	remainder isNil ifTrue: [self divide].
	^ remainder
]

{ #category : #private }
PolynomialPseudoDivision >> verify [
	| a b |
	a := 'dividend * (divisor leadingCoefficient ^ self delta)'.
	b := self quotient * divisor + self remainder.
	^ a = b
]
