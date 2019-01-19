"
This is the multivariate polynomial division algorithm for polynomials over a field.

Input: dividend f and divisors f1,..,fs in K[x1..xd] with a monomial ordering;
Output: quotients q1,..,qs and remander r in K[x1..xd] such that f = q1*f1 + ... + qn*fn + r, such that:
1. LM(qifi) <= LM(f);
2. None of the monomials in r is divisible by any LM(fi).

The algorithm performs O(n^d m^d) operations in the coefficients field K, where n is the total degree of f and m is the maximal total degree of f1..fs.
"
Class {
	#name : #MultivariatePolynomialDivision,
	#superclass : #Object,
	#instVars : [
		'dividend',
		'divisors',
		'quotients',
		'remainder'
	],
	#category : #'Mathematics-Polynomials-Algorithms'
}

{ #category : #'instance creation' }
MultivariatePolynomialDivision class >> divide: aPolynomial by: anArrayOfPolynomials [
	^ self new divide: aPolynomial by: anArrayOfPolynomials
]

{ #category : #private }
MultivariatePolynomialDivision >> divide [
	"Perform the division algorithm computing quotients and remainder."
	| p s zero fi q headp headfi t i |
	zero := dividend zero.
	quotients := (1 to: divisors size) collect: [:each| zero].
	divisors isEmpty ifTrue: [remainder := dividend. ^ self].
	remainder := zero.
	s := divisors size.
	p := dividend.
	[p isZero] whileFalse:
		[headp := p leadingMonomial.
		t := p leadingTerm.
		i := 1.
		[headfi := (fi := divisors at: i) leadingMonomial.
		headfi | headp or: [(i := i + 1) > s]] whileFalse.
		i <= s "i.e. found fi such that headfi | headp"
			ifTrue:
				[q := t / headfi * fi leadingCoefficient reciprocal.
				quotients at: i put: (quotients at: i) + q.
				p := p - (fi * q)]
			ifFalse:
				[remainder := remainder + t.
				p := p - t]]
]

{ #category : #private }
MultivariatePolynomialDivision >> divide2 [
	"Perform the division algorithm computing quotients and remainder."
	| p s zero fi q headp headfi t heads i inverses |
	zero := dividend zero.
	quotients := (1 to: divisors size) collect: [:each| zero].
	divisors isEmpty ifTrue: [remainder := dividend. ^ self].
	remainder := zero.
	s := divisors size.
	p := dividend.
	heads := Array new: divisors size.
	inverses := Array new: divisors size.
	[p isZero] whileFalse:
		[headp := p leadingMonomial.
		t := p termAt: headp.
		i := 1.
		[headfi := (heads at: i) ifNil: [heads at: i put: (fi := divisors at: i) leadingMonomial].
		(headfi | headp) or: [(i := i + 1) > s]] whileFalse.
		i <= s "i.e. found fi such that headfi | headp"
			ifTrue:
				[fi := divisors at: i.
				q := t / headfi * ((inverses at: i) ifNil: [inverses at: i put: (fi at: headfi) reciprocal]).
				quotients at: i put: (quotients at: i) + q.
				p := p - (fi * q)]
			ifFalse:
				[remainder := remainder + t.
				p := p - t]]
]

{ #category : #private }
MultivariatePolynomialDivision >> divide3 [
	"Perform the division algorithm computing quotients and remainder."
	| p s zero fi q headp headfi t heads i |
	zero := dividend zero.
	quotients := (1 to: divisors size) collect: [:each| zero].
	divisors isEmpty ifTrue: [remainder := dividend. ^ self].
	remainder := zero.
	s := divisors size.
	p := dividend.
	heads := Array new: divisors size.
	[p isZero] whileFalse:
		[headp := p leadingMonomial.
		t := p termAt: headp.
		i := 1.
		[headfi := (heads at: i) ifNil: [heads at: i put: (fi := divisors at: i) leadingMonomial].
		(headfi | headp) or: [(i := i + 1) > s]] whileFalse.
		i <= s "i.e. found fi such that headfi | headp"
			ifTrue:
				[fi := divisors at: i.
				q := t / headfi * (fi at: headfi) reciprocal.
				quotients at: i put: (quotients at: i) + q.
				p := p - (fi * q)]
			ifFalse:
				[remainder := remainder + t.
				p := p - t]]
]

{ #category : #initialization }
MultivariatePolynomialDivision >> divide: aPolynomial by: anArrayOfPolynomials [
	dividend := aPolynomial.
	divisors := anArrayOfPolynomials
]

{ #category : #accessing }
MultivariatePolynomialDivision >> dividend [
	^ dividend
]

{ #category : #accessing }
MultivariatePolynomialDivision >> divisors [
	^ divisors
]

{ #category : #accessing }
MultivariatePolynomialDivision >> exactQuotient [
	self remainder isZero ifFalse: [self error: 'not an exact division'].
	^ self quotient
]

{ #category : #printing }
MultivariatePolynomialDivision >> printOn: aStream [
	"Print a representation of the receiver on the stream aStream."

	aStream print: self dividend; nextPutAll: ' = '.
	(1 to: self divisors size) do: [ :each |
		aStream
			nextPut: $(; print: (self quotients at: each); nextPut: $);
			nextPut: $(; print: (self divisors at: each); nextPut: $);
			nextPutAll: ' + '].
	aStream print: self remainder
]

{ #category : #accessing }
MultivariatePolynomialDivision >> quotient [
	self quotients size = 1 ifFalse: [self error: 'not just one quotient'].
	^ self quotients first
]

{ #category : #accessing }
MultivariatePolynomialDivision >> quotients [
	quotients isNil ifTrue: [self divide].
	^ quotients
]

{ #category : #accessing }
MultivariatePolynomialDivision >> remainder [
	remainder isNil ifTrue: [self divide].
	^ remainder
]

{ #category : #private }
MultivariatePolynomialDivision >> verify [
	| total |
	total := self remainder.
	self divisors with: self quotients do: [:f :q| total := total + (f*q)].
	total = self dividend ifFalse: [^ false].

	self divisors with: self quotients do: [:f :q|
		(q isZero or: [(f*q) leadingMonomial <= self dividend leadingMonomial])
			ifFalse: [^ false]].

	self remainder monomials do: [:each| (self divisors noneSatisfy: [:f| f leadingMonomial | each]) ifFalse: [^ false]].
	^ true
]
