"
Polynomials in a finite set of non-commuting indeterminates. They are elements of a free associative algebra (FreeAlgebra).

A free polynomial is a formal linear combination of Words, that in turn are formal (noncommutative) products of arbitrary objects (indeterminates).
"
Class {
	#name : #FreePolynomial,
	#superclass : #FormalSum,
	#category : #'Mathematics-Etc-Algebras'
}

{ #category : #arithmetic }
FreePolynomial >> * anObject [
	((self scalars includes: anObject) or: [anObject isInteger])
		ifTrue: [^ super * anObject].
	(self parent includes: anObject)
		ifTrue: [^ self convolution: anObject].
	(self parent words includes: anObject)
		ifTrue: [^ self multipliedByMonomial: anObject].
	^ DomainError signal
]

{ #category : #accessing }
FreePolynomial >> degree [
	"Answer the total degree of the receiver."
	self isZero ifTrue: [^ Infinity negative].
	^ self monomials max: [:each| each length]
]

{ #category : #testing }
FreePolynomial >> isStandard [
	"Answer true if the receiver is a standard polynomial, i.e. all its monomials are standard words."
	self monomialsDo: [:each| each isStandard ifFalse: [^ false]].
	^ true
]

{ #category : #accessing }
FreePolynomial >> leadingCoefficient [
	^ self at: self leadingMonomial
]

{ #category : #accessing }
FreePolynomial >> leadingMonomial [
	^ self monomials asSortedCollection first
]

{ #category : #accessing }
FreePolynomial >> monomials [
	^ Iterator on: self performing: #monomialsDo:
]

{ #category : #accessing }
FreePolynomial >> monomialsDo: aBlock [
	self keysDo: aBlock
]

{ #category : #arithmetic }
FreePolynomial >> multipliedByMonomial: aWord [
	| newCoefficients |
	newCoefficients := Dictionary new: self size.
	self associationsDo: [:each| newCoefficients at: each key * aWord put: each value].
	^ self parent coefficients: newCoefficients
]

{ #category : #accessing }
FreePolynomial >> one [
	^ self parent one
]

{ #category : #arithmetic }
FreePolynomial >> raisedTo: anInteger [
	"Answer the receiver raised to the power anInteger."

	(anInteger isInteger and: [ anInteger >= 0 ])
		ifFalse: [ ^ DomainError signal: 'undefinted' ].
	anInteger = 0
		ifTrue: [ ^ self one ].
	anInteger = 1
		ifTrue: [ ^ self ].
	^ (self squared raisedTo: anInteger // 2)
		* (self raisedTo: anInteger \\ 2)
]

{ #category : #arithmetic }
FreePolynomial >> squared [
	^ self * self
]
