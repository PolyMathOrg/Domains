"
The field of fractions of a polynomial ring with coefficients over a field.
"
Class {
	#name : #RationalFunctionField,
	#superclass : #FractionRing,
	#category : #'Mathematics-Polynomials'
}

{ #category : #examples }
RationalFunctionField class >> example1 [
	"The field of rational functions in two indeterminates over the rationals:"
	^ (QQ polynomialsIn: #(x y)) fractions
]

{ #category : #examples }
RationalFunctionField class >> example2 [
	"x / y in Q(x,y):"
	| F |
	F := (QQ polynomialsIn: #(x y)) fractions.
	^ (F x: 1) / (F x: 2)
]

{ #category : #'instance creation' }
RationalFunctionField class >> new: anInteger over: aRing [
	^ self over: (aRing polynomialsIn: anInteger)
]

{ #category : #'instance creation' }
RationalFunctionField class >> on: aPolynomialRing [
	| R |
	R := (aPolynomialRing isKindOf: PolynomialRing) ifTrue: [aPolynomialRing] ifFalse: [aPolynomialRing polynomials].
	R := R ordering isLocal
		ifTrue: [aPolynomialRing]
		ifFalse: [aPolynomialRing orderedBy: #llex].
	^ super on: R
]

{ #category : #elements }
RationalFunctionField >> ! anObject [
	(anObject isKindOf: Polynomial)
		ifTrue: [^ self integers ! anObject].
	(anObject isKindOf: RationalFunction)
		ifTrue: [^ self integers ! anObject numerator / (self integers ! anObject denominator)].
	^ super ! anObject
]

{ #category : #morphisms }
RationalFunctionField >> embed: aPolynomial [
	^ RationalFunction numerator: self integers ! aPolynomial denominator: self integers one
]

{ #category : #operations }
RationalFunctionField >> extension: aPolynomial [
	"Answer the algebraic function field extension of the receiver defined by the given irreducible polynomial."
	aPolynomial scalars = self ifFalse: [DomainError signal: 'polynomial coefficients not from this field'].
	aPolynomial parent isUnivariate ifFalse: [DomainError signal: 'not univariate poylnomial'].
	^ FunctionField polynomial: aPolynomial
]

{ #category : #accessing }
RationalFunctionField >> indeterminates [
	^ self integers indeterminates
]

{ #category : #testing }
RationalFunctionField >> isUnit: aRationalFunction [
	"Answer true if the argument is invertible."
	^ aRationalFunction isZero not
]

{ #category : #testing }
RationalFunctionField >> isUnivariate [
	^ self integers isUnivariate
]

{ #category : #printing }
RationalFunctionField >> printOn: aStream [
	aStream print: self scalars.
	aStream nextPut: $(.
	self integers printIndeterminatesOn: aStream.
	aStream nextPut: $)
]

{ #category : #accessing }
RationalFunctionField >> rank [
	^ self integers rank
]

{ #category : #accessing }
RationalFunctionField >> scalars [
	^ self integers scalars
]

{ #category : #accessing }
RationalFunctionField >> size [
	^ Aleph new * self scalars size
]

{ #category : #elements }
RationalFunctionField >> x [
	^ self x: 1
]

{ #category : #elements }
RationalFunctionField >> x: anIndeterminate [
	^ self embed: (self integers x: anIndeterminate)
]

{ #category : #elements }
RationalFunctionField >> y [
	^ self x: 2
]

{ #category : #elements }
RationalFunctionField >> z [
	^ self x: 3
]
