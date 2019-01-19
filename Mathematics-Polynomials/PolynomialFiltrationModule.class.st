"
Submodules of univariate polynomials of degree <= n for a fixed n, in the ring of univariate polynomials R[x]. They define a filtration (see PolynomialRing>>filtrationAt:).
"
Class {
	#name : #PolynomialFiltrationModule,
	#superclass : #FreeModule,
	#instVars : [
		'polynomials',
		'degree'
	],
	#category : #'Mathematics-Polynomials'
}

{ #category : #basis }
PolynomialFiltrationModule >> coordinatesOf: aPolynomial [
	| coefficients |
	coefficients := aPolynomial coefficients.
	^ coefficients, ((1 to: self dimension - coefficients size) collect: [:each| self scalars zero])
]

{ #category : #accessing }
PolynomialFiltrationModule >> degree [
	^ degree
]

{ #category : #'accessing-private' }
PolynomialFiltrationModule >> degree: anInteger [
	degree := anInteger
]

{ #category : #morphisms }
PolynomialFiltrationModule >> differential [
	^ self to: self evaluating: [:f| f derivative]
]

{ #category : #basis }
PolynomialFiltrationModule >> e: anInteger [
	^ polynomials xTo: anInteger - 1
]

{ #category : #basis }
PolynomialFiltrationModule >> elementAt: aTuple [
	^ polynomials coefficients: aTuple
]

{ #category : #testing }
PolynomialFiltrationModule >> includes: anObject [
	^ (polynomials includes: anObject) and: [anObject degree <= degree]
]

{ #category : #morphisms }
PolynomialFiltrationModule >> integral: a to: b [
	^ self dual evaluating: [:f| f integral: a to: b]
]

{ #category : #'accessing-private' }
PolynomialFiltrationModule >> polynomials: aPolynomials [
	polynomials := aPolynomials
]

{ #category : #printing }
PolynomialFiltrationModule >> printOn: aStream [
	aStream print: polynomials; nextPutAll: ('<', (degree+1) printString) sub
]

{ #category : #basis }
PolynomialFiltrationModule >> rank [
	^ degree + 1
]

{ #category : #accessing }
PolynomialFiltrationModule >> scalars [
	^ polynomials scalars
]
