"
Submodules of homogeneous polynomials of a given fixed degree, in a multivariate polynomial ring R[x1,...,xn]. They define a grading (see PolynomialRing>>gradingAt:).
"
Class {
	#name : #PolynomialGradingModule,
	#superclass : #FreeModule,
	#instVars : [
		'polynomials',
		'degree'
	],
	#category : #'Mathematics-Polynomials'
}

{ #category : #basis }
PolynomialGradingModule >> coordinatesOf: aPolynomial [
	^ self scalars tuple: (self monomialBasis collect: [:each| aPolynomial coefficientAt: each])
]

{ #category : #'as yet unclassified' }
PolynomialGradingModule >> degree: anInteger [
	degree := anInteger
]

{ #category : #basis }
PolynomialGradingModule >> e: anInteger [
	^ polynomials monomial: (self monomialBasis at: anInteger)
]

{ #category : #testing }
PolynomialGradingModule >> includes: anObject [
	^ (polynomials includes: anObject) and: [anObject isHomogeneous and: [anObject degree = degree]]
]

{ #category : #basis }
PolynomialGradingModule >> monomialBasis [
	^ self propertyAt: #monomialBasis ifAbsentPut: [polynomials monomials allMonomialsOfDegree: degree]
]

{ #category : #accessing }
PolynomialGradingModule >> ordering [
	^ polynomials ordering
]

{ #category : #'as yet unclassified' }
PolynomialGradingModule >> polynomials: aPolynomialRing [
	polynomials := aPolynomialRing
]

{ #category : #printing }
PolynomialGradingModule >> printOn: aStream [
	aStream print: polynomials; nextPutAll: degree printString sub
]

{ #category : #basis }
PolynomialGradingModule >> rank [
	| n |
	n := polynomials rank.
	^ degree + n - 1 choose: degree
]

{ #category : #accessing }
PolynomialGradingModule >> scalars [
	^ polynomials scalars
]
