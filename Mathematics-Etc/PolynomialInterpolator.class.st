Class {
	#name : #PolynomialInterpolator,
	#superclass : #Object,
	#instVars : [
		'polynomial',
		'corrector'
	],
	#category : #'Mathematics-Etc'
}

{ #category : #'instance creation' }
PolynomialInterpolator class >> new [
	^ super new initialize
]

{ #category : #accessing }
PolynomialInterpolator >> corrector [
	"Answer the correction polynoial."

	^ corrector
]

{ #category : #'accessing-private' }
PolynomialInterpolator >> corrector: aPolynomial [
	corrector := aPolynomial
]

{ #category : #initialization }
PolynomialInterpolator >> initialize [
	self flag: #fix.
	self polynomial: Polynomial null.
	self corrector: Polynomial identity
]

{ #category : #operations }
PolynomialInterpolator >> map: aNumber to: anotherNumber [
	"Change the interpolation polynomial to map aNumber to anotherNumber."

	| f q m |
	f := self polynomial.
	q := self corrector.
	m := anotherNumber - (f value: aNumber) / (q value: aNumber).
	f := q * m + f.
	q := q * aNumber negated + (q shift: 1).
	self polynomial: f.
	self corrector: q.
	^ anotherNumber
]

{ #category : #accessing }
PolynomialInterpolator >> polynomial [
	"Answer the interpolation polynoial."

	^ polynomial
]

{ #category : #'accessing-private' }
PolynomialInterpolator >> polynomial: aPolynomial [
	polynomial := aPolynomial
]
