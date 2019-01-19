Class {
	#name : #CyclicCode,
	#superclass : #PolynomialCode,
	#category : #'Mathematics-Codes'
}

{ #category : #'as yet unclassified' }
CyclicCode >> checkPolynomial [
	| x one |
	x := generator parent x.
	one := generator parent one.
	^ 'x ^ self length - one / generator'
]

{ #category : #'as yet unclassified' }
CyclicCode >> dual [
	^ self class new: self length generator: self generator reversed
]

{ #category : #'as yet unclassified' }
CyclicCode >> includes: aCodeword [
	| x |
	x := generator parent x.
	^ 'self checkPolynomial * aCodeword \\ (x ^ self length - x one) :: isZero'
]

{ #category : #'as yet unclassified' }
CyclicCode >> isIrreducible [
	^ generator isIrreducible
]
