"
Formal Dirichlet series, i.e. formal series in an indeterminate x of the form: sum a(n) * n^{-x} for n >= 1.

Examples:
	DirichletSeries coefficients: Sequence moebius.
	Sequence liouville dirichletSeries.

Structure:
 coefficients	Sequence -- the coefficients of the Dirichlet series

"
Class {
	#name : #DirichletSeries,
	#superclass : #Object,
	#instVars : [
		'coefficients'
	],
	#category : #'Mathematics-Sequences'
}

{ #category : #'instance creation' }
DirichletSeries class >> coefficients: aSequence [
	^ self new coefficients: aSequence
]

{ #category : #examples }
DirichletSeries class >> zeta [
	^ self coefficients: (CFiniteSequence constant: 1)
]

{ #category : #arithmetic }
DirichletSeries >> * anObject [
	(self scalars includes: anObject)
		ifTrue: [^ self class coefficients: coefficients * anObject].
	(anObject isKindOf: self class)
		ifTrue: [^ self class coefficients: (coefficients dirichlet: anObject coefficients)].
	^ DomainError signal
]

{ #category : #arithmetic }
DirichletSeries >> + anObject [
	^ self class coefficients: coefficients + anObject coefficients
]

{ #category : #arithmetic }
DirichletSeries >> - anObject [
	^ self + anObject negated
]

{ #category : #arithmetic }
DirichletSeries >> / anObject [
	^ self * anObject reciprocal
]

{ #category : #comparing }
DirichletSeries >> = anObject [
	^ (anObject isKindOf: DirichletSeries) and: [self coefficients = anObject coefficients]
]

{ #category : #accessing }
DirichletSeries >> coefficients [
	^ coefficients
]

{ #category : #accessing }
DirichletSeries >> coefficients: aSequence [
	coefficients := aSequence
]

{ #category : #comparing }
DirichletSeries >> hash [
	^ coefficients hash
]

{ #category : #accessing }
DirichletSeries >> indeterminate [
	^ 1
]

{ #category : #arithmetic }
DirichletSeries >> negated [
	^ self class coefficients: coefficients negated
]

{ #category : #printing }
DirichletSeries >> printOn: aStream [
	| c n first |
	first := true.
	coefficients startIndex to: coefficients printLimit do: [:i|
		c := coefficients at: i.
		c isZero
			ifFalse:
				[n := i - coefficients startIndex + 1.
				c printString first = $-
					ifTrue: [first ifFalse: [aStream nextPutAll: ' - '].
								c := c negated]
					ifFalse: [first ifFalse: [aStream nextPutAll: ' + ']].
				c printOn: aStream. first := false.
				n > 1 ifTrue: [aStream nextPut: $/; print: n; nextPutAll: 'x' super]]].
	aStream nextPutAll: ' + ...'
]

{ #category : #accessing }
DirichletSeries >> scalars [
	^ coefficients codomain
]

{ #category : #arithmetic }
DirichletSeries >> squared [
	^ self * self
]

{ #category : #operations }
DirichletSeries >> value: aNumber upTo: n [
	| answer |
	answer := aNumber zero.
	1 to: n do: [:i|
		| c |
		c := coefficients at: coefficients startIndex + i - 1.
		answer := answer + (c / (i raiseTo: aNumber))].
	^ answer
]
