Extension { #name : #Integer }

{ #category : #'*Mathematics-Polynomials' }
Integer >> nextPrime [ 

	| pivot |
	self < 2 ifTrue: [^2].
	pivot := self + 1 bitOr: 1.
	[pivot isPrime] whileFalse: [pivot := pivot + 2].
	^pivot
]
