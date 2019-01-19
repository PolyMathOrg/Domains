"
The local graded lexicographic order (lglex) is the negation of the global graded lexicographic order (glex).

This is the order called 'lglex' in Magma. What Singular calls 'Ds', on the other hand, is like this but with the indeterminates reversed.
"
Class {
	#name : #LocalGradedLexicographicOrdering,
	#superclass : #MonomialOrdering,
	#category : #'Mathematics-Monomials-Orderings'
}

{ #category : #ordering }
LocalGradedLexicographicOrdering >> blockCompare: aMonomial with: anotherMonomial [
	| d1 d2 e1 e2 n1 n2 |
	e1 := aMonomial exponents.
	e2 := anotherMonomial exponents.
	n1 := e1 size.
	n2 := e2 size.

	d1 := 0.
	d2 := 0.
	1 to: indeterminates size do: [:i|
		| xi a b |
		xi := indeterminates at: i.
		xi <= n1 ifTrue: [d1 := d1 + (e1 at: xi)].
		xi <= n2 ifTrue: [d2 := d2 + (e2 at: xi)]].
	d1 < d2 ifTrue: [^ 1].
	d1 = d2 ifFalse: [^ -1].

	indeterminates size to: 1 by: -1 do: [:i|
		| xi a b |
		xi := indeterminates at: i.
		a := xi <= n1 ifTrue: [e1 at: xi] ifFalse: [0].
		b := xi <= n2 ifTrue: [e2 at: xi] ifFalse: [0].
		a < b ifTrue: [^ 1].
		a = b ifFalse: [^ -1]].
	^ 0
]

{ #category : #ordering }
LocalGradedLexicographicOrdering >> compare: aMonomial with: anotherMonomial [
	| d1 d2 e1 e2 n1 n2 |
	(d1 := aMonomial degree) < (d2 := anotherMonomial degree) ifTrue: [^ 1].
	d1 = d2 ifFalse: [^ -1].
	e1 := aMonomial exponents.
	e2 := anotherMonomial exponents.
	n1 := e1 size.
	n2 := e2 size.
	indeterminates size to: 1 by: -1 do: [:i|
		| xi a b |
		xi := indeterminates at: i.
		a := xi <= n1 ifTrue: [e1 at: xi] ifFalse: [0].
		b := xi <= n2 ifTrue: [e2 at: xi] ifFalse: [0].
		a < b ifTrue: [^ 1].
		a = b ifFalse: [^ -1]].
	^ 0
]

{ #category : #testing }
LocalGradedLexicographicOrdering >> isGraded [
	^ true
]

{ #category : #testing }
LocalGradedLexicographicOrdering >> isLocal [
	^ true
]

{ #category : #accessing }
LocalGradedLexicographicOrdering >> type [
	^ #lglex
]
