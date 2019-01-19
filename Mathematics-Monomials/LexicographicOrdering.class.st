"
The lexicographic ordering is the 'dictionary' ordering.

The lexicographic ordering has the property that for each subring S[x1..xn] <= R, and each polynomial f in R, f is in S iff its leading monomial is in S.

Elimination by the lexicographic ordering produces elements of an ideal which are free of the first variable.
"
Class {
	#name : #LexicographicOrdering,
	#superclass : #MonomialOrdering,
	#category : #'Mathematics-Monomials-Orderings'
}

{ #category : #ordering }
LexicographicOrdering >> compare: aMonomial with: anotherMonomial [
	| e1 e2 n1 n2 |
	e1 := aMonomial exponents.
	e2 := anotherMonomial exponents.
	n1 := e1 size.
	n2 := e2 size.
	1 to: indeterminates size do: [:i|
		| xi a b |
		xi := indeterminates at: i.
		a := xi <= n1 ifTrue: [e1 at: xi] ifFalse: [0].
		b := xi <= n2 ifTrue: [e2 at: xi] ifFalse: [0].
		a > b ifTrue: [^ 1].
		a = b ifFalse: [^ -1]].
	^ 0
]

{ #category : #testing }
LexicographicOrdering >> isGlobal [
	^ true
]

{ #category : #accessing }
LexicographicOrdering >> type [
	^ #lex
]
