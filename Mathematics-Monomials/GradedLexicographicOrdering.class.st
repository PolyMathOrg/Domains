"
The graded (or total degree) lexicographic ordering first compares the total degree of the monomials, and takes the monomial with largest total degree. If two monomials have the same total degree, the lexicographic ordering is used to break the tie.

The graded lexicographic ordering has the property that for each subring S[x1..xn] <= R, and each homogeneous polynomial f in R, f is in S iff its leading monomial is in S.

Elimination by the graded lexicographic ordering produces elements of an homogeneous ideal which are free of the first variable.
"
Class {
	#name : #GradedLexicographicOrdering,
	#superclass : #MonomialOrdering,
	#category : #'Mathematics-Monomials-Orderings'
}

{ #category : #ordering }
GradedLexicographicOrdering >> blockCompare: aMonomial with: anotherMonomial [
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
	d1 > d2 ifTrue: [^ 1].
	d1 = d2 ifFalse: [^ -1].

	1 to: indeterminates size do: [:i|
		| xi a b |
		xi := indeterminates at: i.
		a := xi <= n1 ifTrue: [e1 at: xi] ifFalse: [0].
		b := xi <= n2 ifTrue: [e2 at: xi] ifFalse: [0].
		a > b ifTrue: [^ 1].
		a = b ifFalse: [^ -1]].
	^ 0
]

{ #category : #ordering }
GradedLexicographicOrdering >> compare: aMonomial with: anotherMonomial [
	| d1 d2 e1 e2 n1 n2 |
	(d1 := aMonomial degree) > (d2 := anotherMonomial degree) ifTrue: [^ 1].
	d1 = d2 ifFalse: [^ -1].
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
GradedLexicographicOrdering >> isGlobal [
	^ true
]

{ #category : #testing }
GradedLexicographicOrdering >> isGraded [
	^ true
]

{ #category : #accessing }
GradedLexicographicOrdering >> type [
	^ #glex
]
