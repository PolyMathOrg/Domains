"
The graded (or total degree) reverse lexicographic ordering first compares the total degree of the monomials, and takes the monomial with largest total degree. If two monomials have the same total degree, the reverse lexicographic ordering is used to break the tie (this is the lexicographic ordering on the reversed list of indeterminates (xn, ..., x1).

The graded reverse lexicographic ordering has the property that for each subring S[x1..xn] <= R, and each homogeneous polynomial f in S[x1..xi], xi divides f iff it divides the leading monomial.

Elimination by the graded reverse lexicographic ordering produces elements of a homogeneous ideal which are divisible by the last variable.
"
Class {
	#name : #GradedReverseLexicographicOrdering,
	#superclass : #MonomialOrdering,
	#category : #'Mathematics-Monomials-Orderings'
}

{ #category : #ordering }
GradedReverseLexicographicOrdering >> blockCompare: aMonomial with: anotherMonomial [
	| d1 d2 n1 n2 e1 e2 |
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
GradedReverseLexicographicOrdering >> compare: aMonomial with: anotherMonomial [
	| d1 d2 n1 n2 e1 e2 |
	(d1 := aMonomial degree) > (d2 := anotherMonomial degree) ifTrue: [^ 1].
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
GradedReverseLexicographicOrdering >> isGlobal [
	^ true
]

{ #category : #testing }
GradedReverseLexicographicOrdering >> isGraded [
	^ true
]

{ #category : #accessing }
GradedReverseLexicographicOrdering >> type [
	^ #grevlex
]
