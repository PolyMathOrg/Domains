"
The local lexicographic order (llex) is the negation of the global lexicographic order.

This is the order called 'llex' in Magma. What Singular calls 'ls', on the other hand, is like this but with the indeterminates reversed.
"
Class {
	#name : #LocalLexicographicOrdering,
	#superclass : #MonomialOrdering,
	#category : #'Mathematics-Monomials-Orderings'
}

{ #category : #ordering }
LocalLexicographicOrdering >> compare1: aMonomial with: anotherMonomial [
	"This is Magma's 'llex' ordering."
	| e1 e2 n1 n2 |
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

{ #category : #ordering }
LocalLexicographicOrdering >> compare2: aMonomial with: anotherMonomial [
	"This is Singular's 'ls' ordering (indeterminates are reversed)."
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
		a < b ifTrue: [^ 1].
		a = b ifFalse: [^ -1]].
	^ 0
]

{ #category : #ordering }
LocalLexicographicOrdering >> compare: aMonomial with: anotherMonomial [
	| e1 e2 n1 n2 |
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
LocalLexicographicOrdering >> isLocal [
	^ true
]

{ #category : #accessing }
LocalLexicographicOrdering >> type [
	^ #llex
]
