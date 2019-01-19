"
Elements of finite algebraic field (or ring) extensions. See AlgebraicExtension.
"
Class {
	#name : #AlgebraicElement,
	#superclass : #RegularFunction,
	#category : #'Mathematics-Fields'
}

{ #category : #'as yet unclassified' }
AlgebraicElement >> = anObject [
	(self class = anObject class and: [parent = anObject parent])
		ifTrue: [^ representative = anObject representative].
	^ self = (parent ! anObject)
]

{ #category : #'as yet unclassified' }
AlgebraicElement >> characteristicPolynomial [
	^ self representation characteristicPolynomial
]

{ #category : #'as yet unclassified' }
AlgebraicElement >> characteristicPolynomial2 [
	| x |
	x := QQ algebraicClosure polynomials x.
	^ self parent base ! (self parent embeddings product: [:each| x - (each value: self)])
]

{ #category : #'as yet unclassified' }
AlgebraicElement >> hash [
	^ representative hash
]

{ #category : #'as yet unclassified' }
AlgebraicElement >> minimalPolynomial [
	^ self representation minimalPolynomial

"	| x |
	x := self parent x.
	^ self conjugates product: [:each| x - each] :: as: self parent base"
]

{ #category : #'as yet unclassified' }
AlgebraicElement >> minimalPolynomial2 [
	^ (self parent preferedEmbedding value: self) minimalPolynomial
]

{ #category : #'as yet unclassified' }
AlgebraicElement >> norm [
	| f |
	f := self minimalPolynomial.
	^ f independentCoefficient / f leadingCoefficient * (f degree even ifTrue: [1] ifFalse: [-1])
	
"alternatively:
	^ self representation determinant"
]

{ #category : #'as yet unclassified' }
AlgebraicElement >> representation [
	"Answer the representation map defined by multiplication by the receiver."
	^ self parent asVectorSpace endomorphisms evaluating: [:x| x * self]
]

{ #category : #'as yet unclassified' }
AlgebraicElement >> symmetricFunction: i [
	^ self notYetImplemented
]

{ #category : #'as yet unclassified' }
AlgebraicElement >> trace [
	"Answer the absolute trace of the receiver."
	| f |
	f := self minimalPolynomial.
	^ (f coefficientAtDegree: f degree - 1) negated
	
"alternatively:
	^ self representation trace"
]
