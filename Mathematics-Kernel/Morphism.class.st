"
Abstract superclass for Functions and other morphisms. See subclasses, and Domain and HomSet.

Examples (three equivalent ways to construct a vector space homomorphism):
	QQ^3 to: QQ^3 evaluating: [:v| (v x - v y, v x, v z)].
	(QQ^3 hom: QQ^3) evaluating: [:v| (v x - v y, v x, v z)].
	(QQ^3) endomorphisms evaluating: [:v| (v x - v y, v x, v z)].

References:
	https://en.wikipedia.org/wiki/Morphism

"
Class {
	#name : #Morphism,
	#superclass : #Object,
	#category : #'Mathematics-Kernel'
}

{ #category : #examples }
Morphism class >> example1Projection [
	"Algebraic structures often come equipped with some canonical morphisms.
	Here we construct the direct product of the ring of rational integers
	with the field of rational numbers, and get the projection to the second component."
	^ 'ZZ ◊ QQ projection: 2'
]

{ #category : #examples }
Morphism class >> example21Embedding [
	"Here we construct Q[x], the ring of univariate polynomials over the rational numbers.
	It comes equipped with a canonical embedding from the rational numbers to the constant polynomials."
	| R phi F psi |
	R := QQ polynomials.
	phi := R embedding.
	"Then we construct its field of fractions Q(x) (the rational functions),
	that comes with a cannonical embedding from the polynomial ring to the rational functions with denominator 1."
	F := R fractions.
	psi := F embedding.
	"Finally we compose them to get an embedding from the rational numbers Q to the field of univariate rational functions Q(x), that sends a number to a constant rational function."
	^ psi î phi
]

{ #category : #examples }
Morphism class >> example22EasierEmbedding [
	"Another way to construct the canonical embedding from Q to the rational functions over Q."
	^ 'QQ  QQ polynomials fractions'
]

{ #category : #examples }
Morphism class >> example3CanonicalMorphism [
	"Canonical morphisms can be retrieved through the message #.
	For example, Z (the ring of integers) is the initial object in
	the category of commutative rings with unit, i.e. there's
	a canonical morphism from Z to any commutative ring:"
	^ 'ZZ  (QQ polynomialsIn: #(x y z))'
]

{ #category : #examples }
Morphism class >> example4CanonicalMorphism [
	"The quotient map from a polynomial ring R to a quotient by
	one of its ideals R/I is another example of canonical morphism."
	| R x I |
	R := QQ polynomials.
	x := R x.
	I := R * (x squared + 1).
	^ 'R  (R / I)'
]

{ #category : #examples }
Morphism class >> example5CanonicalMorphism [
	"The message # can be sent to a Morphism with a Domain as
	argument, or to a Domain with a Morphism as argument.
	This yields canonical constructions.
	For example, given an arbitrary ring homomorphism,
	we can send it *canonically* to a quotient of its codomain."
	| R phi x I |
	R := (ZZ/5) polynomials. "univariate polynomials over Z/<5>"
	phi := R frobenius. "the Frobenius endomorphism"
	x := R x.
	I := R * (x squared + 1).
	^ 'phi  (R / I)'
]

{ #category : #examples }
Morphism class >> example6GLAsMatrixGroupAction [
	"The action of the group GL(3,Q) on the Q-vector space of 3-tuples.
	The action is matrix multiplication by a tuple."
	^ (GeneralLinearMatrixGroup new: 3 over: QQ) action
]

{ #category : #printing }
Morphism >> arrowPrintOn: aStream [
	'aStream print: self domain; nextPut: $; print: self codomain'
]

{ #category : #printing }
Morphism >> arrowPrintString [
	| limit limitedString |
	limit := 100.
	limitedString := String streamContents: [:s | self arrowPrintOn: s] limitedTo: limit.
	limitedString size < limit ifTrue: [^ limitedString].
	^ limitedString , '...etc...'
]

{ #category : #accessing }
Morphism >> codomain [
	^ self subclassResponsibility
]

{ #category : #accessing }
Morphism >> coimage [
	^ self domain / self kernel
]

{ #category : #accessing }
Morphism >> cokernel [
	^ self codomain / self image
]

{ #category : #operations }
Morphism >> compose: aMorphism [
	"Answer the composition of the receiver with the argument.
	Given the argument f:X -> Y and the receiver g:Y -> Z, answer gîf:X -> Z."

	^ self subclassResponsibility
]

{ #category : #operations }
Morphism >> composeWithMeTimes: anInteger [
	"îî"

	"Answer the receiver composed with itself anInteger times."

	anInteger = 1
		ifTrue: [ ^ self ].
	anInteger = 0
		ifTrue: [ ^ self identity ].
	anInteger > 1
		ifTrue: [ ^ ((self compose: self) composeWithMeTimes: anInteger // 2)
				compose: (self composeWithMeTimes: anInteger \\ 2) ].
	^ (self composeWithMeTimes: anInteger negated) inverse
]

{ #category : #operations }
Morphism >> composition: aCodomain [ ""
	"Answer the composition with the canonical morphism from the codomain of the receiver to aCodomain. See also Domain>>."
	^ 'self codomain  aCodomain ifNotNil: [:aMorphism| aMorphism î self]'
]

{ #category : #accessing }
Morphism >> domain [
	^ self subclassResponsibility
]

{ #category : #testing }
Morphism >> hasLeftInverse [
	^ self leftInverse notNil
]

{ #category : #testing }
Morphism >> hasRightInverse [
	^ self rightInverse notNil
]

{ #category : #accessing }
Morphism >> identity [
	^ self domain id
]

{ #category : #accessing }
Morphism >> image [
	^ self domain apply: self
]

{ #category : #operations }
Morphism >> inverse [
	self isEndomorphism ifFalse: [self error: 'ambiguous inverse'].
	^ self leftInverse
]

{ #category : #testing }
Morphism >> is: aSymbol [
	^ aSymbol == #Morphism or: [super is: aSymbol]
]

{ #category : #testing }
Morphism >> isAutomorphism [
	^ self isEndomorphism and: [self isIsomorphism]
]

{ #category : #testing }
Morphism >> isBimorphism [
	^ self isIsomorphism
]

{ #category : #testing }
Morphism >> isEndomorphism [
	^ self domain = self codomain
]

{ #category : #testing }
Morphism >> isIdentity [
	^ self = self domain id
]

{ #category : #testing }
Morphism >> isInvertible [
	^ self inverse notNil
]

{ #category : #testing }
Morphism >> isIsomorphism [
	^ self isEpimorphism and: [self isMonomorphism]
]

{ #category : #testing }
Morphism >> isSplitEpimorphism [
	^ self hasRightInverse
]

{ #category : #testing }
Morphism >> isSplitMonomorphism [
	^ self hasLeftInverse
]

{ #category : #testing }
Morphism >> isTrivial [
	^ self kernel = self domain
]

{ #category : #operations }
Morphism >> leftInverse [
	^ self subclassResponsibility
]

{ #category : #printing }
Morphism >> name [
	^ String streamContents: [:aStream| super printOn: aStream]
]

{ #category : #accessing }
Morphism >> parent [
	"A morphism f:A->B belongs to Hom(A,B)."
	^ self domain hom: self codomain
]

{ #category : #printing }
Morphism >> printOn: aStream [
	aStream nextPutAll: self name; nextPut: $:.
	self arrowPrintOn: aStream
]

{ #category : #accessing }
Morphism >> retraction [
	^ self leftInverse
]

{ #category : #operations }
Morphism >> rightInverse [
	^ self subclassResponsibility
]

{ #category : #accessing }
Morphism >> section [
	^ self rightInverse
]

{ #category : #operations }
Morphism >> | aCodomain [
	"See also Domain>>|."
	^ self corestrictedTo: aCodomain
]
