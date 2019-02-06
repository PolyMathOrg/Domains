"
(Finite) algebraic extensions E/F of a field (or ring) F. They are defined by an irreducible polynomial f with coefficients in F, and are isomorphic to F[x]/<f>. An extension field (or ring) E/F can also be viewed as a vector space (or module) over F.

See also AlgebraicElement.
"
Class {
	#name : #AlgebraicExtension,
	#superclass : #AffineRing,
	#category : #'Mathematics-Fields'
}

{ #category : #examples }
AlgebraicExtension class >> example [
	^ 'QQ extension: QQ polynomials x^4 - 2'
]

{ #category : #'instance creation' }
AlgebraicExtension class >> polynomial: aPolynomial [
	"Answer a new algebraic field extension K(f) where f is the given polynomial in K[x]. The polynomial must be irreducible, otherwise there would be zero divisors."
	^ self new polynomial: aPolynomial
]

{ #category : #converting }
AlgebraicExtension >> asModule [
	^ AlgebraicExtensionAsModule on: self
"	^ FreeModule
		basis: ((1 to: self degree) collect: [:i| self x ^ (i-1)])
		coordinates: [:aVector| self scalars tuple: self degree evaluating: [:i| aVector representative coefficientAtDegree: i-1]]
		over: self scalars"

"
	QQ extension: QQ polynomials x^4 - 2 :: asVectorSpace
"
]

{ #category : #converting }
AlgebraicExtension >> asVectorSpace [
	self scalars isField ifFalse: [^ DomainError signal].
	^ self asModule
]

{ #category : #morphisms }
AlgebraicExtension >> automorphisms [
	"Answer the Galous group of the receiver (assuming the receiver is a Galois extension)."
	self isFinite ifTrue: [^ TransformationGroup new generators: {self frobenius}].
	self flag: #fix. "This is actually isomorphic to the Galois group, not the actual Galois group, it should act on elements of the extension and it's not the full symmetric group."
	^ SymmetricGroup on: (self embeddings collect: [:each| each value: self x])
]

{ #category : #accessing }
AlgebraicExtension >> characteristic [
	^ self scalars characteristic
]

{ #category : #accessing }
AlgebraicExtension >> degree [
	"Answer the degree [E:F] of the relative extension E/F."
	^ self polynomial degree "conflicts with AffineRing>>degree?"
]

{ #category : #accessing }
AlgebraicExtension >> degreeOver: aSubfield [
	"Answer the degree [E:F] of the relative extension E/F."
	self = aSubfield ifTrue: [^ 1].
	self scalars = aSubfield ifTrue: [^ self degree].
	^ self degree * (self scalars degreeOver: aSubfield)
]

{ #category : #private }
AlgebraicExtension >> elementClass [
	^ AlgebraicElement
]

{ #category : #morphisms }
AlgebraicExtension >> embeddings [
	"Answer the n distinct embeddings of the receiver in the algebraic closure of the base field, where n is the degree of the receiver. In the case of number fields, the embeddings go to the complex algebraic numbers.
	When the receiver is a Galois extension, the embeddings send each element to one of its conjugates, and their images are the same."
	^ self propertyAt: #embeddings ifAbsentPut: [self embeddingsIn: self scalars algebraicClosure]
]

{ #category : #morphisms }
AlgebraicExtension >> embeddingsIn: aField [
	^ (self polynomial rootsIn: aField) asArray
		collect: [:x| self to: aField evaluating: [:alpha| alpha representative value: x]]
]

{ #category : #testing }
AlgebraicExtension >> isField [
	^ self scalars isField
]

{ #category : #testing }
AlgebraicExtension >> isIntegralDomain [
	^ self isField or: [super isIntegralDomain]
]

{ #category : #accessing }
AlgebraicExtension >> polynomial [
	^ self relations generator
]

{ #category : #'accessing-private' }
AlgebraicExtension >> polynomial: aPolynomial [
	self relations: aPolynomial parent * aPolynomial
]

{ #category : #printing }
AlgebraicExtension >> printOn: aStream [
	(self hasProperty: #name)
		ifTrue: [ ^ super printOn: aStream ].
	aStream
		print: self scalars;
		nextPut: $(;
		print: self polynomial;
		nextPut: $)
]

{ #category : #accessing }
AlgebraicExtension >> size [
	^ (self scalars size) raisedTo: (self degree)
]

{ #category : #accessing }
AlgebraicExtension >> x [
	"Answer the transcendental element of the receiver."
	^ self project: self base x
]
