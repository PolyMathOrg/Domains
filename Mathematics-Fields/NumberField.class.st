"
Algebraic number fields, i.e. finite (and thus algebraic) field extensions of the rational numbers Q. Number fields can also be viewed as vector spaces over Q.

"
Class {
	#name : #NumberField,
	#superclass : #AlgebraicExtension,
	#category : #'Mathematics-Fields-Number Fields'
}

{ #category : #'instance creation' }
NumberField class >> adjoint: anAlgebraicNumber [
	^ self new adjoint: anAlgebraicNumber
]

{ #category : #examples }
NumberField class >> example [
	^ QQ adjoin: RealAlgebraicNumber sqrt2
]

{ #category : #accessing }
NumberField >> adjoint [
	^ self propertyAt: #adjoint ifAbsentPut: [self polynomial anyRootIn: CC]
]

{ #category : #'accessing-private' }
NumberField >> adjoint: anAlgebraicNumber [
	self propertyAt: #adjoint put: anAlgebraicNumber.
	self polynomial: anAlgebraicNumber minimalPolynomial
]

{ #category : #operations }
NumberField >> archimedeanPlaces [
	^ self notYetImplemented
]

{ #category : #accessing }
NumberField >> basis [
	^ self integralBasis
]

{ #category : #accessing }
NumberField >> discriminant [
	"The discriminant of an integral basis is independent of the choice of basis and it's called the discriminant of the field K and denoted d(K)."
	^ self propertyAt: #discriminant ifAbsentPut: [self integralBasis discriminant]
]

{ #category : #accessing }
NumberField >> integers [
	"Answer the ring of integers of the receiver."
	^ NumberRing on: self
]

{ #category : #accessing }
NumberField >> integralBasis [
	^ self notYetImplemented "COHEN 6.1.8"
]

{ #category : #testing }
NumberField >> isCubic [
	^ self degree = 3
]

{ #category : #testing }
NumberField >> isGaloisExtension [
	self degree = 3 ifTrue: [^ self polynomial discriminant isPerfectSquare].
	self notYetImplemented
]

{ #category : #testing }
NumberField >> isGlobalField [
	^ true
]

{ #category : #testing }
NumberField >> isImaginary [
	"Answer true if no embedding into the complex numbers has image contained in the real numbers."
	^ self signature first = 0
]

{ #category : #testing }
NumberField >> isMonogenic [
	^ self propertyAt: #isMonogenic
]

{ #category : #testing }
NumberField >> isQuadratic [
	^ self degree = 2
]

{ #category : #testing }
NumberField >> isReal [
	"Answer true if every embedding into the complex numbers has image contained in the real numbers."
	^ self signature second = 0
]

{ #category : #morphisms }
NumberField >> isomorphismTo: aNumberField [
	"Field Isomorphism Problem. Answer an isomorphism to aNumberField if there's any, or nil.
	Reference: Henri Cohen, 'A Course In Computational Algebraic Number Theory', Algorithm 4.5.5 and 4.5.6."
	(self polynomial isIrreducible and: [self polynomial isPrimitive])
		ifFalse: [^ self error: 'not irreducible and primitive defining polynomial'].
	(aNumberField polynomial isIrreducible and: [aNumberField polynomial isPrimitive])
		ifFalse: [^ self error: 'not irreducible and primitive defining polynomial'].
	self polynomial degree = aNumberField polynomial degree
		ifFalse: [^ nil].
	"..."
	self notYetImplemented
]

{ #category : #operations }
NumberField >> nonArchimedeanPlaces [
	^ self notYetImplemented
]

{ #category : #morphisms }
NumberField >> preferedEmbedding [
	^ self embeddings detect: [:one| (one value: self x) = self adjoint]
]

{ #category : #printing }
NumberField >> printOn: aStream [
	"aStream print: self scalars; nextPut: $(; print: self adjoint; nextPut: $)"
	aStream print: self scalars; nextPut: $(; print: self polynomial; nextPut: $)
]

{ #category : #morphisms }
NumberField >> realEmbeddings [
	^ self embeddingsIn: RR
]

{ #category : #operations }
NumberField >> regulator [
	^ self notYetImplemented
]

{ #category : #accessing }
NumberField >> scalars [
	^ QQ
]

{ #category : #accessing }
NumberField >> signature [
	"Answer the signature (r1,r2) of the receiver, i.e. r1 the number of embeddings whose image is real, and 2*r2 the number of non-real complex embeddings."
	^ self polynomial signature
]
