"
Linear transformations between finite-rank free modules (or finite-dimensional vector spaces). They are homomorphisms of free modules, and are internally represented by a matrix and a choice of bases for the domain and codomain.

See FreeModule and FreeHomModule.
"
Class {
	#name : #LinearMap,
	#superclass : #ModuleMap,
	#instVars : [
		'domain',
		'codomain',
		'matrix'
	],
	#category : #'Mathematics-Modules-Free'
}

{ #category : #examples }
LinearMap class >> example1 [
	"The transposition of matrices is a linear map:"
	^ 'QQ^(3@2) to: QQ^(2@3) evaluating: [:A| A transposed]'
]

{ #category : #'instance creation' }
LinearMap class >> from: aDomain to: aCodomain evaluating: aBlock [
	"Answer a new instance of the receiver using the one argument block aBlock for evaluating each vector in the domain basis."
	| matrix |
	matrix := Matrix rows: (aDomain basis collect: [:each| aCodomain coordinatesOf: (aBlock value: each)]).
	^ self from: aDomain to: aCodomain matrix: matrix transposed
]

{ #category : #'instance creation' }
LinearMap class >> from: aFreeModule to: anotherFreeModule matrix: aMatrix [
	"Answer a new instance of the reciever defined by the matrix aMatrix in the default bases for the given domain and codomain."

	^ self new
		domain: aFreeModule;
		codomain: anotherFreeModule;
		matrix: aMatrix
]

{ #category : #operations }
LinearMap >> * anObject [
	^ self class from: domain to: codomain matrix: matrix * anObject
]

{ #category : #operations }
LinearMap >> + anObject [
	(self codomain includes: anObject) ifTrue: [^ AffineMap linearMap: self translation: anObject].
	"assume anObject is a LinearMap:"
	(self domain == anObject domain
		and: [self codomain == anObject codomain])
			ifTrue: [^ self class from: domain to: codomain matrix: matrix + anObject matrix].
	(self domain = anObject domain and: [self codomain = anObject codomain])
			ifTrue: [^ self class from: domain to: codomain evaluating: [:v| (self value: v) + (anObject value: v)]].
	^ DomainError signal: 'domains don''t match'
]

{ #category : #comparing }
LinearMap >> = aLinearMap [
	self == aLinearMap ifTrue: [^ true].
	(aLinearMap isKindOf: LinearMap) ifFalse: [^ false].
	(self domain == aLinearMap domain
		and: [self codomain == aLinearMap codomain])
			ifTrue: [^ self matrix = aLinearMap matrix].
	(self domain = aLinearMap domain and: [self codomain = aLinearMap codomain])
		ifFalse: [^ false].
	self domain basis do: [:each|
		(self value: each) = (aLinearMap value: each)
			ifFalse: [^ false]].
	^ true
]

{ #category : #operations }
LinearMap >> adjoint [
	"Answer the transpose (or dual, or adjoint) of the receiver.
	The assignment of a linear map f:V->W to its dual f*:W*->V* produces an injective linear map between Hom(V,W) and Hom(W*,V*).
	This is the 'operator adjoint', not to be confused with the 'Hilbert adjoint' that is defined for an operator in an inner product space."
	^ self class from: codomain dual to: domain dual matrix: matrix adjoint
]

{ #category : #spectrum }
LinearMap >> algebraicMultiplicityAt: anEigenvalue [
	^ self characteristicPolynomial multiplicityAt: anEigenvalue
]

{ #category : #converting }
LinearMap >> asPolynomial [
	"If the receiver is a linear form, answer the receiver as a polynomial in the coordinate ring of the domain."
	| P |
	self isLinearForm ifFalse: [DomainError signal: 'not a linear form'].
	P := self domain coordinateRing.
	^ (P tuple: P rank evaluating: [:i| P x: i]) dot: (self class from: self domain to: self codomain evaluating: self) matrix asTuple "use matrix in the standard basis"
]

{ #category : #converting }
LinearMap >> asRationalMap [
	| P polynomials |
	P := self domain coordinateRing.
	"use matrix in the standard basis:"
	polynomials := ((self class from: self domain to: self codomain evaluating: self) matrix over: P) * (P tuple: P rank evaluating: [:i| P x: i]).
	^ RationalMap from: P spec to: self codomain coordinateRing spec polynomials: polynomials asArray
]

{ #category : #converting }
LinearMap >> asTensor [
	"Answer the tensor expansion of the receiver."
	^ self domain dual í self codomain evaluating: [:indices| matrix at: indices second @ indices first]
]

{ #category : #accessing }
LinearMap >> automorphism [
	"Answer the field automorphism associated with the receiver, looking at the receiver as a semilinear transformation. This is the identity automorphism."
	^ self domain scalars id
]

{ #category : #accessing }
LinearMap >> bitSize [
	^ matrix bitSize
]

{ #category : #operations }
LinearMap >> characteristicPolynomial [
	self isEndomorphism ifFalse: [DomainError signal: 'not an endomorphism'].
	^ matrix characteristicPolynomial
]

{ #category : #accessing }
LinearMap >> codomain [
	^ codomain
]

{ #category : #'accessing-private' }
LinearMap >> codomain: aFreeModule [
	codomain := aFreeModule
]

{ #category : #private }
LinearMap >> computeLeftInverse [
	^ self isMonomorphism ifTrue: [self class from: codomain to: domain matrix: matrix leftInverse]
]

{ #category : #private }
LinearMap >> computeRightInverse [
	^ self isEpimorphism ifTrue: [self class from: codomain to: domain matrix: matrix rightInverse]
]

{ #category : #operations }
LinearMap >> corank [
	^ self cokernel rank
]

{ #category : #operations }
LinearMap >> determinant [
	self isEndomorphism ifFalse: [DomainError signal: 'not an endomorphism'].
	^ matrix determinant
]

{ #category : #accessing }
LinearMap >> domain [
	^ domain
]

{ #category : #'accessing-private' }
LinearMap >> domain: aFreeModule [
	domain := aFreeModule
]

{ #category : #spectrum }
LinearMap >> eigenspaceAt: anEigenvalue [
	^ (self - (self identity * anEigenvalue)) kernel
]

{ #category : #spectrum }
LinearMap >> eigenvalues [
	self isEndomorphism ifFalse: [DomainError signal: 'not an endomorphism'].
	^ matrix eigenvalues
]

{ #category : #operations }
LinearMap >> fiberAt: aVector [
	"Answer the fiber (or inverse image) of aVector.
	The answer is an affine subspace (a linear variety or flat)."
	| n B M1 V r j0 d x |
	n := matrix width.
	B := codomain coordinatesOf: aVector.
	"1. Compute kernel"
	M1 := matrix | B.
	V := M1 kernelMatrix.
	r := V height.
	"2. Solution exists?"
	j0 := (1 to: r) detect: [:j| (V at: j@(n+1)) isZero not] ifNone: [^ nil "no solution"].
	d := (V at: j0@(n+1)) negated.
	x := self scalars tuple: n evaluating: [:i| (V at: j0@i) / d].
	"K := V copyFrom: 1@1 to: (r-1)@n. <- this is 'self matrix kernelMatrix', should avoid computing the kernel again, and cache it"
	^ self kernel + (domain elementAt: x)
]

{ #category : #spectrum }
LinearMap >> geometricMultiplicityAt: anEigenvalue [
	^ (self eigenspaceAt: anEigenvalue) dimension
]

{ #category : #accessing }
LinearMap >> identity [
	^ self class from: domain to: codomain matrix: matrix identity
]

{ #category : #operations }
LinearMap >> index [
	"Answer the index of the receiver, assuming it is an endomorphism.
	This is precisely the Euler characteristic of the 2-term complex 0 -> Domain -> Codomain -> 0."
	^ self kernel rank - self cokernel rank
]

{ #category : #operations }
LinearMap >> inverse [
	"Answer the inverse of the receiver. Answer nil if the receiver is not an isomorphism."

	^ self domain dimension = self codomain dimension ifTrue: [self leftInverse]
]

{ #category : #testing }
LinearMap >> isConstant [
	"Answer true if the receiver is a constant transformation."

	^ self rank <= 1
]

{ #category : #testing }
LinearMap >> isIdentity [
	^ self isEndomorphism and: [matrix isIdentity]
]

{ #category : #testing }
LinearMap >> isInjective [
	^ self rank = self domain rank
]

{ #category : #testing }
LinearMap >> isInvertible [
	^ matrix isInvertible
]

{ #category : #testing }
LinearMap >> isLinearForm [
	"Answer true if the receiver is a linear form (or linear functional, one-form, covector)."
	^ self codomain isKindOf: RingAsModule
]

{ #category : #testing }
LinearMap >> isLocallySimple [
	"Answer true if the receiver is locally simple.
	Given a linear map f:M->N, it is locally simple if there exists a map g:N->M satisfying fgf = f."
	^ self notYetImplemented
]

{ #category : #testing }
LinearMap >> isOrthogonal [
	^ matrix isOrthogonal
]

{ #category : #testing }
LinearMap >> isScalar [
	^ self matrix isScalar
]

{ #category : #testing }
LinearMap >> isSemisimple [
	^ self matrix isSemisimple
]

{ #category : #testing }
LinearMap >> isSurjective [
	^ self rank = self codomain rank
]

{ #category : #testing }
LinearMap >> isUnimodular [
	^ self matrix isUnimodular
]

{ #category : #testing }
LinearMap >> isZero [
	^ matrix isZero
]

{ #category : #operations }
LinearMap >> kernel [
	^ self propertyAt: #kernel ifAbsentPut: [self isTrivial ifTrue: [self domain] ifFalse: [self domain span: matrix kernelMatrix]]
]

{ #category : #operations }
LinearMap >> kernel2 [
	^ self propertyAt: #kernel ifAbsentPut: [(self fiberAt: self codomain ambient zero) direction] "! 3-5 times slower than the other implementaiton"
]

{ #category : #operations }
LinearMap >> leftInverse [
	"Answer a left inverse (or retraction) of the receiver.
	Answer nil if the receiver is not a monomorphism."
	^ self propertyAt: #leftInverse ifAbsentPut: [self computeLeftInverse]
]

{ #category : #accessing }
LinearMap >> matrix [
	"Answer the matrix associated to the receiver with respect to the chosen domain and codomain bases."
	^ matrix
]

{ #category : #'accessing-private' }
LinearMap >> matrix: aMatrix [
	matrix := aMatrix
]

{ #category : #operations }
LinearMap >> minimalPolynomial [
	self isEndomorphism ifFalse: [DomainError signal: 'not an endomorphism'].
	^ matrix minimalPolynomial
]

{ #category : #operations }
LinearMap >> negated [
	"Answer the additive inverse of the receiver."

	^ self class from: domain to: codomain matrix: matrix negated
]

{ #category : #operations }
LinearMap >> nullity [
	"Answer the dimension of the kernel of the receiver."
	^ matrix width - self rank
]

{ #category : #printing }
LinearMap >> printOn: aStream [
	| A B f |
	self isIdentity ifTrue: [aStream nextPutAll: 'id'. ^ self].
	self negated isIdentity ifTrue: [aStream nextPutAll: '-id'. ^ self].
	self isZero ifTrue: [aStream nextPut: $0. ^ self].
	self isLinearForm ifTrue: [aStream print: self asPolynomial. ^ self].
	"If the codomain is tuples, print the linear map as a tuple of linear forms:"
	(self codomain isKindOf: TupleModule) ifTrue:
		[aStream nextPut: $(.
		matrix rows
			do: [:each| aStream print: (self domain dual elementAt: each)]
			separatedBy: [aStream nextPutAll: ', '].
		aStream nextPut: $).
		^ self].
	"Print it as a linear combination of the generators of the codomain:"
	A := self domain coordinateRing.
	B := A polynomialsIn: self codomain names.
	f := B zero.
	matrix rows
		withIndexDo: [:each :i| f := (B x: i) * (self domain dual elementAt: each) asPolynomial + f].
	aStream print: f
]

{ #category : #operations }
LinearMap >> rank [
	^ matrix rank
]

{ #category : #operations }
LinearMap >> rightInverse [
	"Answer a right inverse (or section) of the receiver.
	Answer nil if the receiver is not an epimorphism."
	^ self propertyAt: #rightInverse ifAbsentPut: [self computeRightInverse]
]

{ #category : #accessing }
LinearMap >> scalars [
	^ matrix scalars
]

{ #category : #private }
LinearMap >> species [
	^ LinearMap
]

{ #category : #spectrum }
LinearMap >> spectrum [
	self isEndomorphism ifFalse: [DomainError signal: 'not an endomorphism'].
	^ matrix spectrum
]

{ #category : #operations }
LinearMap >> tensorProduct: aLinearMap [
	"Answer the tensor product of the receiver with the argument."
	^ self class from: domain tensorProduct: aLinearMap domain to: codomain tensorProduct: aLinearMap codomain matrix: matrix tensorProduct: aLinearMap matrix
]

{ #category : #operations }
LinearMap >> trace [
	self isEndomorphism ifFalse: [DomainError signal: 'not an endomorphism'].
	^ matrix trace
]

{ #category : #operations }
LinearMap >> value: anElement [
	(domain isTrivial or: [codomain isTrivial])
		ifTrue: [^ codomain ambient zero].
	^ codomain elementAt: matrix * (domain coordinatesOf: anElement)
]

{ #category : #operations }
LinearMap >> î [ aLinearMap
	"Answer the composition of the receiver with the argument."
	self domain == aLinearMap codomain
		ifTrue: [^ self class from: aLinearMap domain to: codomain matrix: matrix * aLinearMap matrix].
	self domain >= aLinearMap codomain
		ifTrue: [^ self class from: aLinearMap domain to: codomain evaluating: [:each| self value: (aLinearMap value: each)]].
	^ DomainError signal: 'domains don''t match'
]
