"
Bilinear forms are functions from MxM to R (where M is a R-module) that satisfy:
	B(v+cv', w) = B(v, w) + cB(v', w)
	B(v, w+cw') = B(v, w) + cB(v, w')

"
Class {
	#name : #BilinearForm,
	#superclass : #BilinearMap,
	#instVars : [
		'halfDomain',
		'matrix'
	],
	#category : #'Mathematics-Multilinear'
}

{ #category : #'instance creation' }
BilinearForm class >> from: aCartesianProduct evaluating: aBlock [ 
	| V basis matrix n |
	V := aCartesianProduct components first.
	basis := V basis.
	n := basis size.
	matrix := V scalars
					matrix: n
					evaluating: [:i :j|
						aBlock value: {(basis at: i). (basis at: j)}].
	^ self fromHalf: V matrix: matrix
]

{ #category : #'instance creation' }
BilinearForm class >> fromHalf: aVectorSpace evaluating: aBlock [ 
	| basis matrix n |
	basis := aVectorSpace basis.
	n := basis size.
	matrix := 'aVectorSpace scalars ^ (n@n)
						evaluating: [:i :j|
							aBlock value: {(basis at: i). (basis at: j)}]'.
	^ self fromHalf: aVectorSpace matrix: matrix
]

{ #category : #'instance creation' }
BilinearForm class >> fromHalf: aFreeModule matrix: aMatrix [
	"Answer a new instance of the receiver representing the bilinear form associated to aMatrix in the given bases."
	^ self new halfDomain: aFreeModule; matrix: aMatrix
]

{ #category : #arithmetic }
BilinearForm >> * anObject [
	^ self class fromHalf: halfDomain matrix: matrix * anObject
]

{ #category : #arithmetic }
BilinearForm >> + aBilinearForm [
	halfDomain = aBilinearForm halfDomain ifFalse: [^ self error: 'domains don''t match'].
	^ self class
		from: halfDomain
		evaluating: [:each| (self value: each) + (aBilinearForm value: each)]
]

{ #category : #converting }
BilinearForm >> asPolynomial [
	| n P x y |
	n := matrix height.
	P := self scalars polynomialsIn: ((1 to: n) collect: [:i| 'x' asText, i printString sub]), ((1 to: n) collect: [:i| 'y' asText, i printString sub]).
	x := P tuple: n evaluating: [:i| P x: i].
	y := P tuple: n evaluating: [:i| P x: n+i].
	^ x dot: (matrix over: P) * y
]

{ #category : #converting }
BilinearForm >> asTensor [
	"Answer the tensor expansion of the receiver."
	^ self halfDomain dual í self halfDomain dual evaluating: [:indices| matrix at: indices second @ indices first]
]

{ #category : #converting }
BilinearForm >> asTensorLinearMap [
	"Bilinear forms on V are in 1-to-1 correspondence with linear maps from V tensor V to the base field K."
	^ self notYetImplemented
]

{ #category : #converting }
BilinearForm >> associatedQuadraticForm [
	"Answer the associated quadratic form Q(v) := B(v,v)."
	^ QuadraticForm from: halfDomain matrix: matrix
]

{ #category : #accessing }
BilinearForm >> bitSize [
	^ matrix bitSize
]

{ #category : #accessing }
BilinearForm >> codomain [
	^ self scalars
]

{ #category : #accessing }
BilinearForm >> domain [
	^ (halfDomain, halfDomain)
]

{ #category : #accessing }
BilinearForm >> halfDomain [
	^ halfDomain
]

{ #category : #'accessing-private' }
BilinearForm >> halfDomain: aFreeModule [
	halfDomain := aFreeModule
]

{ #category : #testing }
BilinearForm >> isAlternate [
	"A bilinear form B is called 'alternate' if B(v,v) = 0 for all v."
	matrix isSkewSymmetric ifFalse: [^ false].
	matrix diagonalDo: [:each| each isZero ifFalse: [^ false]].
	^ true
]

{ #category : #testing }
BilinearForm >> isAlternating [
	"A bilinear form B is called 'alternating' if B(v,v) = 0 for all v."
	matrix isSkewSymmetric ifFalse: [^ false].
	matrix diagonalDo: [:each| each isZero ifFalse: [^ false]].
	^ true
]

{ #category : #testing }
BilinearForm >> isNonDegenerate [
	"A bilinear form B is called 'non-degenerate' if B(v,w) = 0 for all w implies v = 0.
	B is non-degenerate iff the left and right radicals are trivial."
	^ self rank = self domain dimension
]

{ #category : #testing }
BilinearForm >> isReflexive [
	"A bilinear form B is called 'reflexive' if B(v,w) = 0 implies B(w,v) = 0 for all v,w."
	^ self isSymmetric or: [self isAlternating]
]

{ #category : #testing }
BilinearForm >> isSkewSymmetric [
	"A bilinear form B is called 'skew-symmetric' if B(v,w) = -B(w,v) for all v,w."
	^ matrix isSkewSymmetric
]

{ #category : #testing }
BilinearForm >> isSymmetric [
	"A bilinear form B is called 'symmetric' if B(v,w) = B(w,v) for all v,w."
	^ matrix isSymmetric
]

{ #category : #operations }
BilinearForm >> left [
	"Answer the linear map from the domain to its dual that fixes the right argument. If the bilinear form is non-degenerate, this map is an isomorphism."
	| V Vdual |
	V := self domain at: 1.
	Vdual := V dual.
	^ V to: Vdual evaluating: [:v| Vdual evaluating: [:w| self value: w value: v]]
]

{ #category : #operations }
BilinearForm >> leftRadical [
	^ self left kernel
]

{ #category : #accessing }
BilinearForm >> matrix [
	^ matrix
]

{ #category : #'accessing-private' }
BilinearForm >> matrix: aMatrix [
	matrix := aMatrix
]

{ #category : #arithmetic }
BilinearForm >> negated [
	^ self class fromHalf: halfDomain matrix: matrix negated
]

{ #category : #printing }
BilinearForm >> printOn: aStream [
	aStream print: self asPolynomial
]

{ #category : #operations }
BilinearForm >> rank [
	^ matrix rank
]

{ #category : #operations }
BilinearForm >> right [
	"Answer the linear map from the domain to its dual that fixes the left argument. If the bilinear form is non-degenerate, this map is an isomorphism."
	| V Vdual |
	V := self domain at: 2.
	Vdual := V dual.
	^ V to: Vdual evaluating: [:v| Vdual evaluating: [:w| self value: v value: w]]
]

{ #category : #operations }
BilinearForm >> rightRadical [
	^ self right kernel
]

{ #category : #accessing }
BilinearForm >> scalars [
	^ halfDomain scalars
]

{ #category : #operations }
BilinearForm >> skewSymmetricPart [
	| two |
	two := self scalars one * 2.
	^ self class
		fromHalf: halfDomain
		matrix: matrix - matrix transposed / two
]

{ #category : #operations }
BilinearForm >> symmetricPart [
	| two |
	two := self scalars one * 2.
	^ self class
		fromHalf: halfDomain
		matrix: matrix + matrix transposed / two
]

{ #category : #operations }
BilinearForm >> transposed [
	"The transposed of a bilinear form B(x,y) is B(y,x)."
	^ self class fromHalf: halfDomain matrix: matrix transposed
]

{ #category : #operations }
BilinearForm >> value: anArray [
	self assert: anArray size = 2.
	^ self value: anArray first value: anArray second
]

{ #category : #operations }
BilinearForm >> value: anObject value: anotherObject [
	| left right |
	left := halfDomain coordinatesOf: anObject.
	right := halfDomain coordinatesOf: anotherObject.
	^ left dot: (matrix * right)
]
