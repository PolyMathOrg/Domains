"
The general linear (matrix) group GL(n,R) of nxn invertible matrices with coefficients in the ring R, acting on the R-module of n-tuples R^n.

Example:
	GeneralLinearMatrixGroup on: QQ ^ 3

"
Class {
	#name : #GeneralLinearMatrixGroup,
	#superclass : #MatrixGroup,
	#category : #'Mathematics-Groups-Matrix'
}

{ #category : #comparing }
GeneralLinearMatrixGroup >> >= anObject [
	(anObject isKindOf: MatrixGroup) ifFalse: [^ super >= anObject].
	^ self scalars >= anObject scalars and: [self degree = anObject degree]
]

{ #category : #accessing }
GeneralLinearMatrixGroup >> ambient [
	^ self
]

{ #category : #random }
GeneralLinearMatrixGroup >> atRandom: aRandom [
	| matrices answer |
	matrices := 'self scalars ^ (self degree @ self degree)'.
	[(answer := matrices atRandom: aRandom) isSingular] whileTrue.
	^ answer
]

{ #category : #random }
GeneralLinearMatrixGroup >> atRandom: aRandom bits: bitSize [
	| matrices answer |
	matrices := 'self scalars ^ (self degree @ self degree)'.
	[(answer := matrices atRandom: aRandom bits: bitSize) isSingular] whileTrue.
	^ answer
]

{ #category : #operations }
GeneralLinearMatrixGroup >> center [
	^ ScalarMatrixGroup new: self degree over: self scalars
]

{ #category : #operations }
GeneralLinearMatrixGroup >> commutator [
	(self degree = 2 and: [self scalars size = 2])
		ifFalse: [^ SpecialLinearMatrixGroup new: self degree over: self scalars].
	^ self propertyAt: #commutator
]

{ #category : #testing }
GeneralLinearMatrixGroup >> contains: aMatrix [
	"Answer true if the receiver contains the given element of its ambient."
	^ true
]

{ #category : #operations }
GeneralLinearMatrixGroup >> orthogonal [
	^ OrthogonalMatrixGroup new: self degree over: self scalars
]

{ #category : #printing }
GeneralLinearMatrixGroup >> shortName [
	^ 'GL'
]

{ #category : #accessing }
GeneralLinearMatrixGroup >> size [
	| q n |
	(self space scalars isField and: [self space scalars isFinite])
		ifFalse: [^ super size].
	q := self space scalars size.
	n := self space dimension .
	^ 'q ^ (n*(n-1)/2) * ((1 to: n) inject: 1 into: [:x :k| q^k - 1 * x])'
]

{ #category : #operations }
GeneralLinearMatrixGroup >> special [
	"Answer the special linear group SL(n) which is a subgroup of the receiver."
	^ SpecialLinearMatrixGroup new: self degree over: self scalars
]

{ #category : #converting }
GeneralLinearMatrixGroup >> toAlgebraicVariety [
	| n P det V |
	self scalars isField ifFalse: [self notYetImplemented].
	n := self degree.
	P := self scalars polynomialsIn: n squared + 1.
	det := (P matrix: n coefficients: P generators) determinant.
	V := 'P * (det * (P x: n squared + 1) - P one) :: variety'.
	^ Function
		from: self to: V
		evaluating: [:M| V ! (M asTuple, M determinant reciprocal)]
		inverseEvaluating: [:p| p scalars matrix: n coefficients: p coordinates]
]
