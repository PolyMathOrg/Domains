"
The general linear group GL(V) of automorphisms of an R-module V. The elements are invertible linear transformations from V to itself (see LinearMap, LinearGroup).

Examples (two equivalent ways to create GL(V):
	GeneralLinearGroup on: QQ ^ 3.
	(QQ ^ 3) automorphisms
"
Class {
	#name : #GeneralLinearGroup,
	#superclass : #LinearGroup,
	#category : #'Mathematics-Groups-Linear'
}

{ #category : #comparing }
GeneralLinearGroup >> >= anObject [
	(anObject isKindOf: LinearGroup) ifTrue: [^ space >= anObject space].
	^ super >= anObject
]

{ #category : #operations }
GeneralLinearGroup >> affine [
	^ GeneralAffineGroup on: space
]

{ #category : #accessing }
GeneralLinearGroup >> ambient [
	^ self
]

{ #category : #operations }
GeneralLinearGroup >> asMatrixGroup [
	^ GeneralLinearMatrixGroup new: space rank over: space scalars
]

{ #category : #random }
GeneralLinearGroup >> atRandom: aRandom [
	| answer |
	[(answer := self space endomorphisms atRandom: aRandom) isInvertible] whileFalse.
	^ answer
]

{ #category : #random }
GeneralLinearGroup >> atRandom: aRandom bits: bitSize [
	| answer |
	[(answer := self space endomorphisms atRandom: aRandom bits: bitSize) isInvertible] whileFalse.
	^ answer
]

{ #category : #operations }
GeneralLinearGroup >> center [
	^ ScalarGroup on: space
]

{ #category : #operations }
GeneralLinearGroup >> commutator [
	(space dimension = 2 and: [space scalars size = 2])
		ifFalse: [^ SpecialLinearGroup on: space].
	^ self propertyAt: #commutator ifAbsentPut: [super commutator]
]

{ #category : #testing }
GeneralLinearGroup >> contains: aLinearMap [
	"Answer true if the receiver contains the given element of its ambient."
	^ true
]

{ #category : #operations }
GeneralLinearGroup >> orthogonal [
	^ OrthogonalGroup on: space
]

{ #category : #printing }
GeneralLinearGroup >> shortName [
	^ 'GL'
]

{ #category : #accessing }
GeneralLinearGroup >> size [
	| q n |
	self space isInfinite ifTrue: [^ self space size]. "?"
	(self space scalars isField and: [self space scalars isFinite])
		ifFalse: [^ super size].
	q := self space scalars size.
	n := self space dimension.
	^ 'q ^ (n*(n-1)/2) * ((1 to: n) inject: 1 into: [:x :k| q^k - 1 * x])'
]

{ #category : #operations }
GeneralLinearGroup >> special [
	^ SpecialLinearGroup on: space
]
