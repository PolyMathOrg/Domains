"
Groups of linear transformations acting on an R-module V. They are subgroups of the general linear group GL(V).

These groups act naturally on the domain R-module by the action g^v |-> g(v). They also act by composition on the R[V], the polynomial ring on V (see >>polynomialAction).
"
Class {
	#name : #LinearGroup,
	#superclass : #TransformationGroup,
	#instVars : [
		'space'
	],
	#category : #'Mathematics-Groups-Linear'
}

{ #category : #'instance creation' }
LinearGroup class >> on: aVectorSpace [
	^ self new space: aVectorSpace
]

{ #category : #'instance creation' }
LinearGroup class >> on: aVectorSpace generators: aCollection [
	^ (self on: aVectorSpace) generators: aCollection
]

{ #category : #accessing }
LinearGroup >> action [
	"Answer the natural action that sends (f, x) to f(x)."
	^ GroupAction from: (self, space) to: space evaluatingWithArguments: [:f :x| f value: x]
]

{ #category : #operations }
LinearGroup >> affine [
	self flag: #fix.
	^ AffineGroup linear: self
]

{ #category : #accessing }
LinearGroup >> ambient [
	"Answer the ambient group."
	^ space automorphisms "the general linear group GL(V)"
]

{ #category : #operations }
LinearGroup >> asMatrixGroup [
	self flag: #fix. "the matrix depends on the basis"
	^ (MatrixGroup on: space coordinates) generators: (self generators collect: [:g| g matrix])
]

{ #category : #copying }
LinearGroup >> copyEmpty [
	^ super copyEmpty space: space
]

{ #category : #accessing }
LinearGroup >> degree [
	^ space dimension
]

{ #category : #enumerating }
LinearGroup >> do: aBlock [
	self flag: #fix.
	^ super do: aBlock
"	space endomorphisms do: [:each| (self includes: each) ifTrue: [aBlock value: each]]"
]

{ #category : #invariants }
LinearGroup >> hilbertSeries [
	"Answer the Hilbert series of the invariant ring of the receiver.
	This is the sum of dim(S_d ^G z^d for d>=0 (by Molien's formula, 1897), i.e. it counts the homogeneous polynomials of a given degree d that are invariants for the group."
	| order |
	order := self size.
	self scalars characteristic | order ifTrue: [self error: 'group order divisible by characteristic'].
	^ (self elements sum: [:g| g characteristicPolynomial reciprocal]) / order
]

{ #category : #accessing }
LinearGroup >> identity [
	^ space id
]

{ #category : #testing }
LinearGroup >> includes: aLinearMap [
	^ (space endomorphisms includes: aLinearMap) and: [aLinearMap determinant isZero not and: [self contains: aLinearMap]]
]

{ #category : #testing }
LinearGroup >> isFinite [
	^ self scalars isFinite or: [super isFinite]
]

{ #category : #invariants }
LinearGroup >> polynomialAction [
	"Answer the action of the receiver on K[V], the coordinate ring of the associated space V."
	| R |
	R := self space coordinateRing.
	^ GroupAction from: (self, R) to: R evaluatingWithArguments: [:f :g| g î f]
]

{ #category : #printing }
LinearGroup >> printOn: aStream [
	self class = LinearGroup ifTrue: [^ super printOn: aStream].
	aStream nextPutAll: self shortName; nextPut: $(; print: space; nextPut: $)
]

{ #category : #invariants }
LinearGroup >> reynolds [
	"Answer the Reynolds operator. Properties:
	- K-linear map S -> S^G;
	- restricts to the identity on S^G;
	- it's an S^G-module homomorphisms: R(p*q) = p*R(q) for all invariants p in S^G."
	| order action |
	order := self size.
	action := self polynomialAction.
	^ self space coordinateRing to: self invariantsRing evaluating: [:p| (self sum: [:g| action value: {g. p}]) / order]
]

{ #category : #accessing }
LinearGroup >> scalars [
	^ space scalars
]

{ #category : #printing }
LinearGroup >> shortName [
	^ self class name
]

{ #category : #accessing }
LinearGroup >> space [
	^ space
]

{ #category : #'accessing-private' }
LinearGroup >> space: aVectorSpace [
	space := aVectorSpace
]

{ #category : #private }
LinearGroup >> species [
	^ LinearGroup
]
