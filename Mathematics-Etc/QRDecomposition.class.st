"
My instances are QR factorizations of a given real or complex matrix A, such that A = Q*R where Q is unitary (orthogonal) and R is upper triangular. Morover, if A is nonsingular, the diagonal of R may be taken to be positive, in which case the factorization is unique.
"
Class {
	#name : #QRDecomposition,
	#superclass : #Object,
	#instVars : [
		'matrix',
		'Q',
		'R'
	],
	#category : #'Mathematics-Etc'
}

{ #category : #'as yet unclassified' }
QRDecomposition >> Q [
	Q isNil ifTrue: [self run].
	^ Q
]

{ #category : #'as yet unclassified' }
QRDecomposition >> R [
	R isNil ifTrue: [self run].
	^ R
]

{ #category : #'as yet unclassified' }
QRDecomposition >> matrix: aMatrix [
	matrix := aMatrix
]

{ #category : #'as yet unclassified' }
QRDecomposition >> run [
	| K n basis ortho |
	K := matrix scalars "algebraicClosure".
	n := matrix height.
	self flag: #fix. "we're assuming the columns are independent"
	basis := 'LinearBasis on: K ^ n elements: matrix columns'.
	ortho := basis orthonormalized.
	Q := Matrix columns: ortho.
"	zero := K zero.
	R := matrix species evaluating: [:i :j| i > j ifTrue: [zero] ifFalse: [(basis at: i) dotProduct: (ortho at: j)]]"
	R := Q transposed * matrix
]

{ #category : #'as yet unclassified' }
QRDecomposition >> verify [
	^ matrix = (self Q * self R)
]
