"
Quadratic forms as homogeneous quadratic functions M->R from a finite-rank free R-module to R. Given a basis of M, they can be represented as homogeneous quadratic polynomials or as symmetric matrices that define symmetric bilinear forms MxM->R.
"
Class {
	#name : #QuadraticForm,
	#superclass : #Function,
	#instVars : [
		'coefficients'
	],
	#category : #'Mathematics-Modules-Lattices'
}

{ #category : #'instance creation' }
QuadraticForm class >> coefficients: aTuple [
	"Answer the quadratic form with the given coefficients (in lexicographical order)."

	^ self from: ((aTuple scalars)  raisedTo:  (aTuple size * 2)) sqrtFloor coefficients: aTuple
]

{ #category : #'instance creation' }
QuadraticForm class >> from: aModule coefficients: aTuple [
	"Answer the quadratic form associated with the given coefficients (in lexicographical order) in the distinguished basis of the given free module."
	^ self new domain: aModule; coefficients: aTuple
]

{ #category : #arithmetic }
QuadraticForm >> * anObject [
	^ self class from: self domain coefficients: self coefficients * anObject
]

{ #category : #arithmetic }
QuadraticForm >> + aQuadraticForm [
	self domain = aQuadraticForm domain ifFalse: [^ self error: 'domains don''t match'].
	self domain matrix = aQuadraticForm domain matrix ifFalse: [self notYetImplemented].
	^ self class
		from: self domain
		coefficients: self coefficients + aQuadraticForm coefficients
]

{ #category : #comparing }
QuadraticForm >> = aQuadraticForm [
	(aQuadraticForm isKindOf: QuadraticForm) ifFalse: [^ false].
	^ self coefficients = aQuadraticForm coefficients
]

{ #category : #operations }
QuadraticForm >> adjoint [
	"Answer the adjoint (integral) quadratic form associated to the receiver."
	| A |
	A := self hessian adjoint.
	self rank odd ifTrue: [A := A*2].
	^ self class from: self domain hessian: A
]

{ #category : #converting }
QuadraticForm >> asPolynomial [
	| n P |
	n := self rank.
	P := self domain coordinateRing.
	^ self value: (P tuple: n evaluating: [:i| P x: i])
]

{ #category : #converting }
QuadraticForm >> associatedBilinearForm [
	"Answer the associated symmetric bilinear form (assuming the characteristic is not 2).
	This is, via the polarization identity: B(v,w) := (Q(v+w) - Q(v-w)) / 4."
	^ BilinearForm fromHalf: self domain matrix: self gramian
]

{ #category : #accessing }
QuadraticForm >> at: aPoint [
	| i j n |
	i := aPoint x - 1.
	j := aPoint y - 1.
	i > j ifTrue: [i := j. j := aPoint x - 1].
	n := self rank.
	^ self coefficients at: i * n - (i-1*i//2) + j - i + 1
]

{ #category : #accessing }
QuadraticForm >> bitSize [
	^ self coefficients bitSize
]

{ #category : #accessing }
QuadraticForm >> codomain [
	^ self scalars
]

{ #category : #accessing }
QuadraticForm >> coefficients [
	"Answer the coefficients of the receiver in lexicographical order."
	^ coefficients
]

{ #category : #'accessing-private' }
QuadraticForm >> coefficients: aTuple [
	coefficients := aTuple
]

{ #category : #accessing }
QuadraticForm >> content [
	^ self coefficients content
]

{ #category : #accessing }
QuadraticForm >> determinant [
	"Answer the determinant of the Hessian matrix of the receiver. This is the determinant of the Gram matrix of twice the receiver."
	^ self hessian determinant
]

{ #category : #arithmetic }
QuadraticForm >> directSum: aQuadraticForm [
	"Answer the direct sum of the receiver and the argument."
	(aQuadraticForm isKindOf: QuadraticForm) ifFalse: [^ DomainError signal].
	^ self notYetImplemented
]

{ #category : #accessing }
QuadraticForm >> discriminant [
	"Note: this invariant is defined differently by different authors."
	self rank odd ifTrue: [^ self determinant / 2].
	(self rank // 2) odd ifTrue: [self determinant negated].
	^ self determinant
]

{ #category : #accessing }
QuadraticForm >> gramian [
	"Answer the Gramian matrix G for the receiver Q.
	This is a matrix G such that Q(x) = x^t * G * x."
	^ self hessian collect: [:each| each / 2] "assuming we can divide by 2"
]

{ #category : #comparing }
QuadraticForm >> hash [
	^ self coefficients hash
]

{ #category : #accessing }
QuadraticForm >> hessian [
	"Answer the Hessian matrix H for the receiver Q.
	This is a matrix H such that Q(x) = x^t * H * x / 2."
	^ self scalars matrix: self domain rank evaluating: [:i :j| i = j ifTrue: [(self at: i@j)*2] ifFalse: [self at: i@j]]
]

{ #category : #testing }
QuadraticForm >> isDiagonal [
	"Answer true if the receiver is in diagonal form."
	^ self hessian isDiagonal
]

{ #category : #testing }
QuadraticForm >> isPrimitive [
	^ self content = self scalars one
]

{ #category : #testing }
QuadraticForm >> isRegular [
	^ self associatedBilinearForm isNonDegenerate
]

{ #category : #arithmetic }
QuadraticForm >> negated [
	^ self class from: self domain coefficients: self coefficients negated
]

{ #category : #operations }
QuadraticForm >> primitive [
	^ self class from: self domain coefficients: self coefficients primitive
]

{ #category : #printing }
QuadraticForm >> printOn: aStream [
	aStream print: self asPolynomial
]

{ #category : #accessing }
QuadraticForm >> rank [
	^ self domain rank
]

{ #category : #operations }
QuadraticForm >> reciprocal [
	^ self adjoint primitive * self content
]

{ #category : #accessing }
QuadraticForm >> scalars [
	^ self domain scalars
]

{ #category : #operations }
QuadraticForm >> value: aVector [
	| v n answer |
	v := self domain coordinatesOf: aVector.
	n := self rank.
	answer := self scalars zero.
	1 to: n do: [:i|
		| vi |
		vi := v at: i.
		i to: n do: [:j|
			answer := (self at: i@j) * vi * (v at: j) + answer]].
	^ answer
]

{ #category : #comparing }
QuadraticForm >> ~ aQuadraticForm [
	"Answer true if the receiver and the argument are integrally equivalent."
	^ self hessian ~ aQuadraticForm hessian
]
