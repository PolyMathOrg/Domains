"
Finite and ordered bases of free modules. They are internally represented by a matrix whose rows are the ambient distinguished coordinates of the basis elements.
"
Class {
	#name : #LinearBasis,
	#superclass : #ArrayedCollection,
	#instVars : [
		'ambient',
		'matrix'
	],
	#category : #'Mathematics-Modules-Free'
}

{ #category : #examples }
LinearBasis class >> example [
	"A basis for the vector space of 3-tuples with rational coefficients."
	| V |
	V := QQ raisedTo: 3.
	^ LinearBasis on: V elements: {(1, 2, 3). (3, 2, 3). (2, 0, 0)}
]

{ #category : #'instance creation' }
LinearBasis class >> on: aFreeModule elements: aCollection [
	^ self on: aFreeModule matrix: (Matrix rows: (aCollection collect: [:each| aFreeModule coordinatesOf: each]))
]

{ #category : #'instance creation' }
LinearBasis class >> on: aFreeModule matrix: aMatrix [
	^ self basicNew ambient: aFreeModule; matrix: aMatrix
]

{ #category : #operations }
LinearBasis >> + aLinearBasis [
	"Answer a basis for the sum of the modules generated by the receiver and the argument."
	^ self class on: ambient matrix: (matrix, aLinearBasis matrix) transposed imageMatrix
]

{ #category : #comparing }
LinearBasis >> = aLinearBasis [
	self == aLinearBasis ifTrue: [^ true].
	ambient == aLinearBasis ambient ifTrue: [matrix = aLinearBasis matrix].
	^ super = aLinearBasis
]

{ #category : #accessing }
LinearBasis >> ambient [
	^ ambient
]

{ #category : #'accessing-private' }
LinearBasis >> ambient: aFreeModule [
	ambient := aFreeModule
]

{ #category : #operations }
LinearBasis >> apply: aLinearMap [
	| answer vector |
	answer := self class on: (aLinearMap isBlock ifTrue: [ambient] ifFalse: [aLinearMap codomain]).
	self do: [:each|
		(answer generates: (vector := aLinearMap value: each))
			ifFalse: [answer add: vector]].
	^ answer
]

{ #category : #accessing }
LinearBasis >> at: anInteger [
	^ ambient elementAt: (matrix rowAt: anInteger)
]

{ #category : #operations }
LinearBasis >> changeTo: aLinearBasis [
	"Answer the matrix for changing from the receiver to aLinearBasis."
	^ (Matrix rows: (self collect: [:each| aLinearBasis coordinatesOf: each])) transposed
]

{ #category : #coordinates }
LinearBasis >> coordinateMap [
	^ LinearMap from: self coordinateSpace to: ambient matrix: matrix transposed
]

{ #category : #coordinates }
LinearBasis >> coordinateSpace [
	^ (ambient scalars) raisedTo:( self size)
]

{ #category : #coordinates }
LinearBasis >> coordinatesOf: anElement [
	"Answer the coordinates of anElement when expressed as a linear combination of the vectors of the receiver. Answer nil if anElement is independent from the receiver."
	anElement isZero ifTrue: [^ ambient scalars zeroTuple: self size "self coordinateSpace zero"].
	self isEmpty ifTrue: [^ nil].
"	1 to: self size do: [:i| (self at: i) = anElement ifTrue: [^ self coordinateSpace e: i]]."
	^ self matrix transposed \ ((ambient coordinatesOf: anElement) ifNil: [^ nil])
"alternative 1:
	answer := self matrix leftInverse * (ambient coordinatesOf: anElement).
	^ answer isZero ifFalse: [answer]"
"alternative 2:
	m := self matrix rowAugmented: (ambient coordinatesOf: anElement).
	reducer := m transposed reducer.
	coords := reducer reduced lastColumn.
	^ reducer rank > self size
		ifFalse:
			[answer := self coordinateSpace zero copy.
			reducer pivots do: [:each| answer at: each x put: (coords at: each y)].
			answer]"
]

{ #category : #copying }
LinearBasis >> copy [
	^ self class on: ambient matrix: matrix copy
]

{ #category : #copying }
LinearBasis >> copyFrom: startIndex to: endIndex [
	^ self class on: ambient matrix: (Matrix rows: (matrix rows copyFrom: startIndex to: endIndex))
]

{ #category : #operations }
LinearBasis >> directSum: aLinearBasis [
	"Answer the direct sum of the receiver and the argument."
	^ self class on: (ambient directSum: (aLinearBasis ambient)) matrix: (matrix directSum: (aLinearBasis matrix))
]

{ #category : #operations }
LinearBasis >> dot: aLinearBasis [
	"Answer a basis for the intersection of the modules generated by the receiver and the argument."
	| M N |
	M := matrix.
	N := (M transposed | aLinearBasis matrix transposed) kernelMatrix.
	N isEmpty ifTrue: [^ self class on: ambient matrix: (Matrix rows: #())].
	N := N copyFrom: 1@1 to: N height @ M height.
	^ self class on: self ambient matrix: N * M
]

{ #category : #operations }
LinearBasis >> dual [
	ambient basis = self ifTrue: [^ ambient dual basis].
	^ self class on: ambient dual matrix: (Matrix rows: (self extended matrix transposed inverse rows first: self size))
]

{ #category : #coordinates }
LinearBasis >> elementAt: aTuple [ 
	"Answer the vector with coordinates aTuple when expressed as a linear combination of the receiver."
	| answer |
"	self assert: aTuple size = self size."
	answer := self ambient zero.
	1 to: aTuple size do: [:each|
		answer := (self at: each) * (aTuple at: each) + answer].
	^ answer
]

{ #category : #operations }
LinearBasis >> extended [
	"Answer a basis spanning to all the ambient space, adding generating vectors if needed."
	self isFullRank ifTrue: [^ self].
	^ self class on: ambient matrix: (matrix, (ambient scalars identityMatrix: ambient rank)) transposed imageMatrix
]

{ #category : #testing }
LinearBasis >> generates: anElement [
	"Answer true if the argument is dependent to the receiver.
	Assume it is an element of the ambient module."
	self isEmpty ifTrue: [^ anElement isZero].
	self isFullRank ifTrue: [^ true].
	^ (self coordinatesOf: anElement) notNil
"no need to do extra work here, can optimize"
	"^ (self matrix | (ambient coordinatesOf: anElement)) rank = self size"
]

{ #category : #operations }
LinearBasis >> gramian [
	"Answer the Gramian of the receiver, or Gram matrix.
	If M is the generator matrix of the receiver (>>matrix), then the Gramian is M * M transposed."
	| f |
	f := ambient innerProduct.
	^ ambient scalars
		matrix: self size
		evaluating:
			[:i :j| f value: {(self at: i). (self at: j)}]
]

{ #category : #testing }
LinearBasis >> isEmpty [
	^ matrix isEmpty
]

{ #category : #testing }
LinearBasis >> isFullRank [
	^ self size = self ambient rank
]

{ #category : #testing }
LinearBasis >> isOrthogonal [
	self do: [:v|
		self do: [:w|
			(v ~~ w and: [(ambient innerProduct value: {v.w}) isZero not])
				ifTrue: [^ false]]].
	^ true
]

{ #category : #testing }
LinearBasis >> isOrthonormal [
	self isOrthogonal ifFalse: [^ false].
	self do: [:v| (ambient innerProduct value: {v.v}) = ambient scalars one ifFalse: [^ false]].
	^ true
]

{ #category : #accessing }
LinearBasis >> matrix [
	"Answer the generator matrix M, i.e. the matrix whose rows are the coordinates of the vectors of the receiver in the ambient distinguished basis."
	^ matrix
]

{ #category : #'accessing-private' }
LinearBasis >> matrix: aMatrix [
	matrix := aMatrix
]

{ #category : #operations }
LinearBasis >> orthogonalized [
	"Answer the receiver orthogonalized by the Gram-Schmidt process."
	^ (GramSchmidt basis: self) orthogonalBasis
]

{ #category : #operations }
LinearBasis >> orthonormalized [
	"Answer the receiver orthonormalized by the Gram-Schmidt process."
	^ (GramSchmidt basis: self) orthonormalBasis
]

{ #category : #operations }
LinearBasis >> perp [
	"Answer a bssis of the orthogonal complement of the subspace spanned by the receiver."
	self isEmpty ifTrue: [^ ambient basis].
	"if we're in a vector space over the reals or complex numbers, we can get an orthogonal basis"
	((ambient scalars isKindOf: RealField) or: [ambient scalars isKindOf: ComplexField])
		ifTrue: [^ self extended orthogonalized copyFrom: self size + 1 to: self ambient rank].
	"otherwise we use this, but it assumes the associated bilinear form is just the dot product:"
	^ self class on: ambient matrix: matrix kernelMatrix
]

{ #category : #printing }
LinearBasis >> printOn: aStream [
	aStream nextPut: ${.
	self do: [:each| aStream print: each] separatedBy: [aStream nextPutAll: '; '].
	aStream nextPut: $}
]

{ #category : #accessing }
LinearBasis >> scalars [
	^ ambient scalars
]

{ #category : #enumerating }
LinearBasis >> select: aBlock [ 
	"Evaluate aBlock with each of the receiver's elements as the argument. 
	Collect into a new collection like the receiver, only those elements for 
	which aBlock evaluates to true. Answer the new collection."

	^ self class on: ambient matrix: (Matrix rows: (((1 to: self size) select: [:i| aBlock value: (self at: i)]) collect: [:i| matrix rowAt: i]))
]

{ #category : #accessing }
LinearBasis >> size [
	^ matrix height
]

{ #category : #accessing }
LinearBasis >> span [
	"Answer the submodule spanned by the elements of the receiver."
	self error: 'deprecated'.
	self isFullRank ifTrue: [^ ambient].
	^ ambient span: matrix
]

{ #category : #private }
LinearBasis >> species [
	^ Array
]

{ #category : #coordinates }
LinearBasis >> vectorAt: aTuple [ 
	"Answer the vector with coordinates aTuple when expressed as a linear combination of the receiver."
	^ self elementAt: aTuple
]
