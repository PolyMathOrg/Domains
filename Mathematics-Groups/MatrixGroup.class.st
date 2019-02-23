"
Groups of nxn (non-singular) matrices acting on the R-module of n-tuples R^n. They are subgroups of the general linear matrix group GL(n,R) of nxn invertible matrices with coefficients in the commutative ring R.

These groups act naturally on the module R^n of n-tuples by the action A^v |-> A*v. (Or the corresponding left action).
"
Class {
	#name : #MatrixGroup,
	#superclass : #Group,
	#category : #'Mathematics-Groups-Matrix'
}

{ #category : #examples }
MatrixGroup class >> C3 [
	"Cyclic matrix group of order 3."
	^ self generators: {Matrix rows: {(0,1) % 5. (-1,-1) % 5}}
]

{ #category : #examples }
MatrixGroup class >> C4 [
	"Cyclic matrix group of order 4."
	^ self generators: {Matrix rows: {(0,-1) % 7. (1,0) % 7}}
]

{ #category : #'instance creation' }
MatrixGroup class >> generators: aCollection [
	^ self new: aCollection anyOne height over: aCollection anyOne scalars generators: aCollection
]

{ #category : #examples }
MatrixGroup class >> klein [
	"The Klein four-group (or Vierergruppe) as a matrix group."
	| a b |
	a := Matrix rows: {(1,0). (0, -1)}.
	b := a negated.
	^ self generators: {a. b}
]

{ #category : #'instance creation' }
MatrixGroup class >> new: anInteger over: aRing [
	^ self new scalars: aRing; degree: anInteger
]

{ #category : #'instance creation' }
MatrixGroup class >> new: anInteger over: aRing generators: aCollection [
	^ self new scalars: aRing; degree: anInteger; generators: aCollection
]

{ #category : #elements }
MatrixGroup >> ! anObject [
	(anObject isKindOf: SequenceableCollection)
		ifTrue: [^ self scalars matrix: self degree coefficients: (anObject collect: [:each| self scalars ! each])].
	^ super ! anObject
]

{ #category : #accessing }
MatrixGroup >> action [
	"Answer the natural action that sends (M, x) to M*x."
	^ self rightAction
]

{ #category : #accessing }
MatrixGroup >> ambient [
	"Answer the ambient group."
	^ GeneralLinearMatrixGroup new: self degree over: self scalars
]

{ #category : #private }
MatrixGroup >> computeSize [
	"Schreier-Sims algorithm."
	| G answer |
	G := self.
	answer := 1.
	self space do: [:b| | tree |
		G isTrivial ifTrue: [^ answer].
		tree := SchreierTree root: b generators: G generators action: G action.
		answer := answer * tree orbit size.
		G := tree stabilizer].
	self error: 'what?'.
	^ answer
]

{ #category : #copying }
MatrixGroup >> copyEmpty [
	^ super copyEmpty scalars: self scalars; degree: self degree
]

{ #category : #accessing }
MatrixGroup >> degree [
	^ self propertyAt: #degree
]

{ #category : #'accessing-private' }
MatrixGroup >> degree: anInteger [
	self propertyAt: #degree put: anInteger
]

{ #category : #enumerating }
MatrixGroup >> do: aBlock [
	self flag: #fix.
	((self hasProperty: #elements) or: [self hasProperty: #generators])
		ifTrue: [^ super do: aBlock].
	'self scalars ^ (self degree @ self degree) do: [:each| (each isSingular not and: [self contains: each]) ifTrue: [aBlock value: each]]'
]

{ #category : #invariants }
MatrixGroup >> hilbertSeries [
	"Answer the Hilbert series of the invariant ring of the receiver.
	This is the sum of dim(S_d ^G z^d for d>=0 (by Molien's formula, 1897), i.e. it counts the homogeneous polynomials of a given degree d that are invariants for the group."
	| order |
	order := self size.
	self scalars characteristic | order ifTrue: [self error: 'group order divisible by characteristic'].
	^ (self elements sum: [:g| g characteristicPolynomial reciprocal]) / order
]

{ #category : #accessing }
MatrixGroup >> identity [
	^ self scalars matrix: self degree @ self degree scalar: self scalars one
]

{ #category : #testing }
MatrixGroup >> includes: aMatrix [
	^ (aMatrix isKindOf: Matrix) and: [aMatrix isSquare and: [aMatrix width = self degree and: [aMatrix scalars <= self scalars and: [aMatrix determinant isZero not and: [self contains: aMatrix]]]]]
]

{ #category : #testing }
MatrixGroup >> isFinite [
	^ self scalars isFinite or: [super isFinite]
]

{ #category : #accessing }
MatrixGroup >> leftAction [
	"Answer the natural action that sends (A, x) to x*A."
	^ GroupAction from: (self, self space) to: self space evaluatingWithArguments: [:A :x| x * A]
]

{ #category : #converting }
MatrixGroup >> on: aFreeModule [
	^ LinearTransformationsGroup on: aFreeModule matrices: self
]

{ #category : #invariants }
MatrixGroup >> polynomialAction [
	"Answer the action of the receiver on the polynomial ring K[x1...xn]."
	| R X |
	R := self space coordinateRing.
	X := R tuple: R rank evaluating: [:i| R x: i].
	^ GroupAction from: (self, R) to: R evaluatingWithArguments: [:A :f| f value: (A over: R) * X]
]

{ #category : #printing }
MatrixGroup >> printOn: aStream [
	self shortName isNil ifTrue: [^ super printOn: aStream].
	aStream isText
		ifTrue:
			[aStream nextPutAll: self shortName; nextPutAll: self degree printString sub; nextPut: $(; print: self scalars; nextPut: $)]
		ifFalse:
			[aStream nextPutAll: self shortName; nextPut: $(; print: self scalars; nextPut: $,; print: self degree; nextPut: $)]
]

{ #category : #invariants }
MatrixGroup >> reynolds [
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
MatrixGroup >> rightAction [
	"Answer the natural action that sends (A, x) to A*x."
	^ GroupAction from: (self, self space) to: self space evaluatingWithArguments: [:A :x| A * x]
]

{ #category : #accessing }
MatrixGroup >> scalars [
	^ self propertyAt: #scalars
]

{ #category : #'accessing-private' }
MatrixGroup >> scalars: aRing [
	self propertyAt: #scalars put: aRing
]

{ #category : #printing }
MatrixGroup >> shortName [
	^ nil
]

{ #category : #accessing }
MatrixGroup >> space [
	^ 'self scalars ^ self degree'
]

{ #category : #private }
MatrixGroup >> species [
	^ MatrixGroup
]
