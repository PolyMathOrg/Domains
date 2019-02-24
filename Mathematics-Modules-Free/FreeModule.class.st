"
Finite-rank free R-modules, i.e. R-modules with a basis. They are isomorphic to R^n.

Most functionality is implemented for the cases where R is a field (vector spaces, relying on gaussian elimination), or for R a PID such as Z or Q[x] (relying on the Hermite normal form or computing in the field of fractions).

Free modules are embedded in an ambient module, and are represented by a basis matrix (FreeModule>>matrix) with respect to the ambient standard basis.

For R a PID, free R-modules are always embedded in an ambient K-vector space, where K is the field of fractions of R.

See also LinearMap.
"
Class {
	#name : #FreeModule,
	#superclass : #Module,
	#category : #'Mathematics-Modules-Free'
}

{ #category : #elements }
FreeModule >> ! anObject [
	(anObject isSequenceable and: [anObject size = self rank])
		ifTrue: [^ self elementAt: anObject].
	^ super ! anObject
]

{ #category : #operations }
FreeModule >> * aNumber [
	"Answer the receiver scaled by aNumber."
	aNumber isZero
		ifTrue: [^ self null].
	self isVectorSpace
		ifTrue: [^ self].
	(aNumber = self scalars one or: [aNumber = self scalars one negated])
		ifTrue: [^ self].
	self scalars isPID "this means the receiver is a lattice embedded in a vector space over the fraction field"
		ifTrue: [^ self ambient span: (self generators collect: [:each| each * aNumber]) over: self scalars].
	^ DomainError signal
]

{ #category : #operations }
FreeModule >> + anObject [
	(self ambient includes: anObject) ifTrue: [^ AffineSubspace representative: anObject direction: self].
	self isTrivial ifTrue: [^ anObject].
	anObject isTrivial ifTrue: [^ self].
	(self scalars isPID and: [self scalars = anObject scalars and: [self ambient = anObject ambient]])
		ifFalse: [^ DomainError signal].
	^ self ambient span: self matrix, anObject matrix over: self scalars
]

{ #category : #operations }
FreeModule >> / anObject [
	"Answer the quotient of the receiver by the submodule anObject,
	i.e. the module obtained by 'collapsing' the submodule to zero.
	Alternatively, if anObject is an scalar, scale down the receiver by it."
	(self ambient scalars includes: anObject) ifTrue: [^ self * anObject reciprocal].
	(self includes: anObject) ifTrue: [^ self / (self ambient span: {anObject} over: self scalars)].
	anObject isCollection ifTrue: [^ self / (self ambient span: anObject over: self scalars)].
	anObject isFreeModule ifFalse: [^ super / anObject].
	(self scalars isPID and: [self ambient = anObject ambient])
		ifFalse: [^ DomainError signal].
	self isVectorSpace ifTrue:
		[| Q |
		Q := QuotientSpace mod: anObject.
		self isEmbedded ifFalse: [^ Q].
		^ Q span: (self basis collect: [:each| Q project: each])].
	^ QuotientModule base: self relations: anObject
]

{ #category : #operations }
FreeModule >> /\ aModule [
	"Meet."
	^ self ï aModule
]

{ #category : #comparing }
FreeModule >> < aModule [
	"Answer true if the receiver is strictly included in the argument, i.e. it's a proper submodule of the argument."
	^ self rank < aModule rank and: [self <= aModule]
]

{ #category : #comparing }
FreeModule >> <= aModule [
	"Answer true if the receiver is included in the argument, i.e. it's a submodule of the argument."
	self == aModule ifTrue: [^ true].
	self rank <= aModule rank ifFalse: [^ false].
	self generators do: [:each| (aModule includes: each) ifFalse: [^ false]].
	^ true
]

{ #category : #comparing }
FreeModule >> = anObject [
	self == anObject ifTrue: [^ true].
	(anObject isKindOf: FreeModule) ifFalse: [^ false].
	self scalars = anObject scalars ifFalse: [^ false].
	self rank = anObject rank ifFalse: [^ false].
	self flag: #fix.
	^ self generators allSatisfy: [:each| anObject includes: each] "or better test echelonized matrices are equal"
]

{ #category : #operations }
FreeModule >> \/ aModule [
	"Join."
	^ self + aModule
]

{ #category : #accessing }
FreeModule >> ambient [
	^ self propertyAt: #ambient ifAbsentPut: [self scalars isField ifTrue: [self] ifFalse: [self scalars isIntegralDomain ifTrue: [self over: self scalars fractions] ifFalse: [self]]]
]

{ #category : #operations }
FreeModule >> annihilator [
	"Answer the space of all linear forms that are 0 at all vectors in the receiver."
	self isTrivial ifTrue: [^ self ambient dual].
	self isFullRank ifTrue: [^ self ambient dual null].
	^ self ambient dual span: (self matrix extended transposed inverse copyFromRow: self rank + 1 to: self degree)
]

{ #category : #morphisms }
FreeModule >> apply: aLinearMap [
	"Answer the receiver transformed by aLinearMap."
	^ (aLinearMap isBlock ifTrue: [self ambient] ifFalse: [aLinearMap codomain ambient]) span: (self basis collect: [:each| aLinearMap value: each]) over: self scalars
]

{ #category : #converting }
FreeModule >> asAbelianGroup [
	^ (self as: FreeAbelianGroup) generators: self generators
]

{ #category : #converting }
FreeModule >> asAlgebraicVariety [
	| R |
	R := self scalars polynomialsIn: self ambient rank.
	^ (R * (self annihilator basis asArray collect: [:each| R ! each])) variety
]

{ #category : #converting }
FreeModule >> asLattice [
	| V |
	self scalars fractions = self scalars ifTrue: [^ DomainError signal].
	V := self over: self scalars fractions.
	^ V ambient span: V basis over: self scalars
]

{ #category : #converting }
FreeModule >> asVectorSpace [
	self scalars isField ifTrue: [^ self].
	self scalars isIntegralDomain ifTrue: [^ self over: self scalars fractions].
	^ DomainError signal: 'not over an integral domain'
]

{ #category : #random }
FreeModule >> atRandom: aRandom [
	^ self elementAt: (self coordinates atRandom: aRandom)
]

{ #category : #random }
FreeModule >> atRandom: aRandom bits: bitSize [
	self rank = 0 ifTrue: [^ self zero].
	^ self elementAt: (self coordinates atRandom: aRandom bits: bitSize)
]

{ #category : #morphisms }
FreeModule >> automorphisms [
	^ GeneralLinearGroup on: self
]

{ #category : #basis }
FreeModule >> basis [
	^ self propertyAt: #basis ifAbsentPut: [self matrix rows collect: [:each| self ambient elementAt: each]]
]

{ #category : #operations }
FreeModule >> catProd: aModule [
	"◊"

	"Answer the categorical product, i.e. direct sum of the receiver and the argument."

	^ (aModule isFreeModule and: [ aModule scalars = self scalars ])
		ifTrue: [ self directSum: aModule ]
		ifFalse: [ 'super ◊ aModule' ]
]

{ #category : #basis }
FreeModule >> codimension [
	^ self ambient dimension - self dimension
]

{ #category : #testing }
FreeModule >> contains: anElement [
	self isTrivial ifTrue: [^ anElement isZero].
	self isEmbedded ifFalse: [^ true].
	^ (self coordinatesOf: anElement) notNil
]

{ #category : #basis }
FreeModule >> coordinateMap [
	"Answer the isomorphism between the receiver and its coordinates."
	
	^ self to: self coordinates matrix: self matrix
]

{ #category : #accessing }
FreeModule >> coordinateNames [
	^ self propertyAt: #coordinateNames ifAbsent: [  ]
]

{ #category : #basis }
FreeModule >> coordinateRing [
	"The coordinate ring of a R-module of rank n (or K-vector space of dimension n) is the polynomial ring R[x1..xn] (or K[x1..xn])."

	^ self
		propertyAt: #coordinateRing
		ifAbsentPut: [ self scalars
				polynomialsIn: (self coordinateNames ifNil: [ self rank ]) ]
]

{ #category : #basis }
FreeModule >> coordinates [
	"Answer the coordinate space (or module) of the receiver."

	^ (self scalars) raisedTo: (self rank)
]

{ #category : #basis }
FreeModule >> coordinatesOf: anElement [
	"Answer the coordinates of anElement when expressed as a linear combination of the elements of the distinguished basis of the receiver. Answer nil if anElement is not in the receiver."
	anElement isZero ifTrue: [^ self coordinates zero].
	self isTrivial ifTrue: [^ nil].
	^ self matrix transposed \ (self ambient coordinatesOf: anElement)
"
	^ self matrix transposed \ (self ambient coordinatesOf: anElement)
alternative 1:
	answer := self matrix leftInverse * (ambient coordinatesOf: anElement).
	^ answer isZero ifFalse: [answer]"
"alternative 2:
	m := self matrix rowAugmented: (ambient coordinatesOf: anElement).
	reducer := m transposed reducer.
	coords := reducer reduced lastColumn.
	^ reducer rank > self size
		ifFalse:
			[answer := self coordinates zero copy.
			reducer pivots do: [:each| answer at: each x put: (coords at: each y)].
			answer]"
]

{ #category : #basis }
FreeModule >> corank [
	self isVectorSpace
		ifTrue: [ ^ self ambient rank - self rank ].
	^ (self ambient / self) rank
]

{ #category : #accessing }
FreeModule >> degree [
	"Answer the degree of this free module.
	This is the rank of the ambient module."
	^ self ambient rank
]

{ #category : #accessing }
FreeModule >> denominator [
	^ self matrix denominator
]

{ #category : #basis }
FreeModule >> dimension [
	"Custom notation for vector spaces."
	^ self rank
]

{ #category : #operations }
FreeModule >> directSum: aModule [
	"ê"

	aModule isFreeModule
		ifFalse: [ ^ super directSum: aModule ].
	"Answer the direct sum of the receiver and the argument."
	self scalars = aModule scalars
		ifFalse: [ DomainError signal: 'scalars don''t match' ].
	(self isEmbedded or: [ aModule isEmbedded ])
		ifTrue:
			[ ^ (self ambient compose: (aModule ambient)) span: (self matrix compose: aModule matrix) ].
	^ FreeDirectSumModule
		components:
			{self.
			aModule}
]

{ #category : #basis }
FreeModule >> discriminant [
	^ self gramian determinant
	
"sage defines it like this for free quadratic modules:
	^ (self rank // 2) even ifTrue: [self gramian determinant] ifFalse: [self gramian determinant negated]
"
]

{ #category : #enumerating }
FreeModule >> do: aBlock [
	self coordinates do: [:each| aBlock value: (self elementAt: each)]
]

{ #category : #operations }
FreeModule >> dual [
	| extendedMatrix |
	self isEmbedded ifFalse: [^ self hom: self scalars asSelfModule].
	extendedMatrix := (self matrix, (self ambient scalars identityMatrix: self ambient rank)) transposed imageMatrix.
	^ self ambient dual span: (extendedMatrix transposed inverse copyFromRow: 1 to: self rank) over: self scalars
]

{ #category : #basis }
FreeModule >> e: anInteger [
	^ self basis at: anInteger
]

{ #category : #basis }
FreeModule >> elementAt: aTuple [
	"Answer a module element with the given coordinates in the distinguished basis."
	| answer |
	answer := self zero.
	aTuple withIndexDo: [:each :i| answer := (self e: i) * each + answer].
	^ answer
]

{ #category : #accessing }
FreeModule >> generators [
	^ self basis
]

{ #category : #accessing }
FreeModule >> gramian [
	"Answer the Gramian of the receiver, or Gram matrix.
	If M is the generator matrix of the receiver (>>matrix), and the inner product of the receiver is the dot product, then the Gramian is M * M transposed."
"	^ self matrix * self ambient innerProduct matrix * self matrix transposed"
	| f |
	f := self ambient innerProduct.
	^ self ambient scalars
		matrix: self rank
		evaluating:
			[:i :j| f value: {(self basis at: i). (self basis at: j)}]
]

{ #category : #operations }
FreeModule >> grassmannian: r [
	"Answer the set of r-dimensional subspaces of the receiver."
"	self isVectorSpace ifFalse: [DomainError signal: 'not a vector space']."
	self assert: (r <= self dimension and: [r >= 0]).
	^ Grassmannian new: r over: self
]

{ #category : #comparing }
FreeModule >> hash [
	^ self scalars hash + self rank hashMultiply
]

{ #category : #morphisms }
FreeModule >> hom: aModule [
	"Answer Hom(A,B), the R-module of morphisms that go from the receiver A to the argument B."
	aModule scalars = self scalars ifFalse: [DomainError signal: 'scalars don''t match'].
	^ FreeHomModule from: self to: aModule
]

{ #category : #operations }
FreeModule >> hull: aCollection [
	"Answer the affine hull (flat) spanned by the vectors in aCollection."

	| vectors x0 |
	vectors := aCollection asArray.
	x0 := vectors at: 1.
	^ AffineSubspace
		representative: x0
		direction:
			(self
				span: ((2 to: vectors size) collect: [ :i | x0 - (vectors at: i) ]))
]

{ #category : #morphisms }
FreeModule >> id [
	"Answer the identity morphism."
	^ LinearMap from: self to: self evaluating: [:x| x]
]

{ #category : #testing }
FreeModule >> includes: anObject [
	^ (self ambient includes: anObject) and: [self contains: anObject]
]

{ #category : #accessing }
FreeModule >> innerProduct [
	"Answer the bilinear form defining the Euclidean inner product."
	^ self propertyAt: #innerProduct ifAbsentPut:
		[BilinearForm
			from: (self, self)
			evaluating: [:each| (self coordinatesOf: each first) dot: (self coordinatesOf: each second)]]
]

{ #category : #testing }
FreeModule >> isFinite [
	^ self generators isEmpty or: [self scalars isFinite]
]

{ #category : #testing }
FreeModule >> isFreeAbelianGroup [
	"Answer true if the receiver is a Z-module."
	^ self scalars class = RationalIntegerRing
]

{ #category : #testing }
FreeModule >> isFreeModule [
	^ true
]

{ #category : #testing }
FreeModule >> isFullRank [
	^ self rank = self degree
]

{ #category : #testing }
FreeModule >> isLattice [
	^ self scalars isField not and: [self scalars isPID and: [self ambient scalars = self scalars fractions]]
]

{ #category : #testing }
FreeModule >> isNonDegenerate [
	^ self radical isTrivial
]

{ #category : #testing }
FreeModule >> isTrivial [
	^ self rank = 0
]

{ #category : #testing }
FreeModule >> isVectorSpace [
	^ self scalars isField or: [self isTrivial]
]

{ #category : #accessing }
FreeModule >> matrix [
	"Answer the generator matrix of the receiver, i.e. the matrix whose rows are the coordinates of the generators of the receiver in the ambient distinguished basis."
	^ self propertyAt: #matrix ifAbsentPut: [self ambient scalars identityMatrix: self rank] "if the matrix is not set, it means the receiver is a full ambient module (not embedded)"
]

{ #category : #private }
FreeModule >> matrix: aMatrix [
	self propertyAt: #matrix put: aMatrix
]

{ #category : #accessing }
FreeModule >> names [
	"Answer a list of names for use instead of the elements of the basis when printing linear maps, tensors, etc."
	^ self propertyAt: #names ifAbsentPut: [(1 to: self rank) collect: [:i| 'e', i printString sub]]
]

{ #category : #private }
FreeModule >> newSublattice: aMatrix [
	| M |
	M := aMatrix." echelon."
	M := Matrix rows: (M rows select: [:each| each isZero not]).	
	(self scalars isKindOf: RationalField)
		ifTrue: [^ Lattice new ambient: self; matrix: M].
	^ FreeModule new ambient: self; matrix: M; scalars: self scalars integers
]

{ #category : #private }
FreeModule >> newSubspace: aMatrix [
	| M |
	M := aMatrix echelon.
	M := Matrix rows: (M rows select: [:each| each isZero not]).	
	^ FreeModule new ambient: self; matrix: M
]

{ #category : #accessing }
FreeModule >> norm [
	^ self propertyAt: #norm ifAbsentPut:
		[Function from: self to: self scalars "should go to the reals"
			evaluating: [:x| (self innerProduct value: {x. x conjugated}) squareRoot]]
]

{ #category : #accessing }
FreeModule >> norm2 [
	"Answer the squared norm."
	^ self propertyAt: #norm2 ifAbsentPut:
		[Function from: self to: self scalars
			evaluating: [:x| (self innerProduct value: {x. x conjugated})]]
]

{ #category : #morphisms }
FreeModule >> orthogonalProjection [
	"Answer an orthogonal projection onto the receiver."
	| answer A T |
	self propertyAt: #orthogonalProjection ifPresent: [:aLinearMap| ^ aLinearMap].
	self isTrivial ifTrue: [^ self ambient endomorphisms zero].
	A := self matrix.
	T := A transposed.
	answer := self ambient endomorphisms ! (T * (A * T) inverse * A).
	self propertyAt: #orthogonalProjection put: answer.
	^ answer
]

{ #category : #basis }
FreeModule >> orthonormalBasis [
	^ self propertyAt: #orthonormalBasis ifAbsentPut: [self matrix orthonormalized rows collect: [:each| self ambient elementAt: each]]
]

{ #category : #converting }
FreeModule >> over: aRing [
	aRing = self scalars ifTrue: [^ self].
	aRing isPID ifFalse: [^ DomainError signal: 'not a PID']. "or isIntegralDomain?"
	self notYetImplemented
"	V := self ambient over: aRing fractions.
	self basis collect: [:each| "
]

{ #category : #operations }
FreeModule >> perp [
	"Answer the orthogonal complement of the receiver. This is the subspace of all vectors in the ambient that have inner product zero (are orthogonal to) all vectors in the receiver."
	self isTrivial ifTrue: [^ self ambient].
	"if we're in a vector space over the reals or complex numbers, we can get an orthogonal basis"
	((self scalars isKindOf: RealField) or: [self scalars isKindOf: ComplexField])
		ifTrue: [^ self ambient span: (self matrix extended orthogonalized copyFromRow: self rank + 1 to: self degree)].
	"otherwise we use this, but it assumes the associated bilinear form is just the dot product:"
	^ self ambient span: self matrix kernelMatrix
"
alternative:
	| k n |
	k := self dimension.
	n := self ambient dimension.
	^ (self basis extended orthogonalized copyFrom: k + 1 to: n) span

alternative 2:
	^ self projection kernel

alternative 3:?
	^ basis dual asArray inject: self space into: [:answer :each| answer intersection: each kernel]	

alternative 4:
	^ self ambient span: (self annihilator basis collect: [:f| f asVector])
"
]

{ #category : #operations }
FreeModule >> quotient [
	"Answer the quotient space of the ambient space by the receiver."
	self scalars isField ifTrue: [^ QuotientSpace mod: self]. "it's a quotient of vector spaces"
	(self scalars isPID and: [self ambient isFreeModule]) ifTrue: [^ QuotientModule mod: self].
	^ DomainError signal
]

{ #category : #operations }
FreeModule >> radical [
	^ self ï self perp
]

{ #category : #basis }
FreeModule >> rank [
	^ self basis size
]

{ #category : #morphisms }
FreeModule >> rotations [
	^ SpecialOrthogonalGroup on: self
]

{ #category : #accessing }
FreeModule >> size [
	| n |
	^ (n := self rank) = 0
		ifTrue: [ ^ 1 ]
		ifFalse: [ (self scalars size)  raisedTo: n ]
]

{ #category : #operations }
FreeModule >> span: aCollection [
	"Answer the submodule spanned by the module elements in aCollection."
	^ self span: aCollection over: self scalars
]

{ #category : #operations }
FreeModule >> span: aCollection over: aRing [
	"Answer the submodule spanned by the module elements in aCollection over aRing."
	| A M K |
	A := self ambient.
	M := (aCollection isKindOf: Matrix) ifTrue: [(aCollection over: A scalars) * self matrix] ifFalse: [Matrix rows: (aCollection collect: [:each| A coordinatesOf: each])].
	(aRing isField and: [aRing = self scalars])
		ifTrue:[^ A newSubspace: M].
	aRing isPID
		ifFalse: [^ self notYetImplemented].
	K := aRing fractions.
	A scalars = aRing
		ifTrue: [^ (A over: K) newSublattice: (M over: K)].
	A scalars = K
		ifTrue: [^ A newSublattice: M].
	^ self notYetImplemented
"	| A M K |
	A := self ambient.
	M := (aCollection isKindOf: Matrix) ifTrue: [(aCollection over: A scalars) * self matrix] ifFalse: [Matrix rows: (aCollection collect: [:each| A coordinatesOf: each])].
	(aRing isField and: [aRing = self scalars])
		ifTrue:[^ Subspace on: A matrix: M].
	aRing isPID
		ifFalse: [^ self notYetImplemented].
	K := aRing fractions.
	A scalars = aRing
		ifTrue: [^ Lattice on: (A over: K) matrix: (M over: K)].
	A scalars = K
		ifTrue: [^ Lattice on: A matrix: M].
	^ self notYetImplemented"
]

{ #category : #morphisms }
FreeModule >> to: aModule evaluating: aBlock [
	aModule isFreeModule ifFalse: [^ super to: aModule evaluating: aBlock].
	aModule scalars = self scalars ifFalse: [DomainError signal].
	^ LinearMap from: self to: aModule evaluating: aBlock
]

{ #category : #morphisms }
FreeModule >> to: aModule matrix: aMatrix [
	aModule isFreeModule ifFalse: [^ DomainError signal].
	aModule scalars = self scalars ifFalse: [DomainError signal].
	^ LinearMap from: self to: aModule matrix: aMatrix
]

{ #category : #testing }
FreeModule >> torsion [
	^ self null
]

{ #category : #basis }
FreeModule >> vectorAt: aTuple [
	"Custom notation for vector spaces."
	^ self elementAt: aTuple
]

{ #category : #elements }
FreeModule >> zero [
	^ self propertyAt: #zero ifAbsentPut: [self == self ambient ifTrue: [| e | (e := self e: 1) - e] ifFalse: [self ambient zero]]
]

{ #category : #comparing }
FreeModule >> ~ aModule [
	"Answer true if the receiver is isomorphic to the argument."
	^ self == aModule or: [aModule isFreeModule and: [self scalars = aModule scalars and: [self rank = aModule rank]]]
]

{ #category : #operations }
FreeModule >> ê [ aModule
	"Answer the direct sum of the receiver and the argument."
	aModule isFreeModule ifFalse: [^ super ê aModule].
	self scalars = aModule scalars ifFalse: [DomainError signal: 'scalars don''t match'].
	(self isEmbedded or: [aModule isEmbedded]) ifTrue: [^ self ambient ê aModule ambient span: self matrix ê aModule matrix].
	^ FreeDirectSumModule components: {self. aModule}
]

{ #category : #operations }
FreeModule >> í [ aFreeModule
	"Answer the tensor product of the receiver with the argument."
	self scalars = aFreeModule scalars ifFalse: [DomainError signal: 'scalars don''t match'].
	^ TensorProductModule components: {self. aFreeModule}
]

{ #category : #operations }
FreeModule >> ï [ aModule
	"Answer the intersection of the receiver and the argument."
	| M N |
	(self scalars isPID and: [self ambient = aModule ambient])
		ifFalse: [^ DomainError signal].
	self isTrivial ifTrue: [^ self].
	aModule isTrivial ifTrue: [^ aModule].
	self ambient = aModule ifTrue: [^ self].
	self = aModule ambient ifTrue: [^ aModule].
	self scalars = aModule scalars ifFalse: [^ self notYetImplemented].
	M := self matrix.
	N := (M, aModule matrix) cokernelMatrix.
	N isEmpty ifTrue: [^ self ambient null].
	N := N copyFrom: 1@1 to: N height @ M height.
	^ self ambient span: N * M over: self scalars
]
