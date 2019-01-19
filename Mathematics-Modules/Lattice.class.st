"
A lattice is the set of integer linear combinations of a basis of a rational vector space. This is a discrete subgroup of the ambient Q-vector space (as abelian group) isomorphic to Z^n, and a free Z-module.

Lattice coordinates are in Z, while the elements of the receiver live in the ambient Q-vector space.
"
Class {
	#name : #Lattice,
	#superclass : #FreeModule,
	#category : #'Mathematics-Modules-Lattices'
}

{ #category : #examples }
Lattice class >> A: n [
	"Answer the lattice A_n = {(x0,...,xn) in Z^{n+1} : x0 + ... + xn = 0}."
	| t B |
	't := (-1,1), (QQ ^ (n-1)) zero'.
	B := OrderedCollection new.
	n timesRepeat: [B add: t. t := t >> 1].
	^ self basis: B
]

{ #category : #examples }
Lattice class >> Adual: n [
	"Answer the dual of A_n."
	| V B |
	'V := QQ ^ n'.
	B := OrderedCollection new.
	1 to: n do: [:i| B add: (1, (V e: i) negated)].
	B add: (QQ tuple: n+1 evaluating: [:i| i=1 ifTrue: [n negated / (n+1)] ifFalse: [1 / (n+1)]]).
	^ self basis: B
]

{ #category : #examples }
Lattice class >> D4 [
	"Answer the D4 lattice, which is self-dual."
	^ self basis: {(1,0,0,0). (0,1,0,0). (0,0,1,0). (1,1,1,1)/2}
]

{ #category : #examples }
Lattice class >> D: n [
	"Answer the checkboard lattice D_n = {(x1,...,xn) in Z^n : x0 + ... + xn is even}."
	| t0 t B |
	B := OrderedCollection new.
	't0 := (-1,-1), (QQ ^ (n-2)) zero'.
	B add: t0.
	't := (1,-1), (QQ ^ (n-2)) zero'.
	n-1 timesRepeat: [B add: t. t := t >> 1].
	^ self basis: B
]

{ #category : #examples }
Lattice class >> Ddual: n [
	"Answer the dual of D_n."
	| V B |
	V := 'QQ ^ n'.
	B := OrderedCollection new.
	1 to: n-1 do: [:i| B add: (V e: i)].
	B add: (QQ tuple: n evaluating: [:i| 1/2]).
	^ self basis: B
]

{ #category : #examples }
Lattice class >> E8 [
	| t0 t B answer |
	B := OrderedCollection new.
	t0 := (2,0,0,0,0,0,0,0).
	B add: t0.
	t := (-1,1,0,0,0,0,0,0).
	6 timesRepeat: [B add: t. t := t >> 1].
	B add: (1,1,1,1,1,1,1,1)/2.
	answer := self basis: B.
	'answer properties
			at: #minimalNorm put: 2;
			at: #kissingNumber put: 240;
			at: #CoxeterNumber put: 30;
			at: #packingRadius put: 1/2 sqrt;
			at: #density put: Float pi ^ 4 / 384;
			at: #thickness put: Float pi ^ 4 / 24'.
	^ answer
]

{ #category : #examples }
Lattice class >> Z: n [
	"Answer the n-dimensional cubic or integer lattice Z^n."
	^ 'self basis: (QQ ^ n) basis'
]

{ #category : #'instance creation' }
Lattice class >> basis: aCollection [
	| V M |
	M := Matrix rows: aCollection asArray.
	V := 'M scalars ^ M width'.
	^ self new ambient: V; matrix: M
]

{ #category : #examples }
Lattice class >> bcc [
	"Answer the body-centered cubic lattice (bcc).
	D*_3 is equivalent to bcc."
	^ self basis: {(2,0,0). (0,2,0). (1,1,1)}
]

{ #category : #examples }
Lattice class >> fcc [
	"Answer the face-centered cubic lattice (fcc).
	Both A_3 and D_3 are equivalent to the fcc."
	^ self basis: {(-1,-1,0). (1,-1,0). (0,1,-1)}
]

{ #category : #examples }
Lattice class >> leech [
	"The Leech lattice is the unique even unimodular lattice in R^24 with with no norm 2 vectors."
	| G answer |
	G := QQ matrix: 24 coefficients:
#(8 4 4 4 4 4 4 2 4 4 4 2 4 2 2 2 4 2 2 2 0 0 0 -3
 4 4 2 2 2 2 2 2 2 2 2 2 2 2 1 1 2 1 1 2 1 0 0 -1
 4 2 4 2 2 2 2 2 2 2 2 2 2 1 2 1 2 2 1 1 1 0 0 -1
 4 2 2 4 2 2 2 2 2 2 2 2 2 1 1 2 2 1 2 1 1 0 0 -1
 4 2 2 2 4 2 2 2 2 2 2 1 2 2 2 2 2 2 2 2 1 0 0 -1
 4 2 2 2 2 4 2 2 2 2 2 1 2 2 1 1 2 1 2 1 0 0 0 -1
 4 2 2 2 2 2 4 2 2 2 2 1 2 1 2 1 2 1 1 2 0 0 0 -1
 2 2 2 2 2 2 2 4 1 1 1 2 1 2 2 2 1 2 2 2 2 0 0 1
 4 2 2 2 2 2 2 1 4 2 2 2 2 2 2 2 2 2 2 2 1 1 1 -1
 4 2 2 2 2 2 2 1 2 4 2 2 2 2 1 1 2 2 1 1 0 1 0 -1
 4 2 2 2 2 2 2 1 2 2 4 2 2 1 2 1 2 1 2 1 0 0 1 -1
 2 2 2 2 1 1 1 2 2 2 2 4 1 2 2 2 1 2 2 2 2 1 1 1
 4 2 2 2 2 2 2 1 2 2 2 1 4 2 2 2 2 1 1 1 1 1 1 -1
 2 2 1 1 2 2 1 2 2 2 1 2 2 4 2 2 1 2 2 2 2 2 1 1
 2 1 2 1 2 1 2 2 2 1 2 2 2 2 4 2 1 2 2 2 2 1 2 1
 2 1 1 2 2 1 1 2 2 1 1 2 2 2 2 4 1 2 2 2 2 1 1 1
 4 2 2 2 2 2 2 1 2 2 2 1 2 1 1 1 4 2 2 2 1 1 1 -1
 2 1 2 1 2 1 1 2 2 2 1 2 1 2 2 2 2 4 2 2 2 2 1 1
 2 1 1 2 2 2 1 2 2 1 2 2 1 2 2 2 2 2 4 2 2 1 2 1
 2 2 1 1 2 1 2 2 2 1 1 2 1 2 2 2 2 2 2 4 2 1 1 1
 0 1 1 1 1 0 0 2 1 0 0 2 1 2 2 2 1 2 2 2 4 2 2 2
 0 0 0 0 0 0 0 0 1 1 0 1 1 2 1 1 1 2 1 1 2 4 2 2
 0 0 0 0 0 0 0 0 1 0 1 1 1 1 2 1 1 1 2 1 2 2 4 2
 -3 -1 -1 -1 -1 -1 -1 1 -1 -1 -1 1 -1 1 1 1 -1 1 1 1 2 2 2 4).
	answer := self basis: G rows.
	answer properties
		at: #minimalNorm put: 4;
		at: #kissingNumber put: 196560;
		at: #coveringRadius put: 2 sqrt.
	^ answer
]

{ #category : #examples }
Lattice class >> leech2 [
	"Another version of the Leech lattice."
	| G answer |
	G := QQ matrix: 24 coefficients:
#(4 -2 -2 2 2 2 -1 -1 2 2 -2 2 -2 1 -1 1 1 2 0 -1 0 -2 -2 2
-2 4 0 0 -2 0 -1 2 0 0 2 -1 1 1 -1 1 -2 -2 -1 1 1 2 1 -2
-2 0 4 0 0 -2 0 0 0 0 2 0 0 -2 1 -1 -1 -1 1 -1 -1 1 0 -1
2 0 0 4 0 0 -2 -1 2 2 0 2 -2 1 0 2 -1 0 -1 0 1 -1 -1 0
2 -2 0 0 4 0 -1 -1 1 1 -1 1 -1 0 0 -1 0 2 0 -2 -2 -1 -2 2
2 0 -2 0 0 4 0 0 1 1 -1 1 -1 1 -1 1 1 0 1 0 1 0 -1 1
-1 -1 0 -2 -1 0 4 1 -1 -1 0 -2 2 0 0 0 2 -1 0 0 -1 1 2 -1
-1 2 0 -1 -1 0 1 4 1 1 2 -1 1 0 -1 1 -1 -1 -1 -1 -1 1 1 -1
2 0 0 2 1 1 -1 1 4 2 0 2 -2 1 0 1 -1 0 -1 -2 0 -1 -1 0
2 0 0 2 1 1 -1 1 2 4 0 1 -2 0 -1 1 -1 1 0 -1 -1 -1 -1 1
-2 2 2 0 -1 -1 0 2 0 0 4 0 1 -1 0 1 -1 -2 0 0 0 2 1 -2
2 -1 0 2 1 1 -2 -1 2 1 0 4 -2 0 1 0 0 1 0 -1 1 -2 -2 1
-2 1 0 -2 -1 -1 2 1 -2 -2 1 -2 4 0 -1 0 1 -1 -1 1 0 2 2 -2
1 1 -2 1 0 1 0 0 1 0 -1 0 0 4 -1 1 0 -1 -2 0 0 0 0 0
-1 -1 1 0 0 -1 0 -1 0 -1 0 1 -1 -1 4 -1 -1 0 0 0 0 -1 0 0
1 1 -1 2 -1 1 0 1 1 1 1 0 0 1 -1 4 0 -1 -1 0 1 1 0 -1
1 -2 -1 -1 0 1 2 -1 -1 -1 -1 0 1 0 -1 0 4 1 1 0 0 0 0 0
2 -2 -1 0 2 0 -1 -1 0 1 -2 1 -1 -1 0 -1 1 4 1 -1 -1 -2 -2 2
0 -1 1 -1 0 1 0 -1 -1 0 0 0 -1 -2 0 -1 1 1 4 0 0 0 -1 1
-1 1 -1 0 -2 0 0 -1 -2 -1 0 -1 1 0 0 0 0 -1 0 4 2 0 2 -1
0 1 -1 1 -2 1 -1 -1 0 -1 0 1 0 0 0 1 0 -1 0 2 4 0 1 -1
-2 2 1 -1 -1 0 1 1 -1 -1 2 -2 2 0 -1 1 0 -2 0 0 0 4 1 -2
-2 1 0 -1 -2 -1 2 1 -1 -1 1 -2 2 0 0 0 0 -2 -1 2 1 1 4 -2
2 -2 -1 0 2 1 -1 -1 0 1 -2 1 -2 0 0 -1 0 2 1 -1 -1 -2 -2 4).
	answer := self basis: G rows.
	answer properties
		at: #minimalNorm put: 4;
		at: #kissingNumber put: 196560;
		at: #coveringRadius put: 2 sqrt.
	^ answer
]

{ #category : #accessing }
Lattice >> associatedQuadraticForm [
	"Answer the quadratic form associated to this lattice."
	^ QuadraticForm from: self ambient matrix: self gramian
]

{ #category : #invariants }
Lattice >> coveringNormalizedThinkness [
	"Answer the normalized thickness (or central density) of the covering."
	^ 'self coveringRadius ^ self rank / self fundamentalVolume'
]

{ #category : #invariants }
Lattice >> coveringRadius [
	^ self propertyAt: #coveringRadius
]

{ #category : #invariants }
Lattice >> coveringSphereVolume [
	| n Vn pi p |
	pi := Float pi.
	n := self rank.
	'Vn := n even
			ifTrue: [pi ^ (n/2) / (n/2) factorial]
			ifFalse: [2^n * pi ^ ((n-1)/2) * ((n-1)/2) factorial / n factorial]'.
	p := self coveringRadius.
	^ 'p ^ n * Vn'
]

{ #category : #invariants }
Lattice >> coveringThickness [
	"Answer the thickness of the covering, i.e. the average number of spheres that contain a point of space. The thickness is also called the density or the sparsity of the covering."
	^ self coveringSphereVolume / self fundamentalVolume
]

{ #category : #invariants }
Lattice >> determinant [
	"The determinant det(L) of a lattice L is defined as the volume of its fundamental paralleleliped."
	self matrix isSquare ifTrue: [^ self matrix determinant abs].
	^ self gramian determinant squareRoot
]

{ #category : #invariants }
Lattice >> determinant2 [
	"The determinant det(L) of a lattice L is defined as the volume of its fundamental paralleleliped."
	| B |
	B := self matrix.
	"B square means the lattice is full-rank:"
	^ B isSquare ifTrue: [B determinant abs] ifFalse: [(B transposed * B) determinant squareRoot]
]

{ #category : #invariants }
Lattice >> fundamentalParallelepiped [
	^ self notYetImplemented
]

{ #category : #invariants }
Lattice >> fundamentalVolume [
	"Answer the volume of the fundamental region."
	^ self determinant sqrt
]

{ #category : #accessing }
Lattice >> innerProduct [
	^ self ambient innerProduct
]

{ #category : #testing }
Lattice >> isEven [
	^ self isIntegral and: [self gramian diagonal allSatisfy: [:each| each even]]
]

{ #category : #testing }
Lattice >> isIntegral [
	"Answer true if the receiver is integral, i.e. if the inner product of any two lattice vectors is an integer. This is true iff the Gram matrix contains only integer entries. Equivalently, a lattice L is integral if and only if it is contained in its dual L*: L <= L*. Also, an integral lattice L has the property: L <= L* <= L / det(L)."
	self gramian do: [:each| each isInteger ifFalse: [^ false]].
	^ true
]

{ #category : #testing }
Lattice >> isRootLattice [
	self isIntegral ifFalse: [^ false].
	self basis do: [:v| (self innerProduct value: v value: v) = 2 ifFalse: [^ false]].
	^ true
]

{ #category : #testing }
Lattice >> isSelfDual [
	"A self-dual lattice is a lattice L that equals it's dual L*, L = L*.
	A (integral) lattice is self-dual iff it is unimodular."
	^ self = self reciprocal
	
"alternative:
	^ self isUnimodular
"
]

{ #category : #testing }
Lattice >> isUnimodular [
	^ self isIntegral and: [self determinant abs = 1]
]

{ #category : #private }
Lattice >> matrix: aMatrix [
	| M |
	M := aMatrix HNF.
	M := Matrix rows: (M rows select: [:each| each isZero not]).	
	super matrix: M
]

{ #category : #invariants }
Lattice >> packingCenterDensity [
	^ 'self packingRadius ^ self rank / self fundamentalVolume'
]

{ #category : #invariants }
Lattice >> packingDensity [
	"Answer the density of the lattice packing, i.e. the volume of a sphere / the volume of the fundamental region."
	^ self packingSphereVolume / self fundamentalVolume
]

{ #category : #invariants }
Lattice >> packingRadius [
	^ self propertyAt: #packingRadius
]

{ #category : #invariants }
Lattice >> packingSphereVolume [
	| n Vn pi p |
	pi := Float pi.
	n := self rank.
	'Vn := n even
			ifTrue: [pi ^ (n/2) / (n/2) factorial]
			ifFalse: [2^n * pi ^ ((n-1)/2) * ((n-1)/2) factorial / n factorial]'.
	p := self packingRadius.
	^ 'p ^ n * Vn'
]

{ #category : #operations }
Lattice >> reciprocal [
	"Answer the dual lattice of the receiver (or reciprocal lattice, or polar lattice)."
	| B D |
	B := self matrix.
	D := B * (B transposed * B) leftInverse.
	^ self class basis: D rows
]

{ #category : #basis }
Lattice >> reducedBasis [
	^ self propertyAt: #reducedBasis ifAbsentPut: [(LLL basis: self basis) reducedBasis]
]

{ #category : #accessing }
Lattice >> scalars [
	^ ZZ
]

{ #category : #accessing }
Lattice >> shortVector [
	^ self reducedBasis first
]

{ #category : #invariants }
Lattice >> thetaSeries [
	"Answer the theta series of the lattice."
	^ self propertyAt: #thetaSeries
]
