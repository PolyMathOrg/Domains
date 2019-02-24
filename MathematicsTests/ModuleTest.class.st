Class {
	#name : #ModuleTest,
	#superclass : #TestCase,
	#category : #MathematicsTests
}

{ #category : #private }
ModuleTest >> newFreeModule [
	^ self
		newFreeModuleOver:
			{ZZ.
			QQ.
			(ZZ / (10 atRandom + 1))} atRandom
]

{ #category : #private }
ModuleTest >> newFreeModuleOver: scalars [
	| M N |
"	M := 2 atRandom = 1 ifTrue: [scalars ^ (5 atRandom - 1)] ifFalse: [scalars ^ (5 atRandom - 1 @ (5 atRandom - 1))]."
	M := 2 atRandom = 1 ifTrue: [scalars raisedTo: (4 atRandom)] ifFalse: [scalars raisedTo: (4 atRandom @ 4 atRandom)].
	"don't let it get too big, or the test is too slow:"
	M rank < 4 ifTrue:
		[3 atRandom = 1 ifTrue: [^ M endomorphisms].
		N := self newFreeModuleOver: scalars.
		N rank < 5 ifFalse: [^ M ê N].
		2 atRandom = 1 ifTrue: [^ M hom: N].
		'2 atRandom = 1 ifTrue: [^ M í N]'.
		^ M ê N].
	3 atRandom = 1 ifTrue: [^ M dual].
	^ M
]

{ #category : #private }
ModuleTest >> newFreeModuleOverPID [
	^ self
		newFreeModuleOver:
			{QQ.
			(ZZ / 2).
			ZZ.
			QQ polynomials} atRandom
]

{ #category : #private }
ModuleTest >> newLinearMap [
	| K V W |
	K := {QQ.
	(ZZ / #(2 3 5 7) atRandom)} atRandom.
	V := self newFreeModuleOver: K.
	W := self newFreeModuleOver: K.
	^ (V hom: W) ! (self newMatrix: W rank @ V rank over: K) 
]

{ #category : #private }
ModuleTest >> newMatrix: dim over: aRing [
	| samples |
	2 atRandom = 1 ifTrue: [^ (aRing raisedTo: dim) atRandomBits: 100].
	samples := {aRing zero.
	aRing one.
	aRing one negated}.
	^ aRing
		matrix: dim
		evaluating: [ :i :j | 
			2 atRandom > 1
				ifTrue: [ aRing zero ]
				ifFalse: [ samples atRandom ] ]
]

{ #category : #private }
ModuleTest >> newSmallFreeModuleOver: scalars [
	| M N |
	'M := 2 atRandom = 1 ifTrue: [scalars ^ 3 atRandom] ifFalse: [scalars ^ (3 atRandom @ 3 atRandom)]'.
	"don't let it get too big, or the test is too slow:"
	'M rank < 3 ifTrue:
			[3 atRandom = 1 ifTrue: [^ M endomorphisms].
			N := self newFreeModuleOver: scalars.
			N rank < 4 ifFalse: [^ M ê N].
			2 atRandom = 1 ifTrue: [^ M hom: N].
			2 atRandom = 1 ifTrue: [^ M í N].
			^ M ê N]'.
	3 atRandom = 1 ifTrue: [^ M dual].
	^ M
]

{ #category : #private }
ModuleTest >> newSmallVectorSpace [
	^ self
		newSmallFreeModuleOver:
			{QQ.
			(ZZ / #(2 3 5 7) atRandom)} atRandom
]

{ #category : #private }
ModuleTest >> newVectorSpace [
	^ self
		newFreeModuleOver:
			{QQ.
			(ZZ / #(2 3 5 7) atRandom)} atRandom
]

{ #category : #other }
ModuleTest >> testAdjointMap [
	| V W f a |
	V := QQ raisedTo: (1 to: 3) atRandom.
	W := QQ raisedTo: (1 to: 5) atRandom.
	f := (V hom: W) atRandomBits: 100.
	a := f adjoint.
	self assert: a kernel equals: f image annihilator.
	self assert: a image equals: f kernel annihilator.
	self assert: f isSurjective equals: a isInjective.
	self assert: f isInjective equals: a isSurjective
]

{ #category : #other }
ModuleTest >> testAdjointProperties [
	| V W U f g a |
	V := QQ raisedTo: (1 to: 4) atRandom.
	W := QQ raisedTo: (1 to: 4) atRandom.
	f := (V hom: W) atRandomBits: 100.
	g := (V hom: W) atRandomBits: 100.
	a := QQ atRandomBits: 10.
	self assert: (f + g) adjoint equals: f adjoint + g adjoint.
	self assert: (f * a) adjoint equals: f adjoint * a.
	U := QQ raisedTo: (1 to: 4) atRandom.
	f := (U hom: V) atRandomBits: 100.
	self assert: (g compose: f) adjoint equals: (f adjoint compose: g adjoint)
]

{ #category : #other }
ModuleTest >> testAnnihilator [
	| V v S S0 |
	V := QQ raisedTo: 3.
	v := 1 , -2 , 1.
	S := V span: {v}.
	S0 := S annihilator.
	self assert: S0 dimension equals: S codimension.
	S0 basis do: [ :f | self assert: (f value: v) isZero ]
]

{ #category : #other }
ModuleTest >> testAnnihilatorProperties [
	| V S T |
	V := QQ raisedTo: 5.
	S := (V grassmannian: 4) atRandomBits: 100.
	T := (S grassmannian: 2) atRandomBits: 100.
	T := V span: T basis.	"hack, otherwise T ambient = S"
	self assert: T <= S.
	self assert: T annihilator >= S annihilator.	"reverses inclusions"
	self
		assert: (S + T) annihilator
		equals: S annihilator ï T annihilator.
	self
		assert: S dimension + S annihilator dimension
		equals: V dimension.
	self assert: V annihilator isTrivial
	"	self assert: S annihilator annihilator = S dual dual"
]

{ #category : #other }
ModuleTest >> testAnnihilatorZ2 [
	| V v S S0 |
	V := ZZ / 2 raisedTo: 4.
	[ (v := V atRandom) isZero ] whileTrue.
	S := V span: {v}.
	S0 := S annihilator.
	self assert: S0 dimension equals: S codimension.
	S0 basis do: [ :f | self assert: (f value: v) isZero ]
]

{ #category : #other }
ModuleTest >> testCanonicalMorphisms [
	| V W |
	V := QQ raisedTo: 3.
	W := V span: {(1 , 2 , 3)}.
	self assert: '(V null  W) isZero'.	"canonical morphism from initial object"
	self assert: '(V  W null) isZero'.	"canonical morphism to terminal object"
	self assert: '((W  W null) value: (1,2,3)) isZero'.
	self assert: '(W  V value: (2,4,6)) = (2,4,6)'	"canonical morphism to overobject"
]

{ #category : #other }
ModuleTest >> testDirectSum [
	| M N S |
	M := self newFreeModule.
	N := self newFreeModuleOver: M scalars.
	S := M ê N.
	self testFreeModule: S.
	self testLinearMap: (S ambient projection: 2 atRandom).
	self testLinearMap: (S ambient embedding: 2 atRandom)
]

{ #category : #basis }
ModuleTest >> testDiscriminant [
	| M |
	M := ZZ raisedTo: 3.
	self assert: M discriminant equals: 1.
	self assert: (M span: {(1 , 2 , 3)}) discriminant equals: 14.
	self
		assert:
			(M
				span:
					{(1 , 2 , 3).
					(1 , 1 , 1)}) discriminant
		equals: 6
]

{ #category : #isomorphisms }
ModuleTest >> testFirstIsomorphismTheorem2 [
	| V S T f |
	V := QQ raisedTo: 5.
	S := (V grassmannian: (1 to: V dimension) atRandom) atRandomBits: 50.
	T := (V grassmannian: (1 to: V dimension) atRandom )atRandomBits: 50.
	f := (S hom: T) atRandomBits: 50.
	self assert: f domain / f kernel ~ f image
]

{ #category : #isomorphisms }
ModuleTest >> testFirstIsomorphismTheorem: M [
	| S T f phi |
	S := (M grassmannian: (1 to: M rank) atRandom) atRandomBits: 50.
	T := (M grassmannian: (1 to: M rank) atRandom)atRandomBits: 50.
	f := (S hom: T) atRandomBits: 50.
	phi := S / f kernel
		to: f image
		evaluating: [ :x | f value: x representative ].
	self assert: phi isIsomorphism
]

{ #category : #isomorphisms }
ModuleTest >> testFirstIsomorphismTheoremOverCyclotomicField [
	self testFirstIsomorphismTheorem: ((CyclotomicField new: 7) raisedTo: 5)
]

{ #category : #isomorphisms }
ModuleTest >> testFirstIsomorphismTheoremOverGaloisField [
	self
		testFirstIsomorphismTheorem: ((GaloisField new: 10 atRandom nextPrime to: 3 atRandom + 1) raisedTo: 5)
]

{ #category : #isomorphisms }
ModuleTest >> testFirstIsomorphismTheoremOverPID [
	self testFirstIsomorphismTheorem: self newFreeModuleOverPID
]

{ #category : #isomorphisms }
ModuleTest >> testFirstIsomorphismTheoremOverQ [
	self testFirstIsomorphismTheorem: 'QQ ^ 5'
]

{ #category : #isomorphisms }
ModuleTest >> testFirstIsomorphismTheoremOverQuadraticField [
	self testFirstIsomorphismTheorem: '(QuadraticField sqrt: -5) ^ 5'
]

{ #category : #other }
ModuleTest >> testFreeModule: M [
	| c t v x y |
	x := M atRandomBits: 10 * M rank.
	self assert: x = (M elementAt: (M coordinatesOf: x)).
	y := M atRandomBits: 10 * M rank.
	c := M scalars atRandomBits: 20.
	v := x * c + y.
	t := (M coordinatesOf: x) * c + (M coordinatesOf: y).
	self assert: v = (M elementAt: t).
"	self testLinearMap: M basis coordinatesMap"
]

{ #category : #other }
ModuleTest >> testFreeModuleDiscriminant [
	"From Sage documentation of FreeModule."

	| M |
	M := ZZ raisedTo: 3.
	self assert: M discriminant = 1.
	self assert: (M span: {(1 , 2 , 3)}) discriminant = 14.
	self
		assert:
			(M
				span:
					{(1 , 2 , 3).
					(1 , 1 , 1)}) discriminant = 6
]

{ #category : #other }
ModuleTest >> testFreeZModule [
	| A x0 x y0 y |
	A := FormalSumsModule on: #(a b c) over: ZZ.
	x0 := -2 , -1 , 3.
	x := A elementAt: x0.
	y0 := 1 , 1 , 1.
	y := A elementAt: y0.
	self assert: x + y equals: (A elementAt: x0 + y0).
	self assert: x * 2 - y equals: (A elementAt: x0 * 2 - y0).
	self assert: (x - y - (x - y)) isZero.
	self assert: (A coordinatesOf: x) equals: x0
]

{ #category : #other }
ModuleTest >> testGrassmannian [
	| G S |
	G := 'QQ^3 grassmannian: 2'.
	S := G atRandomBits: 20.
	self assert: S dimension = 2.
	self assert: (G includes: S).
	self assert: (G dual includes: S perp dual)
]

{ #category : #other }
ModuleTest >> testInclusions [
	| S |
	self assert: (QQ raisedTo: 3) < (CC raisedTo: 3).
	self assert: (ZZ raisedTo: 3) < (QQ raisedTo: 3).
	self assert: (RR raisedTo: 3) > (QQ raisedTo: 3).
	self assert: (CC raisedTo: 3) > (RR raisedTo: 3).
	S := (QQ raisedTo: 3) span: {(1,2,3). (1,0,1)}.
		self assert: S < (QQ raisedTo:3).
		self assert: S < (CC raisedTo: 3).
		self deny: S < (ZZ raisedTo: 3).
		self deny: S > (ZZ raisedTo: 3)
]

{ #category : #basis }
ModuleTest >> testLinearBasisChange [
	| V B1 B2 C v |
	V := QQ raisedTo: 3.
	B1 := LinearBasis
		on: V
		elements:
			{(1 , 2 , 3).
			(1 , 1 , 1)}.
	B2 := LinearBasis
		on: V
		elements:
			{(2 , 2 , 2).
			(2 , 3 , 4)}.
	C := B1 changeTo: B2.
	v := B1 elementAt: 3 , 7.
	self assert: C * (3 , 7) = (B2 coordinatesOf: v)
]

{ #category : #basis }
ModuleTest >> testLinearBasisCoordinatesOf [
	| V basis c |
	V := QQ raisedTo: 3.
	basis := LinearBasis
		on: V
		elements:
			{(-1 , 0 , 0).
			(0 , 0 , 2)}.
	c := basis coordinatesOf: 1 , 0 , 4.
	self assert: c equals: -1 , 2
]

{ #category : #basis }
ModuleTest >> testLinearBasisCoordinatesOf2 [
	| V basis c |
	V := QQ raisedTo: 3.
	basis := LinearBasis
		on: V
		elements:
			{(-1 , 0 , 0).
			(0 , 0 , 2)}.
	c := basis coordinatesOf: 1 , 1 , 4.
	self assert: c isNil
]

{ #category : #basis }
ModuleTest >> testLinearBasisCoordinatesOf3 [
	| V B |
	V := QQ raisedTo: 3.
	B := LinearBasis
		on: V
		elements:
			{(1 , 1 , 1).
			(1 , 2 , 3)}.
	self assert: (B coordinatesOf: 1 , 1 , 1) equals: 1 , 0.
	self assert: (B coordinatesOf: 1 , 2 , 3) equals: 0 , 1.
	self assert: (B coordinatesOf: 0 , 1 , 2) equals: -1 , 1
]

{ #category : #basis }
ModuleTest >> testLinearBasisDual [
	| V basis B Bdual I |
	V := QQ raisedTo: 3.
	basis := LinearBasis
		on: V
		elements:
			{(-1 , 0 , 0).
			(0 , 1 , 2).
			(0 , 1 , 1)}.
	B := basis matrix.
	Bdual := basis dual matrix.
	I := B identity.
	self assert: B determinant equals: 1 / Bdual determinant.
	self assert: B transposed * Bdual equals: I
]

{ #category : #basis }
ModuleTest >> testLinearBasisDual2 [
	| V B Bdual |
	V := QQ raisedTo: 3.
	B := LinearBasis
		on: V
		elements:
			{(-1 , 0 , 0).
			(0 , 1 , 2).
			(0 , 1 , 1)}.
	Bdual := B dual.
	self assert: B size = Bdual size.
	1 to: B size do: [ :i | 
		1 to: Bdual size do: [ :j | 
			self
				assert:
					((Bdual at: j) value: (B at: i))
						=
							(i = j
								ifTrue: [ 1 ]
								ifFalse: [ 0 ]) ] ]
]

{ #category : #basis }
ModuleTest >> testLinearBasisGenerates [
	| V B |
	V := QQ raisedTo:3.
	B := LinearBasis
		on: V
		elements:
			{(1 , 1 , 1).
			(1 , 2 , 3)}.
	self assert: (B generates: 1 , 1 , 1).
	self assert: (B generates: 0 , 1 , 2).
	self deny: (B generates: 2 , 2 , 3)
]

{ #category : #'linear maps' }
ModuleTest >> testLinearForm1 [
	| V f |
	V := QQ raisedTo: 3.
	f := V dual evaluating: [ :v | v x + v y - v z ].
	self assert: (f value: 1 , 1 , 1) equals: 1.
	self assert: (f value: 2 , 2 , 1) equals: 3.
	self assert: (f value: 3 , 1 , -1) equals: 5
]

{ #category : #'linear maps' }
ModuleTest >> testLinearForm2 [
	| V f |
	V := QQ raisedTo: 3.
	f := V dual evaluating: [ :v | v x + v y - v z ].
	self assert: f domain equals: V.
	self assert: f kernel dimension equals: 2.
	self assert: f image dimension equals: 1
]

{ #category : #'linear maps' }
ModuleTest >> testLinearFormAsPolynomial [
	| V f x |
	V := (QQ raisedTo: 5) atRandom.
	f := V dual atRandomBits: 100.
	x := V atRandomBits: 100.
	self assert: (f value: x) equals: (f asPolynomial value: x).
	self assert: f asPolynomial asLinearForm equals: f
]

{ #category : #'linear maps' }
ModuleTest >> testLinearFormZ2 [
	| V f |
	V := (PrimeField new: 2) raiseTo: 4.
	f := V dual evaluating: [:v| v sum].
	self assert: f domain = V.
	self assert: f kernel dimension = 3.
	self assert: f image dimension = 1.
	self assert: (f kernel includes: (1,1,1,1) % 2)
]

{ #category : #'linear maps' }
ModuleTest >> testLinearMap [
	| f |
	f := self newLinearMap.
	self testLinearMap: f 
]

{ #category : #'linear maps' }
ModuleTest >> testLinearMap: f [
	| a1 a2 b1 b2 x |
	a1 := f domain atRandomBits: 20.
	a2 := f domain atRandomBits: 20.
	b1 := f value: a1.
	b2 := f value: a2.
	self assert: (f value: f domain zero) isZero.
	x := f domain scalars atRandomBits: 20.
	self assert: (f value: a1 * x + a2) = (b1 * x + b2)
]

{ #category : #'linear maps' }
ModuleTest >> testLinearMapAdjoint [
	| V W f fAdjoint phi |
	V := self newFreeModuleOver: QQ.
	W := self newFreeModuleOver: QQ.
	f := (V hom: W) atRandomBits: 50.
	fAdjoint := f adjoint.
	self assert: fAdjoint domain equals: f codomain dual.
	self assert: fAdjoint codomain equals: f domain dual.
	phi := W dual atRandomBits: 20.
	'self assert: (fAdjoint value: phi) = (phi î f)'
]

{ #category : #'linear maps' }
ModuleTest >> testLinearMapComposition [
	| X Y Z f g x |
	X := QQ raisedTo: 3.
		Y := QQ raisedTo: 5.
		Z := QQ raisedTo: 4.
	f := (X hom: Y) atRandomBits: 1000.
	g := (Y hom: Z) atRandomBits: 1000.
	x := X atRandomBits: 1000.
	self assert: '((X hom: Z) includes: g î f)'.
	self assert: '(g î f value: x) = (g value: (f value: x))'.
	self should: ['f î g'] raise: DomainError
]

{ #category : #'linear maps' }
ModuleTest >> testLinearMapCompositionError [
	| X Y Z f g |
	X := QQ raisedTo: 3.
	Y := QQ raisedTo: 5.
	Z := QQ raisedTo: 4.
	f := (X hom: Y) atRandomBits: 1000.
	g := (Y hom: Z) atRandomBits: 1000.
	self should: [ 'f î g' ] raise: DomainError
]

{ #category : #'linear maps' }
ModuleTest >> testLinearMapFiber [
	| f w v |
	f := self newLinearMap.
	w := f image atRandomBits: 100.
	v := (f fiberAt: w) atRandomBits: 100.
	self assert: (f value: v) equals: w
]

{ #category : #'linear maps' }
ModuleTest >> testLinearMapImage [
	| f image v w |
	f := self newLinearMap.
	image := f image.
	v := f domain atRandomBits: 100.
	w := f value: v.
	self assert: (image includes: w)
]

{ #category : #'linear maps' }
ModuleTest >> testLinearMapInverse [
	| V f |
	V := QQ raisedTo: 3.
	f := V automorphisms atRandomBits: 1000.
	'self assert: (f î f inverse) isIdentity.
		self assert: (f inverse î f) isIdentity'
]

{ #category : #'linear maps' }
ModuleTest >> testLinearMapKernel [
	| f kernel v |
	f := self newLinearMap.
	kernel := f kernel.
	v := kernel atRandomBits: 100.
	self assert: (f value: v) isZero
]

{ #category : #'linear maps' }
ModuleTest >> testLinearMapKernelZ2 [
	| V f kernel |
	V := (PrimeField new: 2) raiseTo: 3.
	f := V dual evaluating: [:v| v sum].
	kernel := f kernel.
	self assert: (kernel apply: f) isTrivial.
	self assert: kernel dimension = 2.
	self assert: (kernel includes: (0,1,1) % 2)
]

{ #category : #'linear maps' }
ModuleTest >> testLinearMapLeftInverse [
	| V W f |
	V := QQ raiseTo: 3.
	W := QQ raiseTo: 5.
	[f := (V hom: W) atRandomBits: 1000. f rank = 3] whileFalse.
	self assert: '(f leftInverse î f) = V id'
]

{ #category : #'linear maps' }
ModuleTest >> testLinearMapRightInverse [
	| V W f |
	V := QQ raiseTo: 5.
	W := QQ raiseTo: 3.
	[f := (V hom: W) atRandomBits: 1000. f rank = 3] whileFalse.
	'self assert: (f î f rightInverse) = W id'
]

{ #category : #'linear maps' }
ModuleTest >> testLinearMapZ2 [
	| V f kernel v |
	V := '(PrimeField new: 2) ^ (5 atRandom + 1)'.
	[f := V endomorphisms atRandom.
	(kernel := f kernel) isTrivial or: [kernel = V]] whileTrue. "find one with non-trivial kernel"
	[v := V atRandom. kernel includes: v] whileTrue.
	self assert: (f value: v) isZero not.
	v := kernel atRandom.
	self assert: (f value: v) isZero
]

{ #category : #other }
ModuleTest >> testMatricesQ [
	self testFreeModule: '(QQ ^ (5 atRandom @ 5 atRandom))'
]

{ #category : #other }
ModuleTest >> testMatricesZ [
	self testFreeModule: '(ZZ ^ (5 atRandom @ 5 atRandom))'
]

{ #category : #other }
ModuleTest >> testMatricesZ2 [
	self testFreeModule: '((ZZ / 2) ^ (5 atRandom @ 5 atRandom))'
]

{ #category : #other }
ModuleTest >> testMatricesZ4 [
	self testFreeModule: '((ZZ / 4) ^ (5 atRandom @ 5 atRandom))'
]

{ #category : #other }
ModuleTest >> testMatrixTraceAsLinearMap [
	| F f |
	F := 'QQ ^ (3@3) :: dual'. "linear forms"
	f := F evaluating: [:x| x trace].
	self assert: f = ((F x: 1) + (F x: 5) + (F x: 9))
]

{ #category : #other }
ModuleTest >> testOrthogonalProjection [
	| V S p v |
	V := QQ raisedTo: 3.
	S := V span: {(1, 1, 0). (1, 0, 0)}.
	p := S orthogonalProjection.
	self testProjection: p.
	v := (78, 21, 139).
	self assert: (p value: v) = (p value: (p value: v)). "idempotent at v"
	self assert: p isIdempotent.
	self assert: p kernel = S perp.
	self assert: p image = S.
	self assert: (S apply: p) = S
]

{ #category : #other }
ModuleTest >> testOrthogonalization [
	| V B |
	V := 'QQ ^ 3'.
	B := LinearBasis on: V elements: {(1, 1, 0). (1, 0, 0)}.
	self assert: B orthogonalized isOrthogonal.
	self assert: B extended orthogonalized isOrthogonal
]

{ #category : #other }
ModuleTest >> testOrthonormalization [
	| V B |
	V := 'QQ ^ 3'.
	B := LinearBasis on: V elements: {(1, 1, 0). (1, 0, 0)}.
	self assert: B orthonormalized isOrthonormal.
	self assert: B extended orthonormalized isOrthonormal
]

{ #category : #bugs }
ModuleTest >> testPIDCoordinatesOfBug [
	| M S |
	M := self newFreeModuleOverPID.
	S := 'M grassmannian: (1 to: M rank) atRandom :: atRandomBits: 50'.
	self assert: (S generators allSatisfy: [:each| (S coordinatesOf: each) notNil])
]

{ #category : #other }
ModuleTest >> testPerp [
	| V S p perp |
	V := QQ raisedTo: 3.
	S := V span: {(1, 1, 1). (2, 0, -2)}.
	perp := S perp.
	self assert: perp dimension = 1.
	self assert: (V innerProduct value: {perp basis first. S basis first}) isZero.
	self assert: (V innerProduct value: {perp basis first. S basis second}) isZero.
	p := S orthogonalProjection.
	self assert: p kernel = perp
]

{ #category : #other }
ModuleTest >> testPerpProperties [
	| V S T |
	V := QQ raisedTo: 3.
	S := V span: {(1, 1, 1). (2, 0, -2)}.
	T := V span: {(1, -1, -3)}. "subspace of S"
	self assert: S + S perp = V.
	self assert: T + T perp = V.
	self assert: (S ï S perp) isTrivial.
	self assert: S <= S perp perp.
	self assert: S perp < T perp "because S > T"
]

{ #category : #other }
ModuleTest >> testPerpZ2 [
	| V S perp |
	V := (ZZ / 2) raiseTo: 3.
	S := V span: {(1,1,1) % 2}.
	perp := S perp.
	self assert: perp dimension = 2.
	self assert: (V innerProduct value: {S basis first. perp basis first}) isZero.
	self assert: (V innerProduct value: {S basis first. perp basis second}) isZero
]

{ #category : #'linear maps' }
ModuleTest >> testProjection: f [
	| v |
	self testLinearMap: f.
	v := f domain atRandomBits: 20.
	self assert: (f value: v) = (f value: (f value: v)). "idempotent at v"
	self assert: f isIdempotent.
	self assert: (f image apply: f) = f image.
	self assert: (f codomain apply: f) = f image
]

{ #category : #other }
ModuleTest >> testQuotientMaps [
	| V S Q pi v s |
	V := 'QQ ^ 5'.
	S := 'V grassmannian: (1 to: V dimension) atRandom :: atRandomBits: 50'.
	Q := V/S.
	pi := Q projection.
	v := V atRandomBits: 100.
	s := pi value: v.
	self assert: (Q includes: s).
	self assert: (V includes: (pi section value: s)).
	self assert: s = (pi value: (pi section value: s))
]

{ #category : #other }
ModuleTest >> testQuotientModuleAnnihilator [
	"Example from Sage"
	| v1 v2 v3 V W |
	v1 := (1/2,0,0). v2 := (3/2,2,1). v3 := (0,0,1).
	V := 'QQ^3 span: {v1. v2. v3} over: ZZ'.
	W := 'QQ^3 span: {v1 + (v2*2). v1*9 + (v2*2). v3*4} over: ZZ'.
	self assert: (V/W) annihilator = (ZZ*16)
]

{ #category : #other }
ModuleTest >> testQuotientModuleInvariants [
	"Example from Sage"
	| v1 v2 v3 V W |
	v1 := (1/2,1,1). v2 := (3/2,2,1). v3 := (0,0,1).
	'V := QQ^3 span: {v1. v2. v3} over: ZZ.
		W := QQ^3 span: {v1*2 + (v2*4). v1*9 + (v2*12). v3*4} over: ZZ'.
	self assert: (V/W) invariants = #(1 4 12)
]

{ #category : #other }
ModuleTest >> testQuotientModuleInvariants2 [
	"Example from Sage"
	| V W |
	V := ZZ raiseTo: 3.
	W := V span: {(1,2,0). (0,1,0). (0,2,0)}.
	self assert: (V/W) invariants = #(1 1 0) "from example in sage fpg_module.py"
]

{ #category : #other }
ModuleTest >> testQuotientModuleIsFinite [
	"Example from Sage"
	| v1 v2 v3 V W |
	v1 := (1/2,0,0). v2 := (3/2,2,1). v3 := (0,0,1).
	'V := QQ^3 span: {v1. v2. v3} over: ZZ.
		W := QQ^3 span: {v1 + (v2*2). v1*9 + (v2*2). v3*4} over: ZZ'.
	self assert: (V/W) isFinite.
	W := V null.
	self assert: (V/W) isFinite not
]

{ #category : #other }
ModuleTest >> testQuotientSpace [
	| M S Q |
	M := self newVectorSpace.
	S := 'M grassmannian: (1 to: M rank) atRandom :: atRandomBits: M rank * 10'.
	Q := M/S.
	self assert: Q rank = (M rank - S rank).
	self assert: (Q includes: S + (M atRandomBits: M rank * 10)).
	self assert: (M / M null) rank = M rank.
	self assert: (M / M) rank = 0
]

{ #category : #other }
ModuleTest >> testQuotientSpace2 [
	| M x |
	M := 'QQ^3 / (1,2,3)'.
	x := M projection value: (1,2,3).
	self assert: x isZero.
"	self assert: (M lifting value: x) = (0,0,0)"
]

{ #category : #isomorphisms }
ModuleTest >> testSecondIsomorphismTheorem: M [
	| S T |
	'S := M grassmannian: (0 to: M rank) atRandom :: atRandomBits: 50.
		T := M grassmannian: (0 to: M rank) atRandom :: atRandomBits: 50.
		self assert: S+T <= M.
		self assert: S ï T <= M.
		self assert: (S+T)/T ~ (S/(S ï T))'
"	f := S -> T :: atRandomBits: 10.
	phi := S / f kernel -> f image evaluating: [:x| f value: x representative].
	self assert: phi isIsomorphism"
]

{ #category : #isomorphisms }
ModuleTest >> testSecondIsomorphismTheoremOverCyclotomicField [
	self testSecondIsomorphismTheorem: '(CyclotomicField new: 7) ^ 5'
]

{ #category : #isomorphisms }
ModuleTest >> testSecondIsomorphismTheoremOverGaloisField [
	self testSecondIsomorphismTheorem: '(GaloisField new: 10 atRandom nextPrime to: 3 atRandom + 1) ^ 5'
]

{ #category : #isomorphisms }
ModuleTest >> testSecondIsomorphismTheoremOverPID [
	self testSecondIsomorphismTheorem: self newFreeModuleOverPID
	
"	S := M grassmannian: (1 to: M rank) atRandom :: atRandomBits: 50.
	T := M grassmannian: (1 to: M rank) atRandom :: atRandomBits: 50.
	self assert: (S+T)/T ~ (S/(S ï T))
"
]

{ #category : #isomorphisms }
ModuleTest >> testSecondIsomorphismTheoremOverQ [
	self testSecondIsomorphismTheorem: 'QQ ^ 5'
]

{ #category : #isomorphisms }
ModuleTest >> testSecondIsomorphismTheoremOverQuadraticField [
	self testSecondIsomorphismTheorem: '(QuadraticField sqrt: -5) ^ 5'
]

{ #category : #other }
ModuleTest >> testSubmoduleInclusion [
	| V S P v w |
	V := '{ZZ. QQ polynomials. (ZZ/2) polynomials} atRandom ^ 3'.
	[v := V atRandomBits: 10. v isZero] whileTrue.
	S := V span: {v}.
	[w := V atRandomBits: 10. S includes: w] whileTrue.
	P := V span: {w*(V scalars atRandomBits: 10)-v. w}.
	self assert: S < P.
	self assert: P > S.
	self assert: S ~= P.
	self assert: P ~= S.
	self assert: (S > P) not.
	self assert: (P < S) not
]

{ #category : #other }
ModuleTest >> testSubmoduleIntersection [
	| V S T T2 |
	V := 'ZZ ^ 3'.
	S := V span: {(1, 1, 1). (2, 0, -2)}.
	'self assert: S ï S ambient = S. "intersection with the ambient vector space Q^3"
		self assert: S ï V asLattice = S. "intersection with over lattice Z^3"
		self assert: S ï S = S.
		T := V span: {(3,1,-1)}.
		self assert: S ï T = T.
		T2 := V span: {(3,1,-1). (0,1,0)}.
		self assert: S ï T2 = T'
]

{ #category : #other }
ModuleTest >> testSubmoduleSum [
	| V v w S T P |
	'V := ZZ ^ 3.
		[v := V atRandomBits: 10. v isZero not] whileFalse.
		[w := V atRandomBits: 10. w isZero not and: [v ~= w]] whileFalse.
		S := V span: {v}.
		T := V span: {w}.
		P := V span: {v. w}.
		self assert: S + T = P.
		self assert: T + S = P.
		T := V span: {v - w. v + w}.
		self assert: S + T = P'
]

{ #category : #other }
ModuleTest >> testSubspaceInclusion [
	| V S P v w |
	'V := QQ ^ 3.
		[v := V atRandomBits: 10. v isZero] whileTrue.
		S := V span: {v}.
		[w := V atRandomBits: 10. S includes: w] whileTrue.
		P := V span: {v-w. w}.
		self assert: S < P.
		self assert: P > S.
		self assert: S ~= P.
		self assert: P ~= S.
		self assert: (S > P) not.
		self assert: (P < S) not'
]

{ #category : #other }
ModuleTest >> testSubspaceIntersection [
	| V S T T2 |
	'V := QQ ^ 3.
		S := V span: {(1, 1, 1). (2, 0, -2)}.
		self assert: S ï V = S.
		self assert: S ï S = S.
		T := V span: {(3,1,-1)}.
		self assert: S ï T = T.
		T2 := V span: {(3,1,-1). (0,1,0)}.
		self assert: S ï T2 = T'
]

{ #category : #other }
ModuleTest >> testSubspaceOfSubspace [
	| V S s T t |
	V := 'QQ ^ 3'.
	S := (V grassmannian: 2) atRandomBits: 100.
	T := (S grassmannian: 1) atRandomBits: 100.
	self assert: S < V.
	self assert: T < S.
	self assert: T < V.
	[s := S atRandomBits: 100. T includes: s] whileTrue.
	[t := T atRandomBits: 100. t isZero] whileTrue.
	self assert: (S includes: s).
	self assert: (S includes: t).
	self assert: (T includes: t)
]

{ #category : #other }
ModuleTest >> testSubspaceSum [
	| V v w S T P |
	V := QQ raisedTo: 3.
	[v := V atRandomBits: 10. v isZero not] whileFalse.
	[w := V atRandomBits: 10. w isZero not and: [v ~= w]] whileFalse.
	S := V span: {v}.
	T := V span: {w}.
	P := V span: {v. w}.
	self assert: S + T = P.
	self assert: T + S = P.
	T := V span: {v - w. v + w}.
	self assert: S + T = P
]

{ #category : #other }
ModuleTest >> testSubspaceSumRandom [
	| V S T U |
	V := QQ raisedTo: 5.
	S := (V grassmannian: (0 to: V dimension) atRandom) atRandomBits: 100.
	T := (V grassmannian: (0 to: V dimension) atRandom) atRandomBits: 100.
	U := S + T.
	self assert: S <= U.
	self assert: T <= U
]

{ #category : #'tensor product' }
ModuleTest >> testTensorHomAdjunction [
	| V W U A B |
	V := self newSmallVectorSpace.
	W := self newSmallFreeModuleOver: V scalars.
	U := self newSmallFreeModuleOver: V scalars.
	A := VíW hom: U.
	B := V hom: (W hom: U).
	self assert: A ~ B.
"	phi := A to: B evaluating: [:f| B evaluating: [:v| (W to: U) evaluating: [:w| f value: víw]]].
	self testLinearMap: phi.
	self assert: phi isIsomorphism"
]

{ #category : #'tensor product' }
ModuleTest >> testTensorProductAssociativity [
	| V1 V2 V3 |
	'V1 := QQ ^ 2.
		V2 := QQ ^ 3.
		V3 := QQ ^ 4'.
	'self assert: (V1 í V2) í V3 ~ (V1 í (V2 í V3))'
]

{ #category : #'tensor product' }
ModuleTest >> testTensorProductCommutativity [
	| V W |
	V := QQ raisedTo: 3.
	W := QQ raisedTo: 4.
	'self assert: V í W ~ (W í V)'
]

{ #category : #'tensor product' }
ModuleTest >> testTensorProductDimension [
	| V1 V2 |
	'V1 := QQ ^ 5 atRandom.
		V2 := QQ ^ 5 atRandom'.
	'self assert: (V1 í V2) dimension = (V1 dimension * V2 dimension)'
]

{ #category : #'tensor product' }
ModuleTest >> testTensorProductDualHomIsomorphism [
	| V W A B |
	'V := self newVectorSpace.
		W := self newFreeModuleOver: V scalars.
		A := V dual í W.
		B := V hom: W.
		self assert: A ~ B'
"	phi := A to: B evaluating: [:t| B evaluating: [:v| t second * (t first value: v)]].
	self testLinearMap: phi.
	self assert: phi isIsomorphism"
]

{ #category : #'tensor product' }
ModuleTest >> testTensorProductDualIsomorphism [
	| V W A B |
	V := self newVectorSpace.
	W := self newFreeModuleOver: V scalars.
	'A := V dual í W dual.
		B := (V í W) dual'.
	self assert: A ~ B
"	phi := A to: B evaluating: [:s| B evaluating: [:t| (s first value: t first) * (s second value: t second)]].
	self testLinearMap: phi.
	self assert: phi isIsomorphism"
]

{ #category : #'tensor product' }
ModuleTest >> testTensorProductOfLinearForms [
	| V f g t v w |
	V := QQ raisedTo: 3.
	f := V dual atRandomBits: 10.
	g := V dual atRandomBits: 10.
	't := f í g'.
	v := V atRandomBits: 10.
	w := V atRandomBits: 10.
	self assert: (t value: t domain ! {v. w}) = (t codomain ! {f value: v. g value: w})
]

{ #category : #'tensor product' }
ModuleTest >> testTensorProductRelations [
	| V W T v v1 v2 w w1 w2 c |
	V := self newVectorSpace.
	W := self newFreeModuleOver: V scalars.
	T := V í W.
	v := V atRandomBits: 100.
	v1 := V atRandomBits: 100.
	v2 := V atRandomBits: 100.
	w := W atRandomBits: 100.
	w1 := W atRandomBits: 100.
	w2 := W atRandomBits: 100.
	c := V scalars atRandomBits: 100.
	self
		assert:
			(T
				!
					{v1.
					w})
				+
					(T
						!
							{v2.
							w})
				=
					(T
						!
							{(v1 + v2).
							w}).
	self
		assert:
			(T
				!
					{v.
					w1})
				+
					(T
						!
							{v.
							w2})
		equals:
			T
				!
					{v.
					(w1 + w2)}.
	self
		assert:
			(T
				!
					{v.
					w}) * c
				=
					(T
						!
							{(v * c).
							w}).
	self
		assert:
			(T
				!
					{v.
					w}) * c
		equals:
			T
				!
					{v.
					(w * c)}
]

{ #category : #isomorphisms }
ModuleTest >> testThirdIsomorphismTheorem: M [
	| S T |
	S := (M grassmannian: (0 to: M rank) atRandom) atRandomBits: 50.
	T := (S grassmannian: (0 to: S rank) atRandom) atRandomBits: 50.
	self assert: S / T <= (M / T).
	self assert: M / T / (S / T) ~ (M / S)
]

{ #category : #isomorphisms }
ModuleTest >> testThirdIsomorphismTheoremOverCyclotomicField [
	self testThirdIsomorphismTheorem: ((CyclotomicField new: 7) raisedTo: 5)
]

{ #category : #isomorphisms }
ModuleTest >> testThirdIsomorphismTheoremOverGaloisField [
	self testThirdIsomorphismTheorem: '(GaloisField new: 10 atRandom nextPrime to: 3 atRandom + 1) ^ 5'
]

{ #category : #isomorphisms }
ModuleTest >> testThirdIsomorphismTheoremOverPID [
	self testThirdIsomorphismTheorem: self newFreeModuleOverPID
]

{ #category : #isomorphisms }
ModuleTest >> testThirdIsomorphismTheoremOverQ [
	self testThirdIsomorphismTheorem: (QQ raisedTo: 5)
]

{ #category : #isomorphisms }
ModuleTest >> testThirdIsomorphismTheoremOverQuadraticField [
	self testThirdIsomorphismTheorem: ((QuadraticField sqrt: -5) raisedTo:5)
]

{ #category : #other }
ModuleTest >> testTuplesQ [
	self testFreeModule: ((QQ raisedTo: 5) atRandom)
]

{ #category : #other }
ModuleTest >> testTuplesRationalFunctionsQ [
	| F |
	F := QQ polynomials fractions.
	self testFreeModule: (F raisedTo: 3) atRandom
]

{ #category : #other }
ModuleTest >> testTuplesZ [
	self testFreeModule: (ZZ raisedTo: (5 atRandom))
]

{ #category : #other }
ModuleTest >> testTuplesZ2 [
	self testFreeModule: (((ZZ / 2)  raisedTo: 5) atRandom)
]

{ #category : #other }
ModuleTest >> testTuplesZ4 [
	self testFreeModule: (((ZZ / 4)  raisedTo: 5) atRandom)
]
