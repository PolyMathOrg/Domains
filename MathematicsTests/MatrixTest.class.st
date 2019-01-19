Class {
	#name : #MatrixTest,
	#superclass : #TestCase,
	#category : #MathematicsTests
}

{ #category : #'as yet unclassified' }
MatrixTest >> newRandomMatrix: dim over: aRing [
	| samples |
	'2 atRandom = 1 ifTrue: [^ aRing^dim atRandomBits: 100]'.
	samples := {aRing zero. aRing one. aRing one negated}.
	^ aRing matrix: dim evaluating: [:i :j| 2 atRandom > 1 ifTrue: [aRing zero] ifFalse: [samples atRandom]]
]

{ #category : #'as yet unclassified' }
MatrixTest >> testAdjugate [
	| A I |
	A := Matrix rows: { (2,1,1). (-1,0,1). (0,2,1) }.
	I := A identity.
	self assert: A * A adjugate = (I * A determinant)
]

{ #category : #'as yet unclassified' }
MatrixTest >> testAdjugate2 [
	| A B |
	A := Matrix rows: { (-3,2,-5). (-1,0,-2). (3,-4,1) }.
	B := Matrix rows: { (-8,18,-4). (-5,12,-1). (4,-6,2) }.
	self assert: A adjugate = B
]

{ #category : #'as yet unclassified' }
MatrixTest >> testAdjugateProperties [
	| M A B I c |
	M := 'QQ ^ (3@3)'.
	A := M rows: { (-3,2,-5). (-1,0,-2). (3,-4,1) }.
	B := M rows: { (-1,2,3). (1,-2,1). (2,2,-1) }.
	c := 7.
	I := M identity.
	self assert: I adjugate = I.
	self assert: (A * B) adjugate = (B adjugate * A adjugate).
	self assert: '(A*c) adjugate = (A adjugate * (c^(M height - 1)))'.
	self assert: '(A^5) adjugate = (A adjugate ^ 5)'.
	self assert: A transposed adjugate = A adjugate transposed
]

{ #category : #'as yet unclassified' }
MatrixTest >> testBacklash [
	"Example from Sage documentation. Non-singular and square."
	| A B X |
	A := QQ matrix: 3 coefficients: #(1 2 4 5 3 1 1 2 -1).
	B := QQ matrix: 3@2 coefficients: #(1 5 1 2 1 5).
	X := A \ B.
	self assert: X = (QQ matrix: 3@2 coefficients: {-1/7. -11/7. 4/7. 23/7. 0. 0}).
	self assert: A * X = B
]

{ #category : #'as yet unclassified' }
MatrixTest >> testBacklashNoSolution [
	"Example from Sage documentation."
	| A v |
	A := QQ matrix: 2@3 coefficients: #(1 2 3 2 4 6).
	v := (1,1).
	self assert: (A \ v) isNil
]

{ #category : #'as yet unclassified' }
MatrixTest >> testBacklashNonSquare [
	"Example from Sage documentation."
	| A B X |
	A := QQ matrix: 2@4 coefficients: #(0 -1 1 0 -2 2 1 0).
	B := QQ matrix: 2@2 coefficients: #(1 0 1 -1).
	X := A \ B.
	self assert: X = (QQ matrix: 4@2 coefficients: (-3/2, (1/2), -1, 0, 0, 0, 0, 0)).
	self assert: A * X = B
]

{ #category : #'as yet unclassified' }
MatrixTest >> testBacklashNonSquare2 [
	| A B X |
	A := QQ matrix: 2@4 coefficients: #(0 0 -1 1 0 -2 2 1).
	B := QQ matrix: 2@2 coefficients: #(1 0 1 -1).
	X := A \ B.
	self assert: A * X = B
]

{ #category : #'as yet unclassified' }
MatrixTest >> testBacklashSingular [
	"Example from Sage documentation."
	| A B X |
	A := QQ matrix: 2@3 coefficients: #(1 2 3 2 4 6).
	B := QQ matrix: 2@2 coefficients: #(6 -6 12 -12).
	X := A \ B.
	self assert: X = (QQ matrix: 3@2 coefficients: (6, -6, 0, 0, 0, 0)).
	self assert: A * X = B
]

{ #category : #'as yet unclassified' }
MatrixTest >> testBacklashTuple [
	"Example from Sage documentation."
	| A v x |
	A := QQ matrix: 3 coefficients: #(1 2 3 -1 2 5 2 3 1).
	v := (1,2,3).
	x := A \ v.
	self assert: x = (-13/12,(23/12),(-7/12)).
	self assert: A * x = v
]

{ #category : #'as yet unclassified' }
MatrixTest >> testBacklashTupleNonSquare [
	"Example from Sage documentation."
	| A v x |
	A := QQ matrix: 2@3 coefficients: #(1 2 3 2 4 6).
	v := (-1/2, -1).
	x := A \ v.
	self assert: x = (-1/2, 0, 0).
	self assert: A * x = v
]

{ #category : #'as yet unclassified' }
MatrixTest >> testBacklashTupleOverZ [
	"Example from Sage documentation."
	| A v x |
	A := ZZ matrix: 2@3 coefficients: #(1 2 3 2 4 6).
	v := ZZ tuple: #(-1 -2).
	x := A \ v.
	self assert: x = (ZZ tuple: #(-1 0 0)).
	self assert: A * x = v
]

{ #category : #'as yet unclassified' }
MatrixTest >> testBacklashTupleOverZBug [
	| A b x |
	A := ZZ matrix: 3@3 coefficients: #(1 0 0 0 1 0 0 0 10).
	b := ZZ tuple: #(0 0 10).
	x := A \ b.
	self assert: A * x = b
]

{ #category : #'as yet unclassified' }
MatrixTest >> testCayleyHamiltorTheoremInQ [
	| n M A |
	n := 6 atRandom.
	M := 'QQ ^ (n@n)'.
	A := M atRandomBits: 100.
	self assert: (A characteristicPolynomial value: A) isZero
]

{ #category : #'as yet unclassified' }
MatrixTest >> testCayleyHamiltorTheoremInZ [
	| n M A |
	n := 6 atRandom.
	M := 'ZZ ^ (n@n)'.
	A := M atRandomBits: 100.
	self assert: (A characteristicPolynomial value: A) isZero
]

{ #category : #'as yet unclassified' }
MatrixTest >> testCharacteristicMatrixAndPolynomialOverQ [
	| n A |
	n := 5 atRandom.
	A := 'QQ ^ (n@n) :: atRandomBits: n*5'.
	self assert: A characteristicPolynomial = A characteristicMatrix determinant
]

{ #category : #'as yet unclassified' }
MatrixTest >> testCharacteristicMatrixAndPolynomialOverZ [
	| n A |
	n := 5 atRandom.
	A := 'ZZ ^ (n@n) :: atRandomBits: n*5'.
	self assert: A characteristicPolynomial = A characteristicMatrix determinant
]

{ #category : #'as yet unclassified' }
MatrixTest >> testCharacteristicPolynomial [
	| M A B |
	M := 'QQ ^ (5@5)'.
	A := M atRandomBits: 100.
	self assert: (A characteristicPolynomial value: A) isZero.
	B := M atRandomBits: 100.
	self assert: (A*B) characteristicPolynomial = (B*A) characteristicPolynomial
]

{ #category : #'as yet unclassified' }
MatrixTest >> testCokernelMatrix [
	"From Sage."
	| A B |
	A := QQ matrix: {(1,2,4,-7,4). (1,1,0,2,-1). (1,0,3,-3,1). (0,-1,-1,3,-2). (0,0,-1,2,-1)}.
	B := QQ matrix: {(1,0,-1,2,-1). (0,1,-1,1,-4)}.
	self assert: A cokernelMatrix "echelon" = B
]

{ #category : #'as yet unclassified' }
MatrixTest >> testDeterminant [
	| M m |
	M := 'QQ ^ (2@2)'.
	m := M rows: { (2,1). (-1,0) }.
	self assert: m determinant = 1
]

{ #category : #'as yet unclassified' }
MatrixTest >> testDeterminant2 [
	| M vandermonde |
	M := 'QQ ^ (3@3)'.
	vandermonde := M rows: {(1,1,1). (3,5,7). (9,25,49)}.
	self assert: vandermonde determinant = 16.
	M := 'ZZ ^ (3@3)'.
	vandermonde := M rows: {(1,1,1). (3,5,7). (9,25,49)}.
	self assert: vandermonde determinant = 16
]

{ #category : #'as yet unclassified' }
MatrixTest >> testDeterminant3 [
	| M A B |
	M := 'QQ ^ (3@3)'.
	A := M rows: {(1,1,1). (3,5,7). (9,25,49)}.
	B := M rows: {(1,0,4). (1,1,1). (2,-2,-3)}.
	self assert: A determinant * B determinant = (A * B) determinant.
	M := 'ZZ ^ (3@3)'.
	A := M rows: {(1,1,1). (3,5,7). (9,25,49)}.
	B := M rows: {(1,0,4). (1,1,1). (2,-2,-3)}.
	self assert: A determinant * B determinant = (A * B) determinant
]

{ #category : #'as yet unclassified' }
MatrixTest >> testDomainError [
	| A B |
	A := 'ZZ ^ (4@4) :: identity'.
	self should: [A / 2] raise: DomainError.
	B := 'QQ ^ (4@4) :: identity'.
	self should: [A + B] raise: DomainError.
	self should: [A * B] raise: DomainError
]

{ #category : #'as yet unclassified' }
MatrixTest >> testFundamentalSubspacesDefinitions [
	| m n A |
	m := 6 atRandom.
	n := 6 atRandom.
	A := self newRandomMatrix: m@n over: QQ.
	'self assert: A rowSpace = (QQ^n span: A rows)'. "definition"
	'self assert: A columnSpace = (QQ^m span: A columns)'. "definition"
	self assert: A coimage = A transposed image. "definition"
	self assert: A cokernel = A transposed kernel. "definition"
	self assert: A image = A columnSpace. "synonyms"
	self assert: A coimage = A rowSpace. "synonyms"

]

{ #category : #'as yet unclassified' }
MatrixTest >> testFundamentalSubspacesDimensions [
	| m n A r |
	m := 6 atRandom.
	n := 6 atRandom.
	A := self newRandomMatrix: m@n over: QQ.
	r := A rank.
	self assert: A image dimension = r.
	self assert: A kernel dimension = (n - r).
	self assert: A nullity = (n - r). "definition"
	self assert: A coimage dimension = r.
	self assert: A cokernel dimension = (m - r)
]

{ #category : #'as yet unclassified' }
MatrixTest >> testHNFvsCHNF [
	| M A |
	M := 'ZZ ^ (4@4)'.
	A := M atRandomBits: 50.
	self assert: A HNF = A antitransposed CHNF antitransposed
]

{ #category : #'as yet unclassified' }
MatrixTest >> testHermiteNormalForm [
	"Example from wikipedia."
	| M A H |
	M := 'ZZ ^ (4@4)'.
	A := M rows: { (3,3,1,4). (0,1,0,0). (0,0,19,16). (0,0,0,3) }.
	H := M rows: { (3,0,1,1). (0,1,0,0). (0,0,19,1). (0,0,0,3) }.
	self assert: A HNF = H
]

{ #category : #'as yet unclassified' }
MatrixTest >> testHermiteNormalForm2 [
	| M A H |
	M := 'ZZ ^ (3@3)'.
	A := M rows: { (9,-36,30). (-36,192,-180). (30,-180,180) }.
	H := M rows: { (3,0,30). (0,12,0). (0,0,60) }.
	self assert: A HNF = H
]

{ #category : #'as yet unclassified' }
MatrixTest >> testHermiteNormalForm3 [
	"Example from wikipedia"
	| M A H |
	M := 'ZZ ^ (3@4)'.
	A := M rows: { (2,3,6,2). (5,6,1,6). (8,3,1,1) }.
	H := M rows: { (1,0,50,-11). (0,3,28,-2). (0,0,61,-13) }.
	self assert: A HNF = H
]

{ #category : #'as yet unclassified' }
MatrixTest >> testHermiteNormalForm4 [
	"Example from Sage"
	| A B |
	A := ZZ matrix: {(1,2,3,4). (5,6,7,8). (9,10,11,12)}.
	B := ZZ matrix: {(1,2,3,4). (0,4,8,12). (0,0,0,0)}.
	self assert: A HNF = B.
	self assert: A echelon = B "the echelon form of integers matrices is the hermite normal form"
]

{ #category : #'as yet unclassified' }
MatrixTest >> testInverse [
	| M A I |
	M := 'QQ ^ (3@3)'.
	A := M rows: { (2,1,1). (-1,0,1). (0,2,1) }.
	I := M identity.
	self assert: A inverse * A = I.
	self assert: A * A inverse = I
]

{ #category : #'as yet unclassified' }
MatrixTest >> testInverse2 [
	| Qx x f A |
	Qx := QQ polynomials.
	x := Qx x.
	f := 'x^8 + (x^6) - (3*(x^4)) - (3*(x^3)) + (8*(x^2)) + (2*x) - 5'.
	A := f companion.
	self assert: (A * A inverse) isIdentity
]

{ #category : #'as yet unclassified' }
MatrixTest >> testIsEchelonForm [
	| A E |
	A := self newRandomMatrix: 6 atRandom @ 6 atRandom over: QQ.
	E := A echelon.
	self assert: E isEchelonForm.
	self assert: E isReducedEchelonForm
]

{ #category : #'as yet unclassified' }
MatrixTest >> testIsHermiteNormalForm [
	"Example from wikipedia."
	| M A H |
	M := 'ZZ ^ (4@4)'.
	A := M rows: { (3,3,1,4). (0,1,0,0). (0,0,19,16). (0,0,0,3) }.
	H := M rows: { (3,0,1,1). (0,1,0,0). (0,0,19,1). (0,0,0,3) }.
	self assert: A isHermiteNormalForm not.
	self assert: H isHermiteNormalForm
]

{ #category : #'as yet unclassified' }
MatrixTest >> testIsHermiteNormalForm2 [
	| M |
	M := 'ZZ ^ (4@4)' rows: {(2,0,1,11). (0,1,5,12). (0,0,6,12). (0,0,0,33)}.
	self assert: M isHermiteNormalForm.
	self assert: M transposed isHermiteNormalForm not.
	M := 'ZZ ^ (5@4) rows: {(2,0,1,11). (0,1,5,12). (0,0,6,12). (0,0,0,33). (0,0,0,0)}'.
	self assert: M isHermiteNormalForm.
	M := 'ZZ ^ (5@4) rows: {(2,0,1,11). (0,1,5,12). (0,0,6,12). (0,0,0,33). (0,0,0,1)}'.
	self assert: M isHermiteNormalForm not
]

{ #category : #'as yet unclassified' }
MatrixTest >> testJordanNormalForm [
	| M A jordan B |
"	<timeout: 2>"
	M := 'QQ ^ (4@4)'.
	A := M rows: { (5,4,2,1). (0,1,-1,-1). (-1,-1,3,0). (1,1,-1,2) }.
	jordan := A jordan.
	self assert: jordan size = 3.
	B := 'QQ ^ (1@1) scalar: 1'.
	self assert: (jordan includes: B).
	B := 'QQ ^ (1@1) scalar: 2'.
	self assert: (jordan includes: B).
	B := 'QQ ^ (2@2) scalar: 4 :: at: 1@2 put: 1; yourself'.
	self assert: (jordan includes: B)
]

{ #category : #'as yet unclassified' }
MatrixTest >> testKernel [
	| A S |
	'A := QQ ^ (4@6) rows: {(1, 0, -3, 0, 2, -8). (0, 1, 5, 0, -1, 4). (0, 0, 0, 1, 7, -9). (0, 0, 0, 0, 0, 0)}.
		S := QQ ^ 6 span: {(3,-5,1,0,0,0). (-2,1,0,-7,1,0). (8,-4,0,9,0,1)}.
		self assert: A kernel = S'
]

{ #category : #'as yet unclassified' }
MatrixTest >> testKernelImageTheorem [
	| n A |
	n := 6 atRandom.
	A := self newRandomMatrix: n@n over: QQ.
	self assert: A kernel dimension + A image dimension = n
]

{ #category : #'as yet unclassified' }
MatrixTest >> testKroneckerProduct [
	| A B C |
	'A := ZZ ^ (2@2) elementAt: (1,2,3,4).
		B := ZZ ^ (2@2) elementAt: (0,5,6,7).
		C := ZZ ^ (4@4) elementAt: (0, 5, 0, 10, 6, 7, 12, 14, 0, 15, 0, 20, 18, 21, 24, 28)'.
	self assert: (A kronecker: B) = C
]

{ #category : #'as yet unclassified' }
MatrixTest >> testLeftInverse [
	| M A |
	M := 'QQ ^ (5@3)'.
	[A := M atRandomBits: 1000. A rank = 3] whileFalse.
	self assert: (A leftInverse * A) isIdentity
]

{ #category : #'as yet unclassified' }
MatrixTest >> testMinimalPolynomial [
	| M m f |
	M := 'QQ ^ (5@5)'.
	m := M atRandomBits: 100.
	f := m minimalPolynomial.
	self assert: f | m characteristicPolynomial.
	self assert: (f value: m) isZero
]

{ #category : #'as yet unclassified' }
MatrixTest >> testMinor [
	| M A |
	M := 'ZZ ^ (3@3)'.
	A := M elementAt: #(1 2 3 4 5 6 7 8 9).
	self assert: (A minor: 2@3) = -6
]

{ #category : #'as yet unclassified' }
MatrixTest >> testMinors [
	| A |
	A := 'ZZ ^ (2@3) elementAt: (1 to: 6)'.
	self assert: (A minors: 2) asArray = #(-3 -6 -3)
]

{ #category : #'as yet unclassified' }
MatrixTest >> testPermanent [
	"Example from https://en.wikipedia.org/wiki/Permanent_(mathematics)"
	| A |
	A := ZZ matrix: 4 coefficients: #(1 1 1 1 2 1 0 0 3 0 1 0 4 0 0 1).
	self assert: A permanent = 10
]

{ #category : #'as yet unclassified' }
MatrixTest >> testQRDecomposition [
	| n A QR Q R |
	n := 3.
	[A := 'QQ ^ (n@n) :: atRandomBits: n*n'. A isFullRank] whileFalse.
	A := A over: RR.
	QR := A QR.
	Q := QR first.
	R := QR second.
	self assert: Q * R = A.
	self assert: Q isOrthogonal.
	self assert: R isUpperTriangular
]

{ #category : #'as yet unclassified' }
MatrixTest >> testQRDecomposition2 [
	"Example from wikipedia:"
	| A Q R |
	A := RR matrix: 3@3 coefficients: #(12 -51 4 6 167 -68 -4 24 -41).
	Q := RR matrix: 3@3 coefficients: {6/7. -69/175. -58/175. 3/7. 158/175. 6/175. -2/7. 6/35. -33/35}.
	R := RR matrix: 3@3 coefficients: #(14 21 -14 0 175 -70 0 0 35).
	self assert: A QR = {Q. R}
]

{ #category : #'as yet unclassified' }
MatrixTest >> testRank [
	| M vandermonde |
	M := 'QQ ^ (3@3)'.
	vandermonde := M rows: {(1,1,1). (3,5,7). (9,25,49)}.
	self assert: vandermonde rank = 3.
	M := 'ZZ ^ (3@3)'.
	vandermonde := M rows: {(1,1,1). (3,5,7). (9,25,49)}.
	self assert: vandermonde rank = 3
]

{ #category : #'as yet unclassified' }
MatrixTest >> testRank2 [
	| M m |
	M := 'QQ ^ (3@3)'.
	m := M rows: {(1,1,1). (2,2,0). (3,3,1)}.
	self assert: m rank = 2.

	M := 'ZZ ^ (3@3)'.
	m := M rows: {(1,1,1). (2,2,2). (5,5,5)}.
	self assert: m rank = 1
]

{ #category : #'as yet unclassified' }
MatrixTest >> testRankNullityTheorem [
	| n A |
	n := 6 atRandom.
	A := self newRandomMatrix: n@n over: QQ.
	self assert: A rank + A nullity = n
]

{ #category : #'as yet unclassified' }
MatrixTest >> testReducerPivots [
	| A |
	A := 'ZZ ^ (3@3)' rows: {(0,-1,-1). (0,-20,1). (0,1,2)}.
	self assert: A reduction pivots asArray = {1@2. 2@3}
]

{ #category : #'as yet unclassified' }
MatrixTest >> testRightInverse [
	| M A |
	M := 'QQ ^ (3@5)'.
	[A := M atRandomBits: 1000. A rank = 3] whileFalse.
	self assert: (A * A rightInverse) isIdentity
]

{ #category : #'as yet unclassified' }
MatrixTest >> testSimilarity [
	"Examples from wikipedia article on SNF"
	| M A B C |
	M := 'QQ ^ (2@2)'.
	A := M rows: {(1,2). (0,1)}.
	B := M rows: {(3,-4). (1,-1)}.
	C := M rows: {(1,0). (1,2)}.
	self assert: A ~ B.
	self deny: A ~ C
]

{ #category : #'as yet unclassified' }
MatrixTest >> testSimilarity2 [
	| n M A B P |
	n := 5 atRandom.
	M := 'QQ ^ (n@n)'.
	A := M atRandomBits: 10*n*n.
	[(P := M atRandomBits: 10*n*n) isSingular] whileTrue.
	B := M atRandomBits: 10*n*n.
	self assert: A ~ (P inverse * A * P).
	self deny: A ~ B
]

{ #category : #'as yet unclassified' }
MatrixTest >> testSmithNormalForm [
	| M A |
	M := 'ZZ ^ (3@3)'.
	A := M rows: { (2,4,4). (-6,6,12). (10,-4,-16) }.
	self assert: A SNF = #(2 6 12)
]

{ #category : #'as yet unclassified' }
MatrixTest >> testSmithNormalForm2 [
	| M A |
	M := 'ZZ ^ (3@3)'.
	"Reduced Laplacian matrix of K_4:"
	A := M rows: { (3,-1,-1). (-1,3,-1). (-1,-1,3) }.
	self assert: A SNF = #(1 4 4)
]

{ #category : #'as yet unclassified' }
MatrixTest >> testSmithNormalForm3 [
	"Example from Willian Stein, 'Algebraic Number Theory, A Computational Approach'."
	| M A |
	M := 'ZZ ^ (3@3)'.
	A := M rows: { (1,4,9). (16,25,36). (49,64,81) }.
	self assert: A SNF = #(1 3 72)
]

{ #category : #'as yet unclassified' }
MatrixTest >> testSmithNormalForm4 [
	"Smith form of a 3x3 matrix of rank 2.
	Example from Willian Stein, 'Algebraic Number Theory, A Computational Approach'."
	| M A |
	M := 'ZZ ^ (3@3)'.
	A := M rows: { (2,3,4). (5,6,7). (8,9,10) }.
	self assert: A SNF = #(1 3 0) "this fails, but Cohen defines SNF only for nonsingular matrices"
]

{ #category : #'as yet unclassified' }
MatrixTest >> testTransposed [
	| A |
	'A := ZZ ^ (6 atRandom @ 6 atRandom) :: atRandomBits: 1000'.
	self assert: A columns = A transposed rows.
	self assert: A transposed transposed = A
]
