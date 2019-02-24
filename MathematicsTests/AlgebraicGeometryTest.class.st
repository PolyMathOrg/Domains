Class {
	#name : #AlgebraicGeometryTest,
	#superclass : #TestCase,
	#category : #MathematicsTests
}

{ #category : #affine }
AlgebraicGeometryTest >> testAffinePlaneCurveMultiplicity [
	| A C |
	A := AffineSpace new: #(x y) over: QQ.
	C := A
		subscheme: A coordinateRing ! [ :x :y | (y raisedTo: 2) - (x raisedTo: 3) ].
	self assert: (C multiplicityAt: 1 , 1) equals: 1.
	self assert: (C multiplicityAt: 0 , 0) equals: 2
]

{ #category : #affine }
AlgebraicGeometryTest >> testAffineSchemeCartesianProduct [
	| X1 X2 P |
	X1 := AffineVariety circle.
	X2 := AffineVariety romanSurface.
	P := X1 cartesianProduct: X2.
	self assert: (P apply: (P ambient projection: 1)) equals: X1.
	self assert: (P apply: (P ambient projection: 2)) equals: X2.
	self assert: X1 dimension + X2 dimension equals: P dimension.
	self
		assert: X1 ambient dimension + X2 ambient dimension
		equals: P ambient dimension.
	self
		assert: (X1 pointsCountOver: ZZ / 3) * (X2 pointsCountOver: ZZ / 3)
		equals: (P pointsCountOver: ZZ / 3).
	self assert: (P satisfies: (5 , 2 , 6 , 2 , 6) % 7)
]

{ #category : #affine }
AlgebraicGeometryTest >> testAffineSchemeCreation [
	| A x y z X Y |
	A := AffineSpace new: 3 over: QQ.
	x := A coordinateRing x.
	y := A coordinateRing y.
	z := A coordinateRing z.
	X := A subscheme: x - y.
	Y := X subscheme: {(x raisedTo: 2) - (z raisedTo: 3). (y raisedTo: 3) - (z raisedTo: 4)}.
	self assert: X ambient equals: A.
	self assert: Y ambient equals: A
]

{ #category : #affine }
AlgebraicGeometryTest >> testAffineSpace [
	| K A |
	K := PrimeField new: 23.
	A := AffineSpace new: 3 over: K.
	self assert: A dimension = 3.
	self assert: A scalars = K.
	self assert: A coordinateRing = (K polynomialsIn: 3).
	self assert: A ambient = A.
	self assert: A coordinateRing spec = A
]

{ #category : #conics }
AlgebraicGeometryTest >> testConicCoefficients [
	self
		assert: (Conic coefficients: 1 , 2 , 3 , 4 , 5 , 6) coefficients
		equals: 1 , 2 , 3 , 4 , 5 , 6.
	self
		assert:
			(Conic
				polynomial:
					(QQ polynomialsIn: 3)
						!
							[ :x :y :z | (x raisedTo: 2) + (x * y * 5) + (y raisedTo: 2) + (z raisedTo: 2) ])
				coefficients
		equals: 1 , 5 , 0 , 1 , 0 , 1
]

{ #category : #conics }
AlgebraicGeometryTest >> testConicDeterminant [
	self
		assert: (Conic coefficients: 1 , 2 , 3 , 4 , 5 , 6) determinant
		equals: 41 / 4
]

{ #category : #conics }
AlgebraicGeometryTest >> testConicIsSmooth [
	self assert: (Conic coefficients: 1 , -1 , 0) isSmooth not.
	self
		assert: (Conic coefficients: (1 , 1 , 1 , 1 , 1 , 0) % 2) isSmooth
]

{ #category : #general }
AlgebraicGeometryTest >> testDifference [
	| A x y C X2 D O |
	A := AffineSpace new: 2 over: QQ.
	x := A coordinateRing x.
	y := A coordinateRing y.
	C := A subscheme: x * y.	"union of x-axis and y-axis"
	X2 := A subscheme: (x raisedTo: 2).	"y-axis with double multiplicity"
	D := X2 - C.	"y-axis with multiplicity 1"
	self assert: D ideal equals: A coordinateRing * x.
	O := A
		subscheme:
			{x.
			y}.
	D := C - O.
	self assert: D equals: C.
	self assert: (C - A) isEmpty	"removing the ambient space removes all"
]

{ #category : #general }
AlgebraicGeometryTest >> testEllipticCurvesAreSmooth [
	| R x y C |
	R := QQ polynomialsIn: #(x y z).
	x := R x.
	y := R y.
	C := (R / ((x raisedTo: 3) - (x*3) + 3 - (y raisedTo: 2) homogenizedIn: 3) )proj.
	self assert: C isSmooth.
	C := (R / ((x raisedTo: 3) + x - (y raisedTo: 2) homogenizedIn: 3) ) proj.
	self assert: C isSmooth.
	C := (R / ((x raisedTo: 3) - x - (y raisedTo: 2) homogenizedIn: 3)) proj.
	self assert: C isSmooth
]

{ #category : #general }
AlgebraicGeometryTest >> testEmpty [
	| A X |
	A := QQ polynomialsIn: #(x y z).
	X := (A / {A continuantOfOrder: 2. A continuantOfOrder: 3}) spec.
	self assert: X isEmpty
]

{ #category : #general }
AlgebraicGeometryTest >> testEqualVarietiesDifferentIdeals [
	| A x I I2 V V2 |
	A := QQ polynomials.
	x := A x.
	I := A * {x}.
	I2 := A * {(x raisedTo: 2)}.
	V := I variety.
	V2 := I2 variety.
	self assert: V equals: V2.
	self assert: I ~= I2
]

{ #category : #general }
AlgebraicGeometryTest >> testEqualVarietiesDifferentIdeals2 [
	| A x y I I2 V V2 |
	A := QQ polynomialsIn: #(x y).
	x := A x.
	y := A y.
	I := A
		*
			{x.
			y}.
	I2 := A
		*
			{(x raisedTo: 2).
			y}.
	V := I variety.
	V2 := I2 variety.
	self assert: V equals: V2.
	self assert: I ~= I2
]

{ #category : #general }
AlgebraicGeometryTest >> testFinite [
	| A x y X |
	A := QQ polynomialsIn: #(x y).
	x := A x.
	y := A y.
	X := (A / {x*x - 1. y*y - (x*x) - 3}) spec.
	self assert: X isFinite
]

{ #category : #general }
AlgebraicGeometryTest >> testIntersection [
	| A x y V V2 W |
	A := QQ polynomialsIn: #(x y).
	x := A x.
	y := A y.
	V := (A / {y}) spec.
	V2 := (A / {x*x - 1} ) spec.
	'W := V ï V2'.
	self assert: (W satisfies: 1 , 0).
	self assert: (W satisfies: 0 , 1) not
]

{ #category : #general }
AlgebraicGeometryTest >> testLinearSubspaceAsAlgebraicVariety [
	| S V |
	S := ((QQ raisedTo: 3) grassmannian: 2) atRandomBits: 10.
	V := S asAlgebraicVariety.
	self assert: V dimension + 1 equals: S dimension.
	self assert: (V satisfies: (S e: 1)).
	self assert: (V satisfies: (S e: 2))
]

{ #category : #general }
AlgebraicGeometryTest >> testLocalAndGlobalDimension [
	"'A Singluar Introduction to Commutative Algebra', Example A.8.4 (local and global dimension)."

	| R I X |
	R := QQ polynomialsIn: #(x y z).
	I := R
		*
			(R
				generate: [ :x :y :z | 
					{(x * z).
					(y * z)} ]).
	X := (R / I) spec.
	self assert: X dimension equals: 2.
	self assert: (X ! (0 , 0 , 0)) localRing dimension equals: 2.
	self assert: (X ! (1 , 0 , 0)) localRing dimension equals: 2.
	self assert: (X ! (0 , 0 , 1)) localRing dimension equals: 1
]

{ #category : #general }
AlgebraicGeometryTest >> testMorphismsOfProjectiveVarieties [
	"'A Singular Introduction To Commutative Algebra', Example A.6.8 (morphisms of projective varieties)."

	| P A x y z X f1 f2 f3 I J Y phi Z |
	P := ProjectiveSpace new: #(x y z) over: CC.	"å^2à"
	A := P coordinateRing.	"à[x,y,z]"
	x := A x.
	y := A y.
	z := A z.
	X := P
		subscheme: {((z raisedTo: 3) - (x * (y raisedTo: 2)) + (y raisedTo: 3))}.
	f1 := x * z.
	f2 := x * y.
	f3 := (x raisedTo: 2) + (y * z).
	"In order for (f1,f2,f3) to define a projective morphism (not just a rational map) it must never be zero at any point of X, this means the intersection of X with V(J) must be empty:"
	I := X ideal.
	J := A
		*
			{f1.
			f2.
			f3}.
	self assert: (I + J) dimension equals: 0.
	Y := P subscheme: J.
	self assert: '(X ï Y) isEmpty'.
	phi := X
		to: P
		representatives:
			{f1.
			f2.
			f3}.
	"The image is a curve of degree 6:"
	Z := phi image.
	self assert: Z isCurve.
	self assert: Z degree equals: 6
]

{ #category : #general }
AlgebraicGeometryTest >> testMultiplicity [
	"Example from Sage documentation."

	| A X q1 q2 |
	A := AffineSpace new: 4 over: QQ.
	X := A
		subscheme:
			A coordinateRing
				! [ :x :y :z :w | 
					{(z * y - (x raisedTo: 7)).
					(w - (2 * z))} ].
	q1 := X ! (1 , (1 / 3) , 3 , 6).
	q2 := X ! (0 , 0 , 0 , 0).
	self assert: q1 multiplicity equals: 1.
	self assert: q2 multiplicity equals: 2
]

{ #category : #general }
AlgebraicGeometryTest >> testMultiplicity2 [
	"Example from Sage documentation."

	| P X q1 q2 q3 |
	P := ProjectiveSpace new: 4 over: QQ.
	X := P
		subscheme:
			P coordinateRing
				! [ :x :y :z :w :t | 
					{((y raisedTo: 2) - (x * t)).
					((w raisedTo: 7) - (t * w * (x raisedTo: 5)) - (z raisedTo: 7))} ].
	q1 := X ! (0 , 0 , 1 , 1 , 1).
	self assert: q1 multiplicity equals: 1.
	q2 := X ! (1 , 0 , 0 , 0 , 0).
	self assert: q2 multiplicity equals: 3.
	q3 := X ! (0 , 0 , 0 , 0 , 1).
	self assert: q3 multiplicity equals: 7
]

{ #category : #general }
AlgebraicGeometryTest >> testMultiplicity3 [
	"Example from Sage documentation."

	| P X q |
	P := ProjectiveSpace new: 3 over: CC.
	X := P
		subscheme:
			P coordinateRing
				! [ :x :y :z :w | (z raisedTo: 5) * (x raisedTo: 2) * w - (y raisedTo: 8) ].
	q := X ! (2 , 0 , 0 , 1).
	self assert: q multiplicity equals: 5
]

{ #category : #general }
AlgebraicGeometryTest >> testMultiplicityAndTangentCone [
	"'A Singular Introduction to Commutative Algebra', Example A.8.5."

	| R C T p |
	R := QQ polynomialsIn: #(x y).
	C := (R / (R ! [ :x :y | (x raisedTo: 3) - y squared ])) spec.
	p := C ! (0 , 0).
	self assert: p multiplicity equals: 2.
	T := (R / (R ! [ :x :y | y raisedTo: 2 ])) spec.
	self assert: p tangentCone equals: T
	"	L := (R / (R ! [:x :y| 100 atRandom * x + (100 atRandom * y)])) spec
		...
		"
]

{ #category : #general }
AlgebraicGeometryTest >> testNotEmpty [
	| A x y X |
	A := QQ polynomialsIn: #(x y).
	x := A x.
	y := A y.
	X := 'A  / {x*x - 1. y*y - (x*x) - 3} :: spec'.
	self assert: X isEmpty not
]

{ #category : #general }
AlgebraicGeometryTest >> testNotFinite [
	| A x y X |
	A := QQ polynomialsIn: #(x y).
	x := A x.
	y := A y.
	X := (A / {y*y - (x*x) - 3} )spec.
	self assert: X isFinite not
]

{ #category : #'finite rings' }
AlgebraicGeometryTest >> testProductRingHomogeneousTuplesBug [
	"This tests a bug that makes Tuple>>~ not an equivalence relation (transitivity is broken)."
	| A p1 p2 c1 c2 |
	A := 'ZZ/2 ◊ (ZZ/2)'.
	p1 := A tuple: {A ! {1. 1}. A ! {1. 1}}.
	p2 := A tuple: {A ! {0. 1}. A ! {0. 1}}.
	self assert: p1 ~ p2.
	'c1 := A^2 count: [:each| each isZero not and: [each ~ p1]].
		c2 := A^2 count: [:each| each isZero not and: [each ~ p2]]'.
	self assert: c1 = c2
]

{ #category : #affine }
AlgebraicGeometryTest >> testProjectiveClosure [
	"From Magma Handbook example Scheme_projective-closure (H118E23)."

	| A1 u v X PX X2 |
	A1 := AffineSpace new: #(u v) over: ZZ / 5.
	u := A1 coordinateRing x: #u.
	v := A1 coordinateRing x: #v.
	X := A1 subscheme: (u raisedTo: 2) - (v raisedTo: 5).
	PX := X projectiveClosure.
	self assert: (PX patch: 3) equals: X.
	X2 := PX patch: 2.
	self assert: X2 projectiveClosure equals: X projectiveClosure
]

{ #category : #affine }
AlgebraicGeometryTest >> testProjectiveEmbedding [
	| A1 u v X PX affinePointsEmbedded projectivePoints |
	A1 := AffineSpace new: #(u v) over: ZZ / 5.
	u := A1 coordinateRing x: #u.
	v := A1 coordinateRing x: #v.
	X := A1 subscheme: (u raisedTo: 2) - (v raisedTo: 5).
	PX := X projectiveClosure.
	affinePointsEmbedded := X points asSet apply: X projectiveEmbedding.
	projectivePoints := PX points asSet.
	self assert: projectivePoints >= affinePointsEmbedded.
	"the projective scheme has one more point at infinity:"
	self
		assert: affinePointsEmbedded size + 1
		equals: projectivePoints size
]

{ #category : #'finite rings' }
AlgebraicGeometryTest >> testProjectiveLineOverFiniteRing [
	| P |
	P := ProjectiveLine over: ZZ / 6.
	"P(Z/6Z) has 12 points: [0:1], [1:1], [2:1], [3:1], [4:1], [5:1], [1:2], [3:2], [5:2], [1:3], [2:3] and [1:0] (Henri Cohen, 'A Course in Computational Algebraic Number Theory', 478p)"
	self assert: P points size equals: 12.
	self assert: (Iterator on: P points performing: #do:) size equals: 12
]

{ #category : #'finite rings' }
AlgebraicGeometryTest >> testProjectiveLineOverFiniteRing2AsDirectProduct [
	| P |
	P := 'ProjectiveLine over: ZZ/2 ◊ (ZZ/2)'.	"isomorphic to ZZ/2[x]/<x(x+1)>"
	self assert: P points size equals: 9.
	self assert: (Iterator on: P points performing: #do:) size equals: 9
]

{ #category : #'finite rings' }
AlgebraicGeometryTest >> testProjectiveLineOverFiniteRing2AsQuotient [
	| R P |
	R := (ZZ / 2) polynomials.
	R := R / (R x * (R x + 1)).	"isomorphic to ZZ/2 ◊ (ZZ/2)"
	P := ProjectiveLine over: R.
	self assert: P points size equals: 9.
	self assert: (Iterator on: P points performing: #do:) size equals: 9
]

{ #category : #'finite rings' }
AlgebraicGeometryTest >> testProjectiveLineOverFiniteRing4 [
	| P |
	'P := ProjectiveLine over: ZZ/4 ◊ (ZZ/4)'.
	self assert: P points size equals: 36.
	self assert: (Iterator on: P points performing: #do:) size equals: 36
]

{ #category : #'finite rings' }
AlgebraicGeometryTest >> testProjectiveLineOverFiniteRing5 [
	| P |
	P := 'ProjectiveLine over: ZZ/2 ◊ (ZZ/2) ◊ (ZZ/2)'.
	self assert: P points size = 27.
	self assert: (Iterator on: P points performing: #do:) size = 27
]

{ #category : #'finite rings' }
AlgebraicGeometryTest >> testProjectiveLineOverFiniteRing6 [
	| R P |
	R := (ZZ / 2) polynomials.
	R := R / ((R x raisedTo: 3) - R x).
	P := ProjectiveLine over: R.
	self assert: P points size equals: 18.
	self assert: (Iterator on: P points performing: #do:) size equals: 18
]

{ #category : #projective }
AlgebraicGeometryTest >> testProjectivePlaneCurveArithmeticGenus [
	| R f C |
	R := ZZ / 5 polynomialsIn: 3.
	f := R
		! [ :x :y :z | 
			(y raisedTo: 2) * (z raisedTo: 7) - (x raisedTo: 9)
				- (x * (z raisedTo: 8)) ].
	C := ProjectivePlaneCurve polynomial: f.
	self assert: C arithmeticGenus equals: 28
	"self assert: C genus = 4"
]

{ #category : #projective }
AlgebraicGeometryTest >> testProjectivePlaneOverFiniteField [
	| P |
	P := ProjectiveSpace new: 2 over: ZZ / 5.
	self assert: P points size equals: 31.
	self assert: (Iterator on: P points performing: #do:) size equals: 31
]

{ #category : #projective }
AlgebraicGeometryTest >> testProjectivePlaneOverFiniteRing [
	| P |
	P := ProjectiveSpace new: 2 over: ZZ / 4.
	self assert: P points size equals: 28
	"this plane has 28 points and 28 lines (falling into 7 neighbour classes of size 4), each line has 6 points and each point is on 6 lines"
]

{ #category : #projective }
AlgebraicGeometryTest >> testProjectiveSchemeAffinePatches [
	| E p a |
	E := EllipticCurve cremona37a.
	p := E ! (2,-3).
	a := p dehomogenizedIn: 2.
	"the affine point is in the second standard affine patch:"
	self assert: (E patch: 2) == a codomain.
	"and when we homogenize again, the same projective embedding is used and come back to the same projective point on exactly the same projective curve:"
	self assert: a homogenized = p.
	self assert: a homogenized codomain == E
]

{ #category : #projective }
AlgebraicGeometryTest >> testProjectiveSchemeDegree [
	"Example from Sage documentation."
	| P X |
	P := ProjectiveSpace new: 5 over: QQ.
	'X := P subscheme: (P coordinateRing ! [:x :y :z :w :t :u| x^7 + (x*y*z*(t^4)) - (u^7)])'.
	self assert: X degree = 7
]

{ #category : #projective }
AlgebraicGeometryTest >> testProjectiveSchemeDegree2 [
	"Example from Sage documentation."
	| P X |
	P := ProjectiveSpace new: 3 over: ZZ/13.
	'X := P subscheme: (P coordinateRing ! [:x :y :z :w| {y^3 - (w^3). x + (7*z)}])'.
	self assert: X degree = 3
]

{ #category : #projective }
AlgebraicGeometryTest >> testProjectiveSchemeDegree3 [
	"Example from Sage documentation."
	| P X |
	P := ProjectiveSpace new: 4 over: QQ.
	'X := P subscheme: (P coordinateRing ! [:x :y :z :w :u| {x^7 - (y*(z^3)*(w^2)*u). w*(z^2) - (y*(u^2)). z^3 + (y^3)}])'.
	self assert: X degree = 63
]

{ #category : #projective }
AlgebraicGeometryTest >> testProjectiveSpace [
	| K P |
	K := PrimeField new: 23.
	P := ProjectiveSpace new: 3 over: K.
	self assert: P dimension = 3.
	self assert: P scalars = K.
	self assert: P coordinateRing = (K polynomialsIn: 4).
	self assert: P ambient = P.
	self assert: P coordinateRing proj = P
]

{ #category : #projective }
AlgebraicGeometryTest >> testProjectiveSpaceOverFiniteField [
	| P S |
	P := ProjectiveSpace new: 1 over: ZZ/3.
	S := P points.
	self assert: S size = 4.
	self assert: S asSet size = 4.
	S := P pointsOver: (ZZ/3 extensionDegree: 2).
	self assert: S size = 10.
	self assert: S asSet size = 10
]

{ #category : #'rational maps' }
AlgebraicGeometryTest >> testRationalMap [
	"Example from Magma handbook Scheme_map-creation (H118E32)."
	| A1 A2 x y f X |
	A1 := AffineSpace new: #(t) over: QQ.
	A2 := AffineSpace new: #(x y) over: QQ.

	f := A1 to: A2 evaluatingWithArguments: [:t| {(t raisedTo: 3) + t. ((t raisedTo: 2) - 3)}].

	self assert: f domain = A1.
	self assert: f codomain = A2.

	x := A2 coordinateRing x.
	y := A2 coordinateRing y.
	X := A2 subscheme: {(x raisedTo: 2)* -1 + (y raisedTo: 3) + ((y raisedTo: 2)*11) + (y*40) + 48}.
	self assert: f image = X
]

{ #category : #'rational maps' }
AlgebraicGeometryTest >> testRationalMap2 [
	"Example from Cox's IVA pag. 234. Parametrization of the tangent surface of the twisted cubic."
	| A2 A3 x y z f X |
	A2 := AffineSpace new: #(t u) over: QQ.
	A3 := AffineSpace new: 3 over: QQ.

	'f := A2 to: A3 evaluatingWithArguments: [:t :u| {t + u. t^2 + (t*u*2). t^3 + (t^2*u*3)}]'.

	x := A3 coordinateRing x.
	y := A3 coordinateRing y.
	z := A3 coordinateRing z.
	X := 'A3 subscheme: {x^3*z - (x*y^2*(3/4)) - (x*y*z*(3/2)) + (y^3) + (z^2*(1/4))}'.
	self assert: f image = X
]

{ #category : #'rational maps' }
AlgebraicGeometryTest >> testRationalMapAffineExample [
	"From lecture notes MIT 18.782 Introduction to Arithmetic Geometry, Lecture #15, Fall 2013, 10/29/2013, Example 15.19."
	| A2 x y X A1 phi phi2 phiInv |
	A2 := AffineSpace new: 2 over: CC.
	x := A2 coordinateRing x.
	y := A2 coordinateRing y.
	'X := A2 subscheme: x^2 + (y^2) - 1'.
	A1 := AffineSpace new: 1 over: CC.
	phi := X to: A1 evaluatingWithArguments: [:x0 :y0| {y0 / (x0 + 1)}].
	phi2 := X to: A1 evaluatingWithArguments: [:x0 :y0| {1 - x0 / y0}].
	self assert: phi = phi2.
	phiInv := A1 to: X evaluatingWithArguments: [:t| {1 - (t raiseTo:2) / (1 + (t raiseTo: 2)). t*2 / (1 + (t raiseTo: 2))}].
	self assert: (phi î phiInv) isIdentity.
	self assert: phi isRegular not.
	self assert: phi isDominant.
"	self assert: phi isSurjective."
	self assert: phiInv isRegular not.
	self assert: phiInv isDominant.
"	self assert: phiInv isSurjective not"
]

{ #category : #'rational maps' }
AlgebraicGeometryTest >> testRationalMapImage [
	| A X X2 f |
	A := AffineSpace new: #(x y) over: QQ.
	"circle centered at (0,0):"
	'X := A subscheme: A coordinateRing ! [:x :y| x^2 + (y^2) - 1]'.
	"circle centered at: (1,2):"
	'X2 := A subscheme: A coordinateRing ! [:x :y| (x-1)^2 + ((y-2)^2) - 1]'.
	"translation by (1,2):"
	f := X to: A evaluatingWithArguments: [:x :y| {x+1. y+2}].
	self assert: f image = X2.
	"global translation by (1,2):"
	f := A to: A evaluatingWithArguments: [:x :y| {x+1. y+2}].
	self assert: (X apply: f) = X2
]

{ #category : #'rational maps' }
AlgebraicGeometryTest >> testRationalMapLinearMapConversion [
	| A2 A3 V2 V3 f f2 p f3 |
	A2 := AffineSpace new: 2 over: QQ.
	A3 := AffineSpace new: 3 over: QQ.
	V2 := QQ raiseTo: 2.
	V3 := QQ raiseTo: 3.

	f := 'V2 hom: V3 :: atRandomBits: 100'.
	f2 := (A2 hom: A3) ! f.

	p := V2 atRandomBits: 100.
	self assert: (f value: p) = (f2 value: p).

	f3 := (V2 hom: V3) ! f2.
	self assert: f = f3
]

{ #category : #'rational points' }
AlgebraicGeometryTest >> testRationalPointsOverFiniteField [
	| P C |
	P := ProjectiveSpace new: 2 over: ZZ / 7.
	C := 'P subscheme: P coordinateRing ! [:x :y :z| x^3 + (y^3) - (z^3)]'.
	self assert: C points size equals: 9.
	self assert: (Iterator on: C points performing: #do:) size equals: 9
]

{ #category : #general }
AlgebraicGeometryTest >> testReduced [
	| A R x y z X |
	A := AffineSpace new: 3 over: QQ.
	R := A coordinateRing.
	x := R x.
	y := R y.
	z := R z.
	X := A subscheme: {x*(y raisedTo: 3). (x raisedTo: 2)*z}.
	self assert: X isReduced not.
	self assert: X reduced = (A subscheme: {x*y. x*z})
]

{ #category : #general }
AlgebraicGeometryTest >> testRingHomomorphismSpec [
	| A B x y phi |
	A := QQ polynomialsIn: #(x y z).
	B := QQ polynomialsIn: #(x y).
	x := B x.
	y := B y.
	phi := A to: B evaluating: [:f| f value: {x-y. x. y}].
	self assert: phi spec domain = B spec.
	self assert: phi spec codomain = A spec.
	self assert: phi spec asRingHomomorphism = phi
]

{ #category : #general }
AlgebraicGeometryTest >> testSingularCubics [
	| R x y C |
	R := QQ polynomialsIn: #(x y z).
	x := R x.
	y := R y.
	C := (R / ((x raisedTo: 3) - (y raisedTo: 2) homogenizedIn: 3) ) proj.
	self assert: (C ! (1,1,1)) isSmooth.
	self assert: (C ! (0,0,1)) isSmooth not.
	self assert: C isSingular.
	C := (R / ((x raisedTo: 3) + (x raisedTo: 2) - (y raisedTo: 2) homogenizedIn: 3) ) proj.
	self assert: C isSingular
]

{ #category : #general }
AlgebraicGeometryTest >> testSmoothness [
	| R C |
	R := QQ polynomialsIn: #(x y).
	"cuspidal curve:"
	C := (R / (R ! [:x :y| (y raisedTo: 2) - (x raisedTo: 3)])) spec.
	self assert: C isSmooth not.
	self assert: C isSingular.
	self assert: (C ! (1 , 1)) isSmooth.
	self assert: (C ! (0 , 0)) isSmooth not
]

{ #category : #general }
AlgebraicGeometryTest >> testSmoothnessOverCC [
	| P R C |
	P := ProjectiveSpace new: 2 over: CC.
	R := P coordinateRing.
	C := P subscheme: R ! [ :x :y :z | x ].
	self assert: C isSingular not.
	C := P subscheme: R ! [:x :y :z| (y raisedTo: 2)*z - (x raisedTo: 3)].
	self assert: C isSingular.
	C := P subscheme: R ! [:x :y :z| (y raisedTo: 2)*z - (x raisedTo: 3) + (z raisedTo: 3)].
	self assert: C isSingular not
]

{ #category : #general }
AlgebraicGeometryTest >> testSmoothnessOverFiniteField [
	| P R C |
	P := ProjectiveSpace new: 2 over: ZZ/19.
	R := P coordinateRing.
	'C := P subscheme: R ! [:x :y :z| x^3 + (y^3) + (z^3)].
		self assert: C isSingular not.
		C := P subscheme: R ! [:x :y :z| x^4 - (x*(z^3))].
		self assert: C isSingular.
		C := P subscheme: R ! [:x :y :z| x^5 + (y^5*19) + (z^5)].
		self assert: C isSingular.
		C := P subscheme: R ! [:x :y :z| x^5 + (y^5*9) + (z^5)].
		self assert: C isSingular not'
]

{ #category : #general }
AlgebraicGeometryTest >> testSmoothnessOverQQ [
	| P C |
	P := ProjectiveSpace new: 2 over: QQ.
	C := P subscheme: P coordinateRing ! [:x :y :z| (x raisedTo: 3) - ((y raisedTo: 2)*z)].
	self assert: C isSingular
]

{ #category : #general }
AlgebraicGeometryTest >> testSpecZ [
	self assert: ZZ spec dimension = 1.
	self assert: ZZ spec isNoetherian.
	self assert: (ZZ spec includes: ZZ*5).
	self deny: (ZZ spec includes: ZZ*6).
	self assert: ZZ spec isInitial not.
	self assert: ZZ spec isTerminal
]

{ #category : #general }
AlgebraicGeometryTest >> testSpecZSubschemes [
	self assert: ZZ spec >= (ZZ / 2) spec.
	self assert: (ZZ / 10) spec >= (ZZ / 5) spec.
	self deny: (ZZ / 10) spec >= (ZZ / 3) spec.
	'self assert: (ZZ / 10) spec ï (ZZ / 15) spec = (ZZ / 5) spec'.
	'self assert: (ZZ / 10) spec ñ (ZZ / 15) spec = (ZZ / 30) spec'
]

{ #category : #'rational points' }
AlgebraicGeometryTest >> testSturmfelsExample1 [
	"Bernd Sturmfels, 'Ideals, Varieties and Macaulay 2', 1. A Curve in Affine 3-Space."

	| R x y I C C1 C2 |
	R := QQ polynomialsIn: #(x y z).	"default ordering is trevlex"
	x := R x.
	y := R y.
	"	z := R z."
	I := R
		*
			{((x raisedTo: 4) - (y raisedTo: 5)).
			((x raisedTo: 3) - (y raisedTo: 7))}.
	self
		assert: I groebnerBasis reduced printString
		equals: '{x^8 - x^3y^3, x^4y^2 - x^3, y^5 - x^4}'.
	C := I variety.
	self assert: C dimension equals: 1.
	self assert: C codimension equals: 2.
	self assert: C projectiveClosure degree equals: 28.
	C1 := C \ (R / R x) spec.
	self
		assert: C1
		equals:
			(R
				/
					{(x * (y raisedTo: 2) - 1).
					((y raisedTo: 5) - (x raisedTo: 4)).
					((x raisedTo: 5) - (y raisedTo: 3))}) spec.
	C2 := C - C1.	"NOTE: the article uses ideal saturation, and this is colon"
	self
		assert: C2
		equals:
			(R
				/
					{(x raisedTo: 3).
					(y raisedTo: 5)}) spec.
	self assert: C1 projectiveClosure degree equals: 13.
	self assert: C1 isReduced	"equivalent to C1 ideal = C1 ideal radical"
]

{ #category : #'rational points' }
AlgebraicGeometryTest >> testSturmfelsExample2 [
	"Bernd Sturmfels, 'Ideals, Varieties and Macaulay 2', 2. Intersecting Our Curve With a Surface."
	| R x y z C S theirunion ourpoints |
	R := QQ polynomialsIn: #(x y z). "default ordering is trevlex"
	x := R x.
	y := R y.
	z := R z.
'	C := (R / {x^4 - (y^5). x^3 - (y^7)}) spec.
	C := C \ (R / R x) spec. "this is C1 from example1"
	S := (R / (x^5 + (y^5) + (z^5) - 1)) spec'.
	theirunion := C ñ S.
	"In this case, the union's ideal coincides with the product of the ideals:"
	self assert: theirunion ideal = (C ideal * S ideal).
	"The intersection of the curve and the surface (whose defining ideal is the sum of the respective ideals):"
	ourpoints := C ï S.
	"We get a finite set of points:"
	self assert: ourpoints dimension = 0.
	"The number of points is 65:"
	self assert: ourpoints projectiveClosure degree = 65.
	"Each of the points is multiplicity-free:"
	self assert: ourpoints isReduced. "equivalent to the original: ourpoints reduced projectiveClosure degree = 65."
]

{ #category : #'tangent cone' }
AlgebraicGeometryTest >> testTangentCone [
	"'A Singular Introduction to Commutative Algebra', Example 5.5.13."

	| R I J X |
	R := QQ polynomialsIn: #(x y z).
	I := R
		*
			(R
				! [ :x :y :z | 
					{(y * z + (z raisedTo: 2) + (x raisedTo: 3)).
					((y raisedTo: 2) + (x * z) + (y raisedTo: 4))} ]).
	X := (R / I) spec.
	J := R
		*
			(R
				! [ :x :y :z | 
					{((y raisedTo: 2) + (x * z)).
					(y * z + (z raisedTo: 2)).
					(x * (z raisedTo: 2) - (y * (z raisedTo: 2)))} ]).
	self assert: (X ! (0 , 0 , 0)) tangentCone ideal equals: J
]

{ #category : #'tangent cone' }
AlgebraicGeometryTest >> testTangentCone2 [
	"M. Kreuzer, 'Computational Commutative Algebra', Example 6.5.27."

	| R J T I |
	R := QQ polynomialsIn: 4.
	J := R
		*
			(R
				generate: [ :x1 :x2 :x3 :x4 | 
					{(x1 * x2 - (x3 raisedTo: 2)).
					((x2 raisedTo: 2) - (x4 raisedTo: 5))} ]).
	T := (R / J) spec tangentConeAt: 0 , 0 , 0 , 0.
	I := R
		*
			(R
				generate: [ :x1 :x2 :x3 :x4 | 
					{(x1 * x2 - (x3 raisedTo: 2)).
					(x2 raisedTo: 2).
					(x2 * (x3 raisedTo: 2)).
					(x3 raisedTo: 4)} ]).
	self assert: T ideal equals: I
]

{ #category : #'tangent cone' }
AlgebraicGeometryTest >> testTangentConeAndTangentSpace [
	"Example from https://en.wikipedia.org/wiki/Tangent_cone."

	| A x y S o |
	A := AffineSpace new: #(x y) over: QQ.
	x := A coordinateRing x.
	y := A coordinateRing y.
	"this curve is singular at (0,0):"
	S := A subscheme: (x raisedTo: 2) + (x raisedTo: 3) - (y raisedTo: 2).
	o := S ! (0 , 0).
	"the tangent cone is the union of the two lines x = y and x = -y:"
	self assert: o tangentCone equals: (A subscheme: (x + y) * (x - y)).
	self assert: o tangentSpace equals: A
]

{ #category : #'rational points' }
AlgebraicGeometryTest >> testTwistedCubic [
	| P R M C |
	P := ProjectiveSpace new: 3 over: QQ.
	R := P coordinateRing.
	"R indeterminateNames: #(u v w t)"
	M := R
		matrix: 2 @ 3
		coefficients: (1 , 2 , 3 , 2 , 3 , 4 collect: [ :i | R x: i ]).
	C := P subscheme: (M minors: 2).
	self assert: C dimension equals: 1.
	self assert: C isSmooth
]

{ #category : #'rational points' }
AlgebraicGeometryTest >> testTwistedCubicDegree [
	"Twisted cubic in P^3 with homogeneous coordinates x,y,w,z."
	| A x y z w X |
	A := QQ polynomialsIn: #(x y z w).
	x := A x.
	y := A y.
	z := A z.
	w := A x: #w.
	X := (A / {(x raisedTo: 2) - (y*w). x*z - (y raisedTo: 2)} ) proj.
	"At this point X is still reducible, it is the union of a line x=y=0 and the twisted cubic:"
	self assert: X degree = 4.
	"To cut out X, we impose an additional equation x^3 - (z * (w^2)) = 0:"
	X := (A / {(x raisedTo: 2) - (y*w). x*z - (y raisedTo: 2). (x raisedTo: 3) - (z*(w raisedTo: 2))} ) proj.
	"But we get the twisted cubic (in some sense) 'counted with multiplicity 2', so the degree is 6"
	self assert: X degree = 6
]
