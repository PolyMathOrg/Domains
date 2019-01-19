Class {
	#name : #SimplicialComplexTest,
	#superclass : #TestCase,
	#category : #MathematicsTests
}

{ #category : #'as yet unclassified' }
SimplicialComplexTest >> test2Sphere [
	| X |
	X := SimplicialComplex sphere: 2.
	self assert: X dimension = 2.
	self assert: X fVector = (1,4,6,4)
]

{ #category : #'as yet unclassified' }
SimplicialComplexTest >> test5Sphere [
	| X |
	X := SimplicialComplex sphere: 5.
	self assert: X dimension = 5.
	self assert: X fVector = (1,7,21,35,35,21,7)
]

{ #category : #'as yet unclassified' }
SimplicialComplexTest >> testAlexanderDual [
	| X Y |
	X := SimplicialComplex faces: #((0 1) (1 2) (2 3) (3 0)).
	self assert: X dual dual = X.
	Y := SimplicialComplex faces: #((1 3) (0 2)).
	self assert: X dual = Y.
	self assert: X dual nonfaces = X complement facets
]

{ #category : #'as yet unclassified' }
SimplicialComplexTest >> testChainComplex [
	"Jeff Erickson, 'Computational Topology', Example 17.7."
	| S2 C |
	S2 := SimplicialComplex facets: ((Simplex vertices: #(w x y z)) faces: 2).
	C := S2 chainComplexOver: ZZ.
	self assert: (C cycles: 1) rank = 3.
	self assert: (C boundaries: 0) rank = 3.
	self assert: (C boundaries: 1) = (C cycles: 0).
	self assert: C betti = #(1 0 1)
]

{ #category : #'as yet unclassified' }
SimplicialComplexTest >> testEulerCharacteristic [
	| X |
	X := SimplicialComplex torus.
	self assert: X euler = 0.
	X := SimplicialComplex sphere: 2.
	self assert: X euler = 2.
	X := SimplicialComplex kleinBottle.
	self assert: X euler = 0.
	X := SimplicialComplex realProjectivePlane.
	self assert: X euler = 1
]

{ #category : #'as yet unclassified' }
SimplicialComplexTest >> testJoin [
	| S X |
	S := SimplicialComplex faces: #((0) (1)).
	X := S * S * S * S * S * S * S * S.
	self assert: X vertices size = 16.
	self assert: X facets size = 256

]

{ #category : #'as yet unclassified' }
SimplicialComplexTest >> testMinimalNonFaces [
	| X |
	X := SimplicialComplex faces: #((1 3) (1 2)).
	self assert: X nonfaces = {Simplex vertices: #(2 3)} asSet.
	X := SimplicialComplex faces: #((0 1) (1 2) (2 3) (3 0)).
	self assert: X nonfaces = {Simplex vertices: #(1 3). Simplex vertices: #(0 2)} asSet

]

{ #category : #'as yet unclassified' }
SimplicialComplexTest >> testMinimalNonFaces2 [
	| X MNF |
	X := SimplicialComplex faces: #((0 1 2) (0 2 3) (2 3 4) (1 2 4) (1 4 5) (0 3 6) (3 6 7) (4 5 7)).
	MNF := (#((3 4 7) (0 7) (0 4) (0 5) (3 5) (1 7) (2 5) (5 6) (1 3) (4 6) (2 7) (2 6) (1 6)) collect: [:each| Simplex vertices: each]) asSet.
	self assert: X nonfaces = MNF
]

{ #category : #'as yet unclassified' }
SimplicialComplexTest >> testProduct [
	| C T |
	"Circle:"
	C := SimplicialComplex faces: #((0 1) (1 2) (0 2)).
	"Torus:"
	T := 'C ◊ C'.
	self assert: T euler = 0.
	self assert: T vertices size = 9.
	self assert: T facets size = 18
]

{ #category : #'as yet unclassified' }
SimplicialComplexTest >> testSimplecialComplex [
	| S |
	S := SimplicialComplex facets: {{1. 2. 3}. {2. 4}. {3. 4}. {5}}.
	self assert: (S faces: 2) asSet size = 1.
	self assert: (S faces: 1) asSet size = 5.
	self assert: (S faces: 0) asSet size = 5
]

{ #category : #'as yet unclassified' }
SimplicialComplexTest >> testSimplex [
	| tetrahedron |
	tetrahedron := Simplex vertices: #(a b c d).
	self assert: tetrahedron dimension = 3.
	self assert: (tetrahedron faces: 2) size = 4.
	self assert: tetrahedron edges size = 6.
	self assert: (tetrahedron faces: 3) size = 1
]

{ #category : #'as yet unclassified' }
SimplicialComplexTest >> testSimplexComplement [
	| V |
	V := (0 to: 5).
	self assert: ((Simplex vertices: #(1 2 3)) complementIn: V) = (Simplex vertices: #(0 4 5)).
	self assert: ((Simplex vertices: #(0 1 3 4)) complementIn: V) = (Simplex vertices: #(2 5)).
	self assert: ((Simplex vertices: #(0 4 1 3 )) complementIn: V) = (Simplex vertices: #(2 5))
]

{ #category : #'as yet unclassified' }
SimplicialComplexTest >> testSimplexInclusion [
	| S S2 |
	S := Simplex new: (2 to: 10) atRandom.
	S2 := Simplex new: (0 to: S dimension) atRandom.
	self assert: S2 <= S
]

{ #category : #'as yet unclassified' }
SimplicialComplexTest >> testSimplexJoin [
	| A B |
	A := Simplex new: 2.
	B := Simplex new: 3.
	self assert: A*B ~ (Simplex new: 2+1+3+1-1)

]

{ #category : #'as yet unclassified' }
SimplicialComplexTest >> testSimplicalChainsBoundaryMap [
	| X d1 d2 |
	X := SimplicialComplex sphere: 2.
	d2 := X boundaryMap: 2 over: QQ.
	d1 := X boundaryMap: 1 over: QQ.
	self assert: d2 isZero not.
	self assert: d1 isZero not.
	self assert: (d1 î d2) isZero
]

{ #category : #'as yet unclassified' }
SimplicialComplexTest >> testSimplicialComplexExample [
	"Example from Herzog, 'Monomial Ideals', pag. 16."
	| X |
	X := SimplicialComplex on: (1 to: 5) faces: #((1 2 4) (1 2 5) (2 3) (3 4)).
	self assert: X facets = (#((1 2 4) (1 2 5) (2 3) (3 4)) collect: [:each| Simplex vertices: each]) asSet.
	self assert: X nonfaces = (#((1 3) (3 5) (4 5) (2 3 4)) collect: [:each| Simplex vertices: each]) asSet.
	self assert: X fVector = (1,5,7,2).
	self assert: X hVector = (1,2,0,-1)
]

{ #category : #'as yet unclassified' }
SimplicialComplexTest >> testSimplicialMap [
	| S T f |
	S := SimplicialComplex faces: #((0 2) (1 5) (3 4)).
	T := SimplicialComplex faces: #((0 2) (1 3)).
	f := S to: T map: ({0 -> 0. 1 -> 1. 2 -> 2. 3 -> 1. 4 -> 3. 5 -> 3} as: Dictionary).
	self assert: f image = T.
	self assert: f isSurjective.
	self assert: f isInjective not.
	self assert: f isIdentity not
]

{ #category : #'as yet unclassified' }
SimplicialComplexTest >> testStanleyReisnerIdealAndBack [
	| X |
	X := SimplicialComplex on: (1 to: 5) faces: #((1 2 4) (1 2 5) (2 3) (3 4)).
	self assert: X stanleyReisnerIdeal asSimplicialComplex = X
]

{ #category : #'as yet unclassified' }
SimplicialComplexTest >> testStanleyReisnerIdealAndBack2 [
	| X |
	X := SimplicialComplex on: (1 to: 5) faces: #((1 3 2) (3 4) (2 4) (5)).
	self assert: X stanleyReisnerIdeal asSimplicialComplex = X
]

{ #category : #'as yet unclassified' }
SimplicialComplexTest >> testStanleyReisnerIdealAndFacetIdealDuality [
	| X |
	X := SimplicialComplex on: (1 to: 5) faces: #((1 2 4) (1 2 5) (2 3) (3 4)).
	self assert: X dual stanleyReisnerIdeal = X complement facetIdeal
]

{ #category : #'as yet unclassified' }
SimplicialComplexTest >> testStanleyReisnerRing [
	| X R |
	X := SimplicialComplex faces: #((0 1) (1 2) (2 3) (3 0)).
	R := QQ polynomialsIn: #(x y z w).
	self assert: X stanleyReisnerRing relations generators asSet = (R generate: [:x :y :z :w| {y*w. x*z}]) asSet
]

{ #category : #'as yet unclassified' }
SimplicialComplexTest >> testTorus [
	| X |
	X := SimplicialComplex torus.
	self assert: X dimension = 2.
	self assert: X fVector = (1,7,21,14)
]
