Class {
	#name : #GraphTest,
	#superclass : #TestCase,
	#category : #MathematicsTests
}

{ #category : #'as yet unclassified' }
GraphTest >> testAutomorphismsK3 [
	"Aut(K3) = Sym(3)"
	| G A |
	G := Graph K: 3.
	A := G automorphisms.
	self assert: A = A ambient

]

{ #category : #'as yet unclassified' }
GraphTest >> testAutomorphismsP3 [
	"Aut(P3) = {id, (1 3)}"
	| G A |
	G := Graph P: 3.
	A := G automorphisms.
	self assert: A = (PermutationGroup on: G values generators: {#((1 3))})
]

{ #category : #'as yet unclassified' }
GraphTest >> testCartesianProduct [
	| G H |
	G := Graph unordered addEdge: 1 -> 2; yourself.
	H := 'G ◊ G'.
	self assert: H size = 4.
	self assert: H numberOfEdges = 4
]

{ #category : #'as yet unclassified' }
GraphTest >> testChromaticNumber [
	| G |
	G := Graph unordered add: 1; add: 2; add: 3; yourself. 
	self assert: G chromaticNumber = 1. "edgeless graph"
	self assert: (Graph K: 3) chromaticNumber = 3.
	self assert: (Graph C: 5) chromaticNumber = 3.
	self assert: (Graph C: 6) chromaticNumber = 2.
	self assert: (Graph W: 6) chromaticNumber = 4.
	self assert: (Graph W: 5) chromaticNumber = 3.
	self assert: (Graph S: 6) chromaticNumber = 2
]

{ #category : #'as yet unclassified' }
GraphTest >> testChromaticPolynomialComplete [
	| x |
	x := ZZ polynomials x.
	self assert: (Graph K: 3) chromaticPolynomial = (x*(x-1)*(x-2))
]

{ #category : #'as yet unclassified' }
GraphTest >> testChromaticPolynomialCylic [
	| x n |
	x := ZZ polynomials x.
	n := 4 atRandom.
	'self assert: (Graph C: n) chromaticPolynomial = (x-1^n + ((-1)^n * (x-1)))'
]

{ #category : #'as yet unclassified' }
GraphTest >> testChromaticPolynomialPath [
	| x n |
	x := ZZ polynomials x.
	n := 4 atRandom + 1.
	'self assert: (Graph P: n) chromaticPolynomial = (x-1^(n-1)*x)'
]

{ #category : #'as yet unclassified' }
GraphTest >> testComplement [
	| G H |
	G := Graph unordered addEdges: {#a -> #b. #b -> #c. #d -> #e}; yourself.
	H := G complement.
	self assert: (G ñ H) isComplete.
	self assert: '(G ï H) isEdgeless'.
	self assert: H complement = G
]

{ #category : #'as yet unclassified' }
GraphTest >> testConnectedComponents [
	| G |
	G := Graph unordered addEdges: {#a -> #b. #b -> #c. #d -> #e}; yourself.
	self assert: G components size = 2.
	self assert: (G components collect: [:each| each order]) = #(2 3) asSet.
	self assert: G components anyOne components size = 1
]

{ #category : #'as yet unclassified' }
GraphTest >> testDistance [
	| G |
	G := Digraph unordered addEdges: {#a -> #b. #b -> #c. #d -> #e}; yourself.
	self assert: (G distanceFrom: #a to: #c) = 2.
	self assert: (G distanceFrom: #d to: #e) = 1.
	self assert: (G distanceFrom: #b to: #b) = 0.
	self assert: (G distanceFrom: #a to: #e) isInfinite
]

{ #category : #'as yet unclassified' }
GraphTest >> testEquals [
	| G H |
	G := Digraph ordered addEdges: {#a -> #b. #b -> #c. #c -> #a. #X -> #Y}; yourself.
	H := Digraph ordered addEdges: {#a -> #b. #b -> #c. #c -> #a}; yourself.
	self assert: G ~= H.
	H addEdge: #X -> #Y.
	self assert: G = H.
	self assert: G hash = H hash
]

{ #category : #'as yet unclassified' }
GraphTest >> testImplicit [
	| G |
	G := RootedDigraph unordered roots: {2 raiseTo: 3} children: [:each| each divisors copyWithout: each].
	self assert: G size = 4.
	self assert: G values asSet = #(1 2 4 8) asSet.
	self assert: G edges size = 6
]

{ #category : #'as yet unclassified' }
GraphTest >> testIntersection [
	| G H I |
	G := Digraph unordered addEdges: {#a -> #b. #b -> #c. #d -> #e. #x -> #b}; yourself.
	H := Digraph unordered addEdges: {#A -> #B. #b -> #c. #d -> #e. #X -> #X. #b -> #a}; yourself.
	I := 'G ï H'.
	self assert: I numberOfEdges = 2.
	self assert: (I hasEdge: #b -> #c).
	self assert: (I hasEdge: #d -> #e)
]

{ #category : #'as yet unclassified' }
GraphTest >> testIsComplete [
	| G |
	G := Digraph unordered.
	G addEdges: {#a -> #b. #b -> #a. #b -> #c. #a -> #c. #c -> #a}.
	G := G reflexive.
	self assert: G isComplete not.
	G addEdge: #c -> #b.
	self assert: G isComplete
]

{ #category : #'as yet unclassified' }
GraphTest >> testIsConnected [
	| G |
	G := Graph unordered addEdges: {#a -> #b. #b -> #c. #d -> #e}; yourself.
	self assert: G isConnected not.
	G addEdge: #e -> #a.
	self assert: G isConnected
]

{ #category : #'as yet unclassified' }
GraphTest >> testIsCyclic [
	| G |
	G := Digraph unordered addEdges: {#a -> #b. #b -> #c. #d -> #e}; yourself.
	self assert: G isCyclic not.
	G addEdge: #e -> #a.
	self assert: G isCyclic not.
	G addEdge: #c -> #a.
	self assert: G isCyclic
]

{ #category : #'as yet unclassified' }
GraphTest >> testIsSimple [
	| G |
	G := Digraph ordered addEdges: {#a -> #b. #b -> #c. #d -> #e}; yourself.
	self assert: G isSimple.
	G addEdge: #c -> #b.
	self assert: G isSimple.
	G addEdge: #c -> #b.
	self assert: G isSimple not
]

{ #category : #'as yet unclassified' }
GraphTest >> testIsSimple2 [
	| G |
	G := Digraph ordered addEdges: {#a -> #b. #b -> #c. #d -> #e}; yourself.
	self assert: G isSimple.
	G addEdge: #c -> #c.
	self assert: G isSimple not "a graph with a loop is not simple"
]

{ #category : #'as yet unclassified' }
GraphTest >> testIsomorphism [
	| G H |
	G := Graph unordered.
	5 timesRepeat: [G addEdge: 5 atRandom -> 5 atRandom].
	H := G shuffled.
	self assert: G ~ H.
	G := Graph C: 5. "pentagon"
	H := G copy.
	G addEdges: {1 -> 6. 6 -> 2}. "make a little triangle"
	H addEdges: {1 -> 6. 6 -> 3}. "same, but skip vertex 2 in the middle"
	H := H shuffled.
	self deny: G ~ H
]

{ #category : #'as yet unclassified' }
GraphTest >> testPetersenGraph [
	| G |
	G := Graph petersen.
	self assert: G nodes size = 10.
	self assert: G edges size = 15.
	self assert: G isCubic.
	self assert: G radius = 2.
	self assert: G diameter = 2.
"	self assert: G girth = 5"
]

{ #category : #'as yet unclassified' }
GraphTest >> testShortestPath [
	| G |
	G := Digraph unordered.
	G addEdges: {#a -> #b. #b -> #a. #b -> #c. #a -> #c. #c -> #a}.
	self assert: (G shortestPathFrom: #c to: #b) asArray = #(a b).
	G addEdge: #c -> #b.
	self assert: (G shortestPathFrom: #c to: #b) asArray = #(b)
]

{ #category : #'as yet unclassified' }
GraphTest >> testTransposed [
	| G T |
	G := Digraph unordered addEdges: {#a -> #b. #b -> #c. #d -> #e}; yourself.
	T := G transposed.
	self assert: (G hasEdge: #b -> #c).
	self assert: (G hasEdge: #c -> #b) not.
	self assert: (T hasEdge: #b -> #c) not.
	self assert: (T hasEdge: #c -> #b)
]

{ #category : #'as yet unclassified' }
GraphTest >> testTuttePolynomial [
	| G P x y T |
	G := Graph ordered addEdges: {1->2. 2->3. 3->4. 4->1. 1->3}; yourself.
	P := ZZ polynomialsIn: #(x y).
	x := P x.
	y := P y.
	T := 'x*(x^2 + (x+y)) + (x^2 + (x+y)) + (x*y + (y^2))'.
	self assert: G tuttePolynomial = T
]

{ #category : #'as yet unclassified' }
GraphTest >> testTuttePolynomial2 [
	| G P x y T |
	G := Graph ordered addEdges: {1->2. 2->3. 3->4. 4->1. 1->3}; yourself.
	P := ZZ polynomialsIn: #(x y).
	x := P x.
	y := P y.
	T := 'x*(x^2 + (x+y)) + (x^2 + (x+y)) + (x*y + (y^2))'.
	self assert: G tuttePolynomial = T
]

{ #category : #'as yet unclassified' }
GraphTest >> testTuttePolynomialK3 [
	| G P x y T |
	G := Graph K: 3.
	P := ZZ polynomialsIn: #(x y).
	x := P x.
	y := P y.
	T := 'x^2 + x + y'.
	self assert: G tuttePolynomial = T
]

{ #category : #'as yet unclassified' }
GraphTest >> testTuttePolynomialK4 [
	| G P x y T |
	G := Graph K: 4.
	P := ZZ polynomialsIn: #(x y).
	x := P x.
	y := P y.
	T := 'x^3 + (x^2*3) + (x*2) + (x*y*4) + (y*2) + (y^2*3) + (y^3)'.
	self assert: G tuttePolynomial = T
]

{ #category : #'as yet unclassified' }
GraphTest >> testUndirectedEdgeContraction [
	| G |
	G := Graph ordered addEdges: {1->2. 2->3. 3->4. 4->1. 1->3}; yourself.
	self assert: G edges size = 5.
	self assert: (G / (1->2)) edges size = 4.
	self assert: (G / (1->2) / ((1->2)->3)) edges size = 3
]

{ #category : #'as yet unclassified' }
GraphTest >> testUnion [
	| G |
	G := Digraph unordered addEdges: {#a -> #b. #b -> #c. #d -> #e. #x -> #b}; yourself.
	self assert: (G ñ G transposed) = G symmetric
]
