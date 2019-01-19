Class {
	#name : #AffineGeometryTest,
	#superclass : #TestCase,
	#category : #MathematicsTests
}

{ #category : #'as yet unclassified' }
AffineGeometryTest >> testAffineHull [
	| V v1 v2 H |
	V := 'QQ ^ 3'.
	v1 := (1,0,0).
	v2 := (2,2,2).
	H := V hull: {v1. v2}.
	self assert: H isLine.
	self assert: (H includes: v1).
	self assert: (H includes: v2)
]

{ #category : #'as yet unclassified' }
AffineGeometryTest >> testAffineHullEmpty [
	| V H |
	V := 'QQ ^ 3'.
	H := V hull: {}.
	self assert: H isEmpty.
	self assert: H dimension = -1.
	self assert: H size = 0
]

{ #category : #'as yet unclassified' }
AffineGeometryTest >> testAffineMapCollinearity [
	"Affine maps preserve collinearity."
	| A f p1 fp1 p2 fp2 p3 fp3 |
	A := 'QQ ^ 3'.
	f := (A automorphisms atRandomBits: 100) + (A atRandomBits: 100).
	"three collinear points:"
	p1 := (1,2,3) + (1,0,1). p2 := (2,4,6) + (1,0,1). p3 := (-1,-2,-3) + (1,0,1).
	self assert: (A hull: {p1.p2.p3}) isLine.
	"the imagees of the three collinear points must be collinear:"
	fp1 := f value: p1. fp2 := f value: p2. fp3 := f value: p3.
	self assert: (A hull: {fp1.fp2.fp3}) isLine
]

{ #category : #'as yet unclassified' }
AffineGeometryTest >> testAffineMapComposition [
	| X Y Z f g x |
	'X := QQ^3.
		Y := QQ^5.
		Z := QQ^4'.
	f := ((X hom: Y) atRandomBits: 1000) + (Y atRandomBits: 100).
	g := ((Y hom: Z) atRandomBits: 1000) + (Z atRandomBits: 100).
	x := X atRandomBits: 1000.
"	self assert: ((X hom: Z) includes: g î f)."
	self assert: (g î f value: x) = (g value: (f value: x)).
	self should: [f î g] raise: DomainError
]

{ #category : #'as yet unclassified' }
AffineGeometryTest >> testAffineMapEvaluating [
	| V f |
	V := 'QQ^3'.
	f := AffineMap from: V to: V evaluating: [:p| p*2 - (1,0,0)].
	self assert: (f value: (1,2,3)) = (1,4,6)
]

{ #category : #'as yet unclassified' }
AffineGeometryTest >> testAffineMapInverse [
	| A f |
	A := 'QQ^3'.
	f := (A automorphisms atRandomBits: 1000) + (A atRandomBits: 100).
	self assert: (f î f inverse) isIdentity.
	self assert: (f inverse î f) isIdentity
]

{ #category : #'as yet unclassified' }
AffineGeometryTest >> testAffineSubspaceParallelism [
	| V A B C |
	V := 'QQ ^ 3'.
	A := (V span: {(1,1,1)}) + (5,0,0).
	B := (V span: {(1,1,1). (1,0,0)}) + (10,0,0).
	C := (V span: {(1,1,2). (0,1,0)}) + (10,0,0).
	self assert: A || B.
	self assert: B || A.
	self deny: A || C.
	self deny: B || C
]
