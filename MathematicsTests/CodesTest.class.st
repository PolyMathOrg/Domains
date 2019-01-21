Class {
	#name : #CodesTest,
	#superclass : #TestCase,
	#category : #MathematicsTests
}

{ #category : #tests }
CodesTest >> testDual [
	| C |
	C := LinearCode
		subspace:
			((ZZ / 2 raisedTo: 5)
				span:
					{((0 , 0 , 0 , 0 , 0) % 2).
					((1 , 1 , 1 , 1 , 1) % 2)}).
	self assert: C dual size equals: C ambient size / C size.
	C dual
		do:
			[ :v | "check each codeword of the dual has an even number of 1's, because it must be perpendicular to 11111 (and 00000 of course)." self assert: (v count: [ :each | each = (1 % 2) ]) even ]
]

{ #category : #tests }
CodesTest >> testGolay24 [
	| C W x y |
	C := LinearCode G24.
	self assert: C isSelfDual.
	W := C weightEnumerator.
	x := W parent x.
	y := W parent y.
	self
		assert: W
		equals:
			(x raisedTo: 24) + ((x raisedTo: 16) * (y raisedTo: 8) * 759)
				+ ((x raisedTo: 12) * (y raisedTo: 12) * 2576)
				+ ((x raisedTo: 8) * (y raisedTo: 16) * 759) + (y raisedTo: 24)	"typo in neil's video 22:20"
]

{ #category : #tests }
CodesTest >> testHamming743 [
	| H7 |
	H7 := LinearCode H7.
	self assert: H7 isCyclic.
	self assert: H7 minimumDistance = 3.
	self assert: H7 weightDistribution = #(0 3 3 3 3 3 3 3 4 4 4 4 4 4 4 7) asBag.
	self assert: H7 dual minimumDistance = 4
]

{ #category : #tests }
CodesTest >> testHamming844 [
	| C P x y |
	C := LinearCode H8.
	self assert: C isSelfDual.
	self assert: C isSelfOrthogonal.
	self assert: C minimumDistance = 4.
	self assert: C dual minimumDistance = 4.
	P := ZZ polynomialsIn: 2.
	x := P x. y := P y.
	'self assert: C weightEnumerator = (x^8 + (x*y^4*14) + (y^8))'
]

{ #category : #tests }
CodesTest >> testMacWilliamsTheorem [
	"(MacWilliams, 1962) the theorem relates the weight enumerator of a linear code to the weight enumerator of its dual."
	"From youtube, Neil Sloane 'Error Correcting Codes, Group Theory and Invariant Theory, Part 1' 20:30."
	| C W Wperp x y |
	C := LinearCode H7.
	W := C weightEnumerator.
	Wperp := C dual weightEnumerator.
	x := Wperp parent x.
	y := Wperp parent y.
	self assert: Wperp = ((W value: {x+y. x-y}) / C size)
]

{ #category : #tests }
CodesTest >> testParityCheckMatrix [
	| H7 M |
	H7 := LinearCode H7.
	M := H7 parityCheckMatrix.
	self assert: (M * H7 atRandom) isZero
]

{ #category : #tests }
CodesTest >> testSelfDual [
	| F C |
	F := ZZ/2.
	"{00,11} is the smallest self-dual code"
	C := 'LinearCode subspace: (F^2 span: {(0,0) % 2. (1,1) % 2})'.
	self assert: C isSelfDual.
	self assert: C isSelfOrthogonal.
	"TODO: test other examples of self-dual codes: H8, G24"
]

{ #category : #tests }
CodesTest >> testSingletonBound: C [
	"Any linear [n,k,d] code satisfies k + d <= n + 1."
	| n k d |
	n := C length.
	k := C rank.
	d := C minimumDistance.
	self assert: k + d <= (n + 1).
]

{ #category : #tests }
CodesTest >> testSingletonBoundH7 [
	"Any linear [n,k,d] code satisfies k + d <= n + 1."
	self testSingletonBound: LinearCode H7
]

{ #category : #tests }
CodesTest >> testSingletonBoundTetracode [
	"Any linear [n,k,d] code satisfies k + d <= n + 1."
	self testSingletonBound: LinearCode tetracode
]

{ #category : #tests }
CodesTest >> testTetracode [
	| C P x y |
	C := LinearCode subspace: ('ZZ/3 ^ 4' span: {(1,1,1,0) % 3. (0,1,2,1) % 3}).
	self assert: C isSelfDual.
	self assert: C minimumDistance = 3.
	P := ZZ polynomialsIn: #(x y).
	x := P x.
	y := P y.
	'self assert: C weightEnumerator = (x^4 + (x*(y^3)*8))'
]

{ #category : #tests }
CodesTest >> testWeightEnumerator [
	"From youtube, Neil Sloane 'error correcting codes, group theory and invariant theory part 1' 19:30."
	| F C w x y |
	F := ZZ/2.
	C := 'LinearCode subspace: (F^5 span: {(0,0,0,0,0) % 2. (1,1,1,1,1) % 2})'.
	w := C weightEnumerator.
	x := w parent x.
	y := w parent y.
	'self assert: w = (x^5 + (y^5))'.
	'self assert: C dual weightEnumerator = (x^5 + (x^3*(y^2)*10) + (y^4*x*5))'
]
