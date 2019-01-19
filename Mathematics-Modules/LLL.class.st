"
This is the Lenstra-Lenstra-Lovasz algorithm.

Input: integer lattice of dimension d given by a basis {b1, ..., bd};
Output: an almost H-reduced basis of the lattice.

The algorithm takes at most O(d^6 ln^3(B)), where the input vectors bi all satisfy |bi|^2 <= B. In practice however, this upper bound is quite pessimistic.

"
Class {
	#name : #LLL,
	#superclass : #Object,
	#instVars : [
		'basis',
		'delta',
		'orthogonalBasis',
		'mu'
	],
	#category : #'Mathematics-Modules-Lattices'
}

{ #category : #'instance creation' }
LLL class >> basis: aCollection [
	^ self new basis: aCollection
]

{ #category : #examples }
LLL class >> example [
	| b1 b2 b3 lll |
	b1 := (1, 1, 1).
	b2 := (-1, 0, 2).
	b3 := (3, 5, 6).
	lll := self basis: { b1. b2. b3 }.
	^ lll reducedBasis
]

{ #category : #examples }
LLL class >> example2 [
	"Find polynomial x^2 - x - 1 that has the golden ratio phi as root."
	| r b1 b2 b3 lll |
	r := 1.618034.
	b1 := (1, 0, 0, (10000 * r squared)).
	b2 := (0, 1, 0, (10000 * r)).
	b3 := (0, 0, 1, 10000).
	lll := self basis: { b1. b2. b3 }.
	^ lll reducedBasis
]

{ #category : #initialization }
LLL >> basis: aCollection [
	| d |
	basis := Array withAll: aCollection.
	d := basis size.
	delta := 3/4 "(4/3 + 0.0000000001)^((d-1)/2)"
]

{ #category : #private }
LLL >> computeMu [
	| n bi oj |
	n := basis size.
	mu := ZZ matrix: n@n evaluating: [:i :j|
		bi := basis at: i.
		oj := orthogonalBasis at: j.
		(bi dot: oj) / (oj dot: oj)]
]

{ #category : #private }
LLL >> computeOrthogonalBasis [
	| k vi vj vectors |
	vectors := Array withAll: basis.
	k := vectors size.
	1 to: k do: [ :i |
		vi := vectors at: i.
		i+1 to: k do: [ :j |
			vj := vectors at: j.
			vj := vj - (vi * ((vj dot: vi) / (vi dot: vi))).
			vectors at: j put: vj ] ].
	orthogonalBasis := vectors
]

{ #category : #private }
LLL >> computeReducedBasis [
	| k mukj bj bk a b |
	self computeOrthogonalBasis; computeMu.
	k := 1.
	[k < basis size] whileTrue:
		[k-1 to: 0 by: -1 do: [ :j |
			mukj := mu at: k+1 @ (j+1).
			bj := basis at: j+1.
			bk := basis at: k+1.
			mukj abs > (1/2) ifTrue:
				[basis at: k+1 put: bk - (bj * mukj rounded).
				self update: k+1]].
		a := (orthogonalBasis at: k+1) norm2.
		b := (orthogonalBasis at: k) norm2.
		a >= ((delta - (mu at: k+1 @ k) squared) * b)
			ifTrue: [k := k + 1]
			ifFalse:
				[basis swap: k+1 with: k.
				self update: k+1.
				k := k-1 max: 1]].
	^ basis
]

{ #category : #accessing }
LLL >> reducedBasis [
	orthogonalBasis notNil ifFalse: [self computeReducedBasis].
	^ basis
]

{ #category : #private }
LLL >> update: k [
	self flag: #fix. "don't need to recompute all"
	self computeOrthogonalBasis; computeMu
]
