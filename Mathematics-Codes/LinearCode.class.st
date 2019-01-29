"
In coding theory, a linear code is an error-correcting code for which any linear combination of codewords is also a codeword. Thus, linear codes can be seen as a vector space (or more precisely as a subspace of a vector space).

References:
	https://en.wikipedia.org/wiki/Linear_code

"
Class {
	#name : #LinearCode,
	#superclass : #Domain,
	#instVars : [
		'subspace'
	],
	#category : #'Mathematics-Codes'
}

{ #category : #examples }
LinearCode class >> G11 [
	"Answer the perfect ternary Golary code [11,6,5]."
	
	^ self
		matrix:
			(Matrix
				rows:
					{((1 , 0 , 0 , 0 , 0 , 0 , 1 , 1 , 1 , 1 , 1) % 3).
					((0 , 1 , 0 , 0 , 0 , 0 , 0 , 1 , 2 , 2 , 1) % 3).
					((0 , 0 , 1 , 0 , 0 , 0 , 1 , 0 , 1 , 2 , 2) % 3).
					((0 , 0 , 0 , 1 , 0 , 0 , 2 , 1 , 0 , 1 , 2) % 3).
					((0 , 0 , 0 , 0 , 1 , 0 , 2 , 2 , 1 , 0 , 1) % 3).
					((0 , 0 , 0 , 0 , 0 , 1 , 1 , 2 , 2 , 1 , 0) % 3)})
]

{ #category : #examples }
LinearCode class >> G12 [
	"Answer the extended ternary Golary code [12,6,6]."
	
	^ self
		matrix:
			(Matrix
				rows:
					{((1 , 0 , 0 , 0 , 0 , 0 , 0 , 1 , 1 , 1 , 1 , 1) % 3).
					((0 , 1 , 0 , 0 , 0 , 0 , 1 , 0 , 1 , 2 , 2 , 1) % 3).
					((0 , 0 , 1 , 0 , 0 , 0 , 1 , 1 , 0 , 1 , 2 , 2) % 3).
					((0 , 0 , 0 , 1 , 0 , 0 , 1 , 2 , 1 , 0 , 1 , 2) % 3).
					((0 , 0 , 0 , 0 , 1 , 0 , 1 , 2 , 2 , 1 , 0 , 1) % 3).
					((0 , 0 , 0 , 0 , 0 , 1 , 1 , 1 , 2 , 2 , 1 , 0) % 3)})
]

{ #category : #examples }
LinearCode class >> G24 [
"Answer the extended binary Golary code [24,12,8].
	Its generator matrix is I|A, where I is the 12x12 identity matrix and A is the complement of the adjacency matrix of the icosahedron."

	| F A |
	F := ZZ / 2.
	A := Graph icosahedron adjacencyMatrix: (1 to: 12).
	A := A
		apply:
			(Function
				from: A scalars
				to: F
				evaluating: [ :x | 
					x = 0
						ifTrue: [ F one ]
						ifFalse: [ F zero ] ]).
	^ self matrix: A identity | A
]

{ #category : #examples }
LinearCode class >> H7 [
	"Answer the [7,4,3] Hamming code, which is the binary cyclic code of length 7 with generator polynomial 1 + x + x^3."
	
	| generators c |
	generators := OrderedCollection
		with: (c := (1 , 1 , 0 , 1 , 0 , 0 , 0) % 2).
	3 timesRepeat: [ generators add: (c := c >> 1) ].
	^ self matrix: (Matrix rows: generators)
]

{ #category : #examples }
LinearCode class >> H8 [
	"Answer the extended Hamming code [8,4,4]."
	
	^ self
		matrix:
			(Matrix
				rows:
					{((1 , 0 , 0 , 0 , 0 , 1 , 1 , 1) % 2).
					((0 , 1 , 0 , 0 , 1 , 0 , 1 , 1) % 2).
					((0 , 0 , 1 , 0 , 1 , 1 , 0 , 1) % 2).
					((0 , 0 , 0 , 1 , 1 , 1 , 1 , 0) % 2)})
]

{ #category : #examples }
LinearCode class >> hadamard8 [
	"Answer the [8,3,4] Hadamard code."
	
	^ self
		matrix:
			(Matrix
				rows:
					{((0 , 0 , 0 , 0 , 1 , 1 , 1 , 1) % 2).
					((0 , 0 , 1 , 1 , 0 , 0 , 1 , 1) % 2).
					((0 , 1 , 0 , 1 , 0 , 1 , 0 , 1) % 2)})
]

{ #category : #'instance creation' }
LinearCode class >> matrix: aMatrix [
	"Answer a linear code with generator matrix aMatrix."
	
	^ self subspace: aMatrix rowSpace
]

{ #category : #examples }
LinearCode class >> simplex [
	"Answer the [7,3,4] simplex code, which is the dual code of the Hamming code."
	
	^ self
		matrix:
			(Matrix
				rows:
					{((0 , 0 , 0 , 1 , 1 , 1 , 1) % 2).
					((0 , 1 , 1 , 0 , 0 , 1 , 1) % 2).
					((1 , 0 , 1 , 0 , 1 , 0 , 1) % 2)})
]

{ #category : #'instance creation' }
LinearCode class >> subspace: aLinearSubspace [
	^ self new subspace: aLinearSubspace
]

{ #category : #examples }
LinearCode class >> tetracode [
	"Answer the tetracode, a self dual code of minimum distance 3."
	
	^ self
		subspace:
			((ZZ / 3 raisedTo: 4)
				span:
					{((1 , 1 , 1 , 0) % 3).
					((0 , 1 , 2 , 1) % 3)})
]

{ #category : #comparing }
LinearCode >> <= aLinearCode [
	^ self asVectorSpace <= aLinearCode asVectorSpace
]

{ #category : #comparing }
LinearCode >> = aLinearCode [
	^ (aLinearCode isKindOf: LinearCode)
		and: [ self asVectorSpace = aLinearCode asVectorSpace ]
]

{ #category : #accessing }
LinearCode >> ambient [
	"Answer the ambient vector space."
	^ self asVectorSpace ambient
]

{ #category : #converting }
LinearCode >> asLattice [
	"A linear code in a finite field or ring can be lifted to a lattice."
	| S F lift |
	S := self asVectorSpace.
	F := S scalars.
	lift := S to: (S apply: F projection section) evaluating: [:each| each apply: F section].
	^ Lattice basis: (S basis apply: lift)
]

{ #category : #converting }
LinearCode >> asVectorSpace [
	^ subspace
]

{ #category : #random }
LinearCode >> atRandom: aRandom bits: bitSize [
	^ self asVectorSpace atRandom: aRandom bits: bitSize
]

{ #category : #morphisms }
LinearCode >> automorphisms [
	"Answer the subgroup of Perm(F^k) (permutation of coordinates) that leave the receiver invariant.
	The automorphisms of a code and it's dual are the same."
	
	self notYetImplemented
]

{ #category : #accessing }
LinearCode >> completeWeightEnumerator [
	"Answer the complete weight enumerator polynomial."
	| F P |
	F := self ambient scalars elements asArray.
	P := ZZ polynomialsIn: F size.
	^ self elements sum: [:each| P monomial: (P monomials exponents: (F collect: [:i| each occurrencesOf: i]))]
]

{ #category : #private }
LinearCode >> computeMinimumDistance [
	| answer w |
	answer := Infinity positive.
	w := self weight.
	self do: [:each| each isZero ifFalse: [answer := answer min: (w value: each)]].
	^ answer
]

{ #category : #accessing }
LinearCode >> dimension [
	^ self rank
]

{ #category : #accessing }
LinearCode >> distance [
	"Answer the Hamming distance function."
	| k V |
	k := self dimension.
	V := self ambient.
	^ (V, V) to: ZZ evaluating: [:xy| | x y | x := V coordinatesOf: xy first. y := V coordinatesOf: xy second. (1 to: k) count: [:i| (x at: i) ~= (y at: i)]]
]

{ #category : #graphs }
LinearCode >> distanceGraph: d [
	"Answer the graph of the codewords of the receiver, with two codewords adjacent if their Hamming distance is d."
	| h G |
	h := self distance. "the Hamming distance function"
	G := Graph unordered.
	self elements do: [:x|
		self elements do: [:y|
			(h value: {x.y}) = d
				ifTrue: [G addEdgeFrom: x to: y]]].
	^ G
]

{ #category : #enumerating }
LinearCode >> do: aBlock [
	self asVectorSpace do: aBlock
]

{ #category : #operations }
LinearCode >> dual [
	"Answer the dual or orthogonal code of the receiver."
	^ LinearCode subspace: self asVectorSpace perp
]

{ #category : #accessing }
LinearCode >> generatorMatrix [
	^ self asVectorSpace matrix
]

{ #category : #comparing }
LinearCode >> hash [
	^ self asVectorSpace hash
]

{ #category : #testing }
LinearCode >> includes: aCodeword [
	^ self asVectorSpace includes: aCodeword
]

{ #category : #testing }
LinearCode >> isCyclic [
	"A code is called a cylic code if for each codeword (c1,...,cn) it also contains the cyclic right shifted word (cn,c1,c2,...,cn-1), i.e. the code is invariant under cylic shifts."
	self do: [:each| (self includes: (each wrap: 1)) ifFalse: [^ false]].
	^ true
]

{ #category : #testing }
LinearCode >> isMaximumDistanceSeparable [
	"Any linear [n,k,d] code satisfies k + d <= n + 1 (Singleton bound). If a code satisfies k + d = n + 1 it's called Maximum Distance Separable (MDS)."
	| n k d |
	n := self length.
	k := self rank.
	d := self minimumDistance.
	^ k + d = (n + 1)
]

{ #category : #testing }
LinearCode >> isSelfDual [
	self ambient dimension even ifFalse: [^ false].
	self dimension = (self ambient dimension / 2) ifFalse: [^ false].
	^ self = self dual
]

{ #category : #testing }
LinearCode >> isSelfOrthogonal [
	^ self asVectorSpace <= self dual asVectorSpace
]

{ #category : #morphisms }
LinearCode >> isometries [
	"Answer the subgroup of Iso(F^k) that leave the receiver invariant."
	self notYetImplemented
]

{ #category : #accessing }
LinearCode >> length [
	"Answer the length of a codeword."
	^ self ambient dimension
]

{ #category : #accessing }
LinearCode >> minimumDistance [
	"Answer the minimum Hamming distance between codewords.
	If the minimum distance is d, the code can correct (d-1)/2 errors."
	^ self propertyAt: #minimumDistance ifAbsentPut: [self computeMinimumDistance]
]

{ #category : #accessing }
LinearCode >> parityCheckMatrix [
	^ self dual generatorMatrix
]

{ #category : #printing }
LinearCode >> printOn: aStream [
	aStream nextPut: $[; print: self length; nextPut: $,; print: self rank; nextPut: $,; print: self minimumDistance; nextPut: $].
	aStream isText
		ifTrue: [aStream nextPutAll: self ambient scalars size printString sub]
		ifFalse: [aStream nextPut: $-; print: self ambient scalars size]
]

{ #category : #accessing }
LinearCode >> rank [
	^ self asVectorSpace dimension
]

{ #category : #accessing }
LinearCode >> rate [
	^ (self size log: 2) / self length
]

{ #category : #accessing }
LinearCode >> relativeDistance [
	^ self minimumDistance / self length
]

{ #category : #accessing }
LinearCode >> size [
	"Answer the number of codewords."
	^ self asVectorSpace size
]

{ #category : #'accessing-private' }
LinearCode >> subspace: aLinearSubspace [
	subspace := aLinearSubspace
]

{ #category : #graphs }
LinearCode >> tannerGraph [
	| matrix G |
	matrix := self parityCheckMatrix.
	G := Graph unordered.
	1 to: matrix height do: [:i|
		1 to: matrix width do: [:j|
			(matrix at: i@j) isZero not
				ifTrue:
					[| subcode digit |
					subcode := matrix rowAt: i.
					digit := matrix columnAt: j.
					G addEdgeFrom: subcode to: digit]]].
	^ G
]

{ #category : #accessing }
LinearCode >> weight [
	"Answer the Hamming weight function."
	| V |
	V := self ambient.
	^ Function from: V to: ZZ evaluating: [:x| (V coordinatesOf: x) weight]
]

{ #category : #accessing }
LinearCode >> weightDistribution [
	| answer w |
	w := self weight.
	answer := Bag new.
	self do: [:each| answer add: (w value: each)].
	^ answer
]

{ #category : #accessing }
LinearCode >> weightDistribution: aCodeword [
	"Answer the weight distribution wrt aCodeword."
	self notYetImplemented
]

{ #category : #accessing }
LinearCode >> weightEnumerator [
	"Answer the Hamming weight enumerator polynomial."

	| P x y weights answer n |
	P := ZZ polynomialsIn: #(x y).
	x := P x.
	y := P y.
	answer := P zero.
	n := self ambient dimension.
	weights := self weightDistribution.
	weights asSet do: [:i| answer := (x  raisedTo: (n - i)) * (y raisedTo: i) * (weights occurrencesOf: i) + answer].
	^ answer
]
