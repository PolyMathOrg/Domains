Class {
	#name : #RootSystem,
	#superclass : #Object,
	#instVars : [
		'roots',
		'ambient'
	],
	#category : #'Mathematics-Etc-Lie'
}

{ #category : #examples }
RootSystem class >> A: V [
	| roots |
	roots := Set new.
	1 to: V dimension do: [:i|
		i to: V dimension do: [:j|
			roots add: (V e: i) - (V e: j)]].
	^ self on: V roots: roots
]

{ #category : #examples }
RootSystem class >> B: V [
	| roots |
	roots := Set new.
	1 to: V dimension do: [:i|
		roots add: (V e: i).
		i to: V dimension do: [:j|
			roots add: (V e: i) - (V e: j); add: (V e: i) + (V e: j)]].
	^ self on: V roots: roots
]

{ #category : #examples }
RootSystem class >> C: V [
	| roots |
	roots := Set new.
	1 to: V dimension do: [:i|
		roots add: (V e: i)*2.
		i to: V dimension do: [:j|
			roots add: (V e: i) - (V e: j); add: (V e: i) + (V e: j)]].
	^ self on: V roots: roots
]

{ #category : #examples }
RootSystem class >> D: V [
	| roots |
	roots := Set new.
	1 to: V dimension do: [:i|
		i to: V dimension do: [:j|
			roots add: (V e: i) - (V e: j); add: (V e: i) + (V e: j)]].
	^ self on: V roots: roots
]

{ #category : #examples }
RootSystem class >> example1 [
	"This is a normalized root system in R^n. The Weyl group associated to it is the symmetric group S_n."
	| V roots |
	V := QQ raisedTo: 3.
	roots := Set new.
	1 to: V dimension do: [:i|
		1 to: i-1 do: [:j|
			roots add: (V e: i) - (V e: j); add: (V e: j) - (V e: i)]].
	^ RootSystem on: V roots: roots
]

{ #category : #examples }
RootSystem class >> example2 [
	"This is a normalized root system in R^n. The Weyl group associated to it is the hyperoctahedral group."
	| V roots |
	V := 'RR ^ 3'.
	roots := Set new.
	1 to: V dimension do: [:i|
		1 to: i-1 do: [:j|
			roots
				add: (V e: i) * (RealAlgebraicNumber sqrt: 2);
				add: (V e: i) * (RealAlgebraicNumber sqrt: 2) negated;
				add: (V e: i) - (V e: j);
				add: (V e: j) - (V e: i);
				add: (V e: i) + (V e: j);
				add: ((V e: i) + (V e: j)) negated]].
	^ RootSystem on: V roots: roots
]

{ #category : #examples }
RootSystem class >> example3 [
	"This is a normalized root system in R^n. The Weyl group associated to it is an index 2 subgroup of the hyperoctahedral group."
	| V roots |
	V := QQ raisedTo: 3.
	roots := Set new.
	1 to: 3 do: [:i|
		1 to: i-1 do: [:j|
			roots
				add: (V e: i) - (V e: j);
				add: (V e: j) - (V e: i);
				add: (V e: i) + (V e: j);
				add: ((V e: i) + (V e: j)) negated]].
	^ RootSystem on: V roots: roots
]

{ #category : #examples }
RootSystem class >> hexagonal [
	^ self A: 'QQ ^ 2'
]

{ #category : #'instance creation' }
RootSystem class >> on: aVectorSpace roots: aCollection [
	^ self new ambient: aVectorSpace; roots: aCollection
]

{ #category : #accessing }
RootSystem >> ambient [
	"Answer the ambient space of the receiver."
	^ ambient
]

{ #category : #'accessing-private' }
RootSystem >> ambient: aVectorSpace [
	ambient := aVectorSpace
]

{ #category : #roots }
RootSystem >> coroots [
	^ roots collect: [:v| v * 2 / (ambient innerProduct value: {v.v})]
]

{ #category : #operations }
RootSystem >> coxeterElement [
	| O answer |
	O := ambient automorphisms orthogonal.
	answer := ambient id.
	'self simpleRoots do: [:each| answer := answer î (O reflectionAt: each)]'.
	^ answer
]

{ #category : #operations }
RootSystem >> coxeterMatrix [
	"Answer the Coxeter matrix of the receiver.
	Given a basis a_i of simple roots, the Coxeter matrix m_ij is defined by <a_i,a_j> = -2 cos(pi / m_ij)."
	| S |
	S := self normalized simpleRoots.
	^ ambient scalars
		matrix: S size
		evaluating: [:i :j| Float pi / ((ambient innerProduct value: {(S at: i). (S at: j)}) / -2) arcCos]
]

{ #category : #operations }
RootSystem >> coxeterNumber [
	^ self weylGroup orderOf: self coxeterElement
]

{ #category : #roots }
RootSystem >> degreeOf: aPositiveRoot [
	"Answer the degree of the given positive root."
	^ (self simpleRoots coordinatesOf: aPositiveRoot) asArray sum
]

{ #category : #operations }
RootSystem >> dual [
	^ self class on: ambient roots: self coroots
]

{ #category : #operations }
RootSystem >> exponents [
	"Answer the 'sequence of exponents' of the root system."
	| h |
	self flag: #fix. "complex eigenvalues, but how about finite fields?"
	h := self coxeterNumber.
	^ self coxeterElement eigenvalues collect: [:each| each log / (Float pi * 2 i / h)]
]

{ #category : #testing }
RootSystem >> isCrystallographic [
	^ self roots allSatisfy: [:x|
		self coroots allSatisfy: [:y|
			(ambient innerProduct value: {x. y}) isInteger]]
]

{ #category : #testing }
RootSystem >> isIntegral [
	^ self isCrystallographic
]

{ #category : #testing }
RootSystem >> isIrreducible [
	^ self coxeterDiagram isConnected
]

{ #category : #testing }
RootSystem >> isNormalized [
	^ roots allSatisfy: [:each| (ambient innerProduct value: {each.each}) = 2]
]

{ #category : #operations }
RootSystem >> lattice [
	"Answer the root lattice, the Z-submodule spanned by roots of the receiver."
	^ Lattice basis: self simpleRoots
]

{ #category : #roots }
RootSystem >> negativeRoots [
	^ self positiveRoots negated
]

{ #category : #operations }
RootSystem >> normalized [
	^ self class on: ambient roots: (roots collect: [:x| x * (2 / (ambient innerProduct value: {x.x}))])
]

{ #category : #roots }
RootSystem >> positiveRoots [
	| answer |
	answer := Set new.
	roots do: [:a| (answer includes: a negated)
		ifFalse:
			[answer add: a.
			answer copy do: [:b| (roots includes: a+b) ifTrue: [answer add: b]]]].
	^ answer
]

{ #category : #roots }
RootSystem >> positiveRootsSorted [
	^ self positiveRoots asSortedCollection: [:a :b| (self simpleRoots coordinatesOf: b - a) asArray allSatisfy: [:each| each positive]]
]

{ #category : #operations }
RootSystem >> positiveWeylChamber [
	"Answer the positive Weyl chamber that is choosen in the receiver to define the positive roots."
	^ self notYetImplemented
]

{ #category : #printing }
RootSystem >> printOn: aStream [
	aStream nextPut: ${.
	roots do: [:each| aStream print: each] separatedBy: [aStream nextPut: $,].
	aStream nextPut: $}
]

{ #category : #accessing }
RootSystem >> rank [
	^ ambient dimension
]

{ #category : #accessing }
RootSystem >> roots [
	^ roots
]

{ #category : #'accessing-private' }
RootSystem >> roots: aCollection [
	roots := aCollection
]

{ #category : #roots }
RootSystem >> simpleRoots [
	| M |
	M := Matrix columns: (self positiveRoots asArray collect: [:each| ambient coordinatesOf: each]).
	^ LinearBasis on: ambient matrix: M imageMatrix
]

{ #category : #operations }
RootSystem >> weightLattice [
	"Answer the lattice spanned by the weights of the receiver. This lattice is invariant under the Weyl group and also under the map v -> -v. Also, the root lattice is contained in the weight lattice."
	^ Lattice basis: self weights
]

{ #category : #operations }
RootSystem >> weights [
	"Answer the fundamental weights of the receiver.
	A vector v is integral iff it can be expressed as integer linear combination of the fundamental weights."
	^ self notYetImplemented
]

{ #category : #operations }
RootSystem >> weylAction [
	| W |
	W := self weylGroup.
	W name: 'W'.
	^ GroupAction from: (W, self roots) to: self roots evaluatingWithArguments: [:f :x| f value: x]
]

{ #category : #operations }
RootSystem >> weylGroup [
	"Answer the Weyl group of the root system, i.e. the (finite) group of isometries of the ambient vector space generated by reflections through hyperplanes perpendicular to the roots. The Weyl group W(R) is the subgroup of GL(V) (and more specifically O(V)) generated by the reflections {s_r} that act on each root r by -1: s_r(r) = -r."
	| O W |
	O := ambient automorphisms orthogonal.
	W := TransformationGroup new generators: (self roots collect: [:each| O reflectionAt: each]).
"	W name: 'W'."
	^ W
]

{ #category : #operations }
RootSystem >> weylVector [
	^ self positiveRoots sum / 2
]
