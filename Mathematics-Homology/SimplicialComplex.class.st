"
Abstract simplicial complexes. These are combinatorial objects consisting of a collection of simplices (the 'faces' of the simplicial complex) with the following properties:
- every subface of a face is also in the complex;
- the intersection of two faces is either empty or a common face of both simplices, and it is also in the complex.

An abstract simplicial complex can also be seen as a subset of the power set of some set V, often V={1,...,n}, closed under inclusion.

Simplicial complexes form a category with simplicial maps as morphisms. See SimplicialMap.
"
Class {
	#name : #SimplicialComplex,
	#superclass : #CellComplex,
	#category : #'Mathematics-Homology'
}

{ #category : #'instance creation' }
SimplicialComplex class >> faces: aCollection [
	"Answer a new simplicial complex with the given collection of simplices as faces.
	The faces in aCollection are not assumed to be maximal, so we compute a subset of maximal faces (facets)."
	| faces maximalFaces |
	faces := Set new: aCollection size.
	aCollection do: [:each|
		(each isKindOf: Simplex)
			ifTrue: [faces add: each]
			ifFalse: [faces add: (each as: Simplex)]].
	faces := faces asSortedCollection: [:a :b| a dimension <= b dimension].
	maximalFaces := Set new.
	1 to: faces size do: [:i| | face |
		face := faces at: i.
		((i+1 to: faces size) anySatisfy: [:j| face <= (faces at: j)])
			ifFalse: [maximalFaces add: face]].
	^ self facets: maximalFaces
]

{ #category : #'instance creation' }
SimplicialComplex class >> facets: aCollection [
	"Answer a new simplicial complex with the given collection of simplices as facets.
	The faces in aCollection are assumed to be maximal."
	| facets |
	facets := Set new: aCollection size.
	aCollection do: [:each|
		(each isKindOf: Simplex)
			ifTrue: [facets add: each]
			ifFalse: [facets add: (each as: Simplex)]].
	^ self new facets: facets
]

{ #category : #examples }
SimplicialComplex class >> kleinBottle [
	"A minimal triangulation of the Klein bottle."
	^ self facets: #((2 3 7) (1 2 3) (1 3 5) (1 5 7) (1 4 7) (2 4 6) (1 2 6) (1 6 0) (1 4 0) (2 4 0) (3 4 7) (3 4 6) (3 5 6) (5 6 0) (2 5 0) (2 5 7))
]

{ #category : #'instance creation' }
SimplicialComplex class >> on: aVertexSet faces: aCollection [
	"Answer a new simplicial complex with the given collection of simplices as faces.
	The faces in aCollection are not assumed to be maximal, so we compute a subset of maximal faces (facets)."
	^ (self faces: aCollection) vertices: aVertexSet
]

{ #category : #'instance creation' }
SimplicialComplex class >> on: aVertexSet facets: aCollection [
	"Answer a new simplicial complex with the given collection of simplices as facets.
	The faces in aCollection are assumed to be maximal."
	^ (self facets: aCollection) vertices: aVertexSet
]

{ #category : #examples }
SimplicialComplex class >> realProjectivePlane [
	"A minimal triangulation of the real projective plane."
	^ self facets: #((0 1 2) (0 2 3) (0 1 5) (0 4 5) (0 3 4) (1 2 4) (1 3 4) (1 3 5) (2 3 5) (2 4 5))
]

{ #category : #examples }
SimplicialComplex class >> sphere: n [
	"A minimal triangulation of the n-sphere."
	^ self facets: ((Simplex new: n+1) faces: n)
]

{ #category : #examples }
SimplicialComplex class >> torus [
	"A minimal triangulation of the torus."
	^ self facets: #((0 1 2) (1 2 4) (1 3 4) (1 3 6) (0 1 5) (1 5 6) (2 3 5) (2 4 5) (2 3 6) (0 2 6) (0 3 4) (0 3 5) (4 5 6) (0 4 6))
]

{ #category : #operations }
SimplicialComplex >> * aSimplicialComplex [
	"Answer the join of the receiver with the argument."
	| join |
	join := Set new.
	self facets do: [:each|
		aSimplicialComplex facets do: [:other| join add: each * other]].
	^ self species facets: join
]

{ #category : #operations }
SimplicialComplex >> - aSimplicialComplex [ "ñ "
	^ self species faces: self facets, aSimplicialComplex facets
]

{ #category : #operations }
SimplicialComplex >> / aFace [
	"Answer the link of aFace. This is the complex of all faces of simplices in the star that do not intersect aFace."
	^ self notYetImplemented
]

{ #category : #morphisms }
SimplicialComplex >> apply: aSimplicialMap [
	^ self species faces: (self facets collect: aSimplicialMap)
]

{ #category : #homology }
SimplicialComplex >> boundaryMap: k over: aRing [
	"The k-th boundary map or differential d(k) goes from C(k) to C(k-1).
	Its image is the group of (k-1)-boundaries B(k-1), a subgroup of C(k-1).
	Its kernel is the group of k-cycles Z(k), a subgroup of C(k)."

	"The boundary of a chain is the linear combination of the boundary of the simplices in the chain. The boundary of a k-chain is a (k-1)-chain."

	| domain codomain |
	domain := self chains: k over: aRing.
	codomain := self chains: k-1 over: aRing.
	k = 0 ifTrue: [^ (domain hom: codomain) zero].
	^ domain to: codomain evaluating: [:x|
		| answer |
		answer := codomain zero.
		x keysAndValuesDo: [:key :value|
			| V |
			V := key vertices asArray.
			1 to: V size do: [:i| | F f |
				"F is the facet opposite the i-th vertex:"
				F := Simplex vertices: (V copyWithoutIndex: i).
				f := (codomain x: F) * value.
				i odd ifTrue: [answer := answer + f] ifFalse: [answer := answer - f]]].
		answer]
]

{ #category : #enumerating }
SimplicialComplex >> cells: n do: aBlock [
	"Iterate over the n-cells of the receiver, possibly with repetitions."
	^ self faces: n do: aBlock
]

{ #category : #homology }
SimplicialComplex >> chains: k over: aRing [
	"Answer the group of k-chains."
	k < 0 ifTrue: [^ FormalSumsModule on: #() over: aRing].
	^ FormalSumsModule on: (self cells: k) asArray over: aRing
]

{ #category : #enumerating }
SimplicialComplex >> collect: aBlock [
	^ self species faces: (self elements collect: aBlock)
]

{ #category : #operations }
SimplicialComplex >> complement [
	| V |
	V := self vertices.
	^ self species on: V facets: (self facets collect: [:each| each complementIn: V])
]

{ #category : #operations }
SimplicialComplex >> cone [
	"Answer the join of the receiver with a new one-vertex simplicial complex."
	^ self * (self species facets: #((0)))
]

{ #category : #testing }
SimplicialComplex >> contains: aSimplex [
	^ self facets anySatisfy: [:one| one >= aSimplex]
]

{ #category : #operations }
SimplicialComplex >> coskeleton: n [
	"Answer the n-coskeleton of the receiver."
	^ self notYetImplemented
]

{ #category : #invariants }
SimplicialComplex >> dimension [
	self isVoid ifTrue: [^ Infinity negative].
	^ (self facets collect: [:each| each dimension]) max
]

{ #category : #operations }
SimplicialComplex >> dirProd: aSimplicialComplex [
	"◊"
	
	"Answer the direct product of the receiver and the argument."

	| product |
	product := Set new.
	self facets
		do: [ :each | 
			aSimplicialComplex facets
				do: [ :other | 
					self
						pathsFrom: each vertices
						to: other vertices
						do: [ :path | product add: (Simplex vertices: path) ] ] ].
	^ self species faces: product
]

{ #category : #enumerating }
SimplicialComplex >> do: aBlock [
	-1 to: self dimension do: [:each| (self faces: each) do: aBlock]
]

{ #category : #operations }
SimplicialComplex >> dual [
	"Answer the Alexander dual of the receiver.
	This is the simplicial complex made of the complement of all faces *not* in the receiver, and it is generated by the complements of the minimal nonfaces."
	| V |
	V := self vertices.
	^ self species on: V facets: (self nonfaces collect: [:each| each complementIn: V])
]

{ #category : #accessing }
SimplicialComplex >> edges [
	^ self faces: 1
]

{ #category : #accessing }
SimplicialComplex >> faces: m [
	^ Set accumulate: [:aBlock| self faces: m do: aBlock]
]

{ #category : #enumerating }
SimplicialComplex >> faces: n do: aBlock [
	"Iterate over the n-cells of the receiver, possibly with repetitions."
	self facets do: [:each| each faces: n do: [:face| aBlock value: face]]
]

{ #category : #operations }
SimplicialComplex >> facetIdeal [
	"Answer the facet ideal of this simplicial complex.
	This is the ideal generated by those squarefree monomials associated to the maximal faces (facets) of the simplicial complex."
	^ self facetIdealIn: (QQ polynomialsIn: self vertices size)
]

{ #category : #operations }
SimplicialComplex >> facetIdealIn: aRing [
	"Answer the facet ideal of this simplicial complex in the given polynomial ring.
	This is the ideal generated by those squarefree monomials associated to the maximal faces (facets) of the simplicial complex."
	| labelling |
	labelling := self labelling.
	^ aRing * (self facets collect: [:each|
		each vertices inject: aRing one into: [:g :v| g * (aRing x: (labelling at: v))]])
]

{ #category : #accessing }
SimplicialComplex >> facets [
	"Answer the maximal faces of the receiver."
	^ self propertyAt: #facets
]

{ #category : #'accessing-private' }
SimplicialComplex >> facets: aCollection [
	self propertyAt: #facets put: aCollection
]

{ #category : #testing }
SimplicialComplex >> includes: aSimplex [
	^ (aSimplex isKindOf: Simplex) and: [self contains: aSimplex]
]

{ #category : #testing }
SimplicialComplex >> isConnected [
	^ (self skeleton: 1) asGraph isConnected
]

{ #category : #testing }
SimplicialComplex >> isPure [
	| d |
	d := self dimension.
	^ self facets allSatisfy: [:each| each dimension = d]
]

{ #category : #testing }
SimplicialComplex >> isTrivial [
	"Answer true if this is the trivial complex, with only one face (the empty simplex)."
	^ self facets size = 1 and: [self facets allSatisfy: [:each| each isTrivial]]
]

{ #category : #testing }
SimplicialComplex >> isVoid [
	"Answer true if this is the void complex, that has no faces."
	^ self facets isEmpty
]

{ #category : #accessing }
SimplicialComplex >> labelling [
	"Answer a dictionary that associates a positive integer number to each vertex.
	For a simplicial complex with n vertices, the labels are 1,2,...,n."
	| V labelling |
	self propertyAt: #labelling ifPresent: [:aDictionary| ^ aDictionary].
	V := self vertices.
	(V allSatisfy: [:each| each isInteger])
		ifTrue: [V := V asSortedCollection]
		ifFalse: [V := V asSortedCollection: [:a :b| a printString <= b printString]].
	labelling := Dictionary new.
	1 to: V size do: [:each| labelling at: (V at: each) put: each].
	^ self propertyAt: #labelling put: labelling
]

{ #category : #accessing }
SimplicialComplex >> nonfaces [
	"Answer the set of minimal nonfaces, i.e. simpleces on the vertex set of the receiver which are not faces of the receiver."
	| answer V F |
	self isVoid ifTrue: [Set with: (Simplex vertices: #())].
	answer := Set new.
	V := self vertices asArray.
"	1 to: self vertices size do: [:k|"
	1 to: self dimension + 2 do: [:k|
		V combinations: k atATimeDo: [:combination|
			F := Simplex vertices: combination copy.
			((self contains: F) not and: [answer noneSatisfy: [:none| F >= none]])
				ifTrue: [answer add: F]]].
	^ answer
]

{ #category : #operations }
SimplicialComplex >> openStarOf: aCollection [
	"Answer the open star in the receiver of the simplices in aCollection.
	This is just a set of simplices, and not necesarily forms a complex."
	| answer |
	answer := Set new.
	aCollection do: [:each|
		self do: [:other| (each intersects: other) ifTrue: [answer add: other]]].
	^ answer
]

{ #category : #private }
SimplicialComplex >> pathsFrom: A to: B do: aBlock [
	| x |
	A isEmpty ifTrue: [^ aBlock value: {A}].
	B isEmpty ifTrue: [^ aBlock value: {B}].
	A size = 1 ifTrue:
		[| v |
		v := A at: 1.
		^ B do: [:w| aBlock value: {{v. w}}]].
	B size = 1 ifTrue:
		[| w |
		w := B at: 1.
		^ A do: [:v| aBlock value: {{v. w}}]].
	x := {A last. B last}.
	self pathsFrom: A allButLast to: B do: [:each| aBlock value: (each copyWith: x)].
	self pathsFrom: A to: B allButLast do: [:each| aBlock value: (each copyWith: x)]
]

{ #category : #printing }
SimplicialComplex >> printOn: aStream [
	aStream nextPut: $<.
	self facets do: [:each| aStream print: each] separatedBy: [aStream nextPut: $,].
	aStream nextPut: $>
]

{ #category : #accessing }
SimplicialComplex >> ridges [
	^ self faces: self dimension - 2
]

{ #category : #enumerating }
SimplicialComplex >> select: aBlock [
	^ self species on: self vertices faces: (self elements select: aBlock)
]

{ #category : #operations }
SimplicialComplex >> skeleton: n [
	"Answer the n-skeleton of the receiver."
	^ self collect: [:each| each dimension <= n]
]

{ #category : #private }
SimplicialComplex >> species [
	^ SimplicialComplex
]

{ #category : #operations }
SimplicialComplex >> stanleyReisnerIdeal [
	"Answer the Stanley-Reisner ideal of this simplicial complex.
	This is the ideal generated by those squarefree monomials associated to nonfaces of the simplicial complex."
	^ self stanleyReisnerIdealIn: (QQ polynomialsIn: self vertices size)
]

{ #category : #operations }
SimplicialComplex >> stanleyReisnerIdealIn: aRing [
	"Answer the Stanley-Reisner ideal of this simplicial complex in the given polynomial ring.
	This is the ideal generated by those squarefree monomials associated to nonfaces of the simplicial complex."
	| labelling |
	labelling := self labelling.
	^ aRing * (self nonfaces collect: [:each|
		each vertices inject: aRing one into: [:g :v| g * (aRing x: (labelling at: v))]])
]

{ #category : #operations }
SimplicialComplex >> stanleyReisnerRing [
	^ self stanleyReisnerRingOver: QQ
]

{ #category : #operations }
SimplicialComplex >> stanleyReisnerRingOver: aRing [
	^ (self stanleyReisnerIdealIn: (aRing polynomialsIn: self vertices size)) quotientRing
]

{ #category : #operations }
SimplicialComplex >> starOf: aCollection [
	"Answer the (closed) star in the receiver of the simplices in aCollection.
	This is the closure of the open star."
	^ self species on: self vertices faces: (self openStarOf: aCollection)
]

{ #category : #accessing }
SimplicialComplex >> support [
	"Answer the collection of vertices that belong to any face in the receiver."
	^ self vertices select: [:each| self facets anySatisfy: [:any| any includes: each]]
]

{ #category : #operations }
SimplicialComplex >> suspension [
	^ self * (self class sphere: 0)
]

{ #category : #morphisms }
SimplicialComplex >> to: aSimplicialComplex evaluating: aBlock [
	^ SimplicialMap from: self to: aSimplicialComplex evaluating: aBlock
]

{ #category : #morphisms }
SimplicialComplex >> to: aSimplicialComplex map: aDictionary [
	"Answer a simplicial map that maps vertices by aDictionary."
	^ SimplicialMap from: self to: aSimplicialComplex map: aDictionary
]

{ #category : #morphisms }
SimplicialComplex >> to: aSimplicialComplex mapping: aBlock [
	"Answer a simplicial map that maps vertices by aBlock."
	^ SimplicialMap from: self to: aSimplicialComplex mapping: aBlock
]

{ #category : #'accessing-private' }
SimplicialComplex >> vertices: aCollection [
	self propertyAt: #vertices put: aCollection asSet
]

{ #category : #operations }
SimplicialComplex >> wedgeProduct: aSimplicialComplex [
	"Answer the wedge product (one-point union) of the receiver with the argument."
	| v0 w0 facets |
	v0 := self support anyOne.
	w0 := aSimplicialComplex support anyOne.
	facets := Set new.
	self facets do: [:each| facets add: (each collect: [:v| v = v0 ifTrue: [{0. 0}] ifFalse: [{1. v}]])].
	aSimplicialComplex facets do: [:each| facets add: (each collect: [:w| w = w0 ifTrue: [{0. 0}] ifFalse: [{2. w}]])].
	^ self species "on: vertices" facets: facets
]
