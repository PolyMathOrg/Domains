"
Abstract cell complexes. See subclasses.
"
Class {
	#name : #CellComplex,
	#superclass : #Domain,
	#category : #'Mathematics-Homology'
}

{ #category : #homology }
CellComplex >> boundaryMap: k over: aRing [
	"The k-th boundary map or differential d(k) goes from C(k) to C(k-1).
	Its image is the group of (k-1)-boundaries B(k-1), a subgroup of C(k-1).
	Its kernel is the group of k-cycles Z(k), a subgroup of C(k)."
	^ (self chains: k over: aRing) to: (self chains: k-1 over: aRing) evaluating: [:x| x boundary]
]

{ #category : #accessing }
CellComplex >> cells: n [
	"Answer the set of n-cells of the receiver."
	^ Set accumulate: [:aBlock| self cells: n do: aBlock]
]

{ #category : #enumerating }
CellComplex >> cells: n do: aBlock [
	"Iterate over the n-cells of the receiver, possibly with repretitions.
	Subclasses should reimplement."
	^ self do: [:each| each dimension = n ifTrue: [aBlock value: each]]
]

{ #category : #homology }
CellComplex >> chainComplexOver: aRing [
	^ ChainComplex differentials: ((self dimension+1 to: 0 by: -1) collect: [:i| self boundaryMap: i over: aRing])
]

{ #category : #homology }
CellComplex >> chains: k over: aRing [
	"Answer the group of k-chains."
	k < 0 ifTrue: [^ aRing freeModuleIn: #()].
	^ aRing freeModuleIn: (self cells: k) asArray
]

{ #category : #invariants }
CellComplex >> dimension [
	self isVoid ifTrue: [^ Infinity negative].
	^ self max: [:each| each dimension]
]

{ #category : #invariants }
CellComplex >> euler [
	"Answer the Euler characteristic of the receiver."
	^ (0 to: self dimension) sum: [:p| (-1 raisedTo: p) * (self cells: p) size]
]

{ #category : #invariants }
CellComplex >> fPolynomial [
	"Answer the f-polynomial of this cell complex. This is the univariate polynomial with coefficients given by the f-vector (in decreasing order of exponents)."
	^ ZZ polynomials coefficients: self fVector reversed
]

{ #category : #invariants }
CellComplex >> fVector [
	"Answer the f-vector of this cell complex. This is a tuple of integers that count the number of cells of each dimension."
	^ ZZ tuple: self dimension + 2 evaluating: [:i| (self cells: i-2) size]
]

{ #category : #invariants }
CellComplex >> gVector [
	"Answer the g-vector of this cell complex."
	| h |
	h := self hVector.
	^ ZZ tuple: h size // 2 + 1 evaluating: [:i| i == 1 ifTrue: [1] ifFalse: [(h at: i) - (h at: i-1)]]
]

{ #category : #invariants }
CellComplex >> hPolynomial [
	"Answer the h-polynomial of this cell complex. This is the result of composing the f-polynomial with 'x - 1'."
	| f x |
	f := self fPolynomial.
	x := f parent x.
	^ 'f î (x - 1)'
]

{ #category : #invariants }
CellComplex >> hVector [
	"Answer the h-vector of this cell complex. This is the tuple of coefficients of the h-polynomial (in decreasing order of exponents)."
	^ self hPolynomial coefficients reversed
]

{ #category : #testing }
CellComplex >> isTrivial [
	"Answer true if this is the trivial complex, with only the empty cell."
	^ self size = 1
]

{ #category : #testing }
CellComplex >> isVoid [
	"Answer true if this is the void complex, that has no cells."
	^ self size = 0
]

{ #category : #printing }
CellComplex >> printOn: aStream [
	aStream nextPut: $<.
	self do: [:each| aStream print: each] separatedBy: [aStream nextPut: $,].
	aStream nextPut: $>
]

{ #category : #accessing }
CellComplex >> vertices [
	| answer |
	self propertyAt: #vertices ifPresent: [:aSet| ^ aSet].
	answer := Set new.
	self facets do: [:each| answer addAll: each vertices].
	^ self propertyAt: #vertices put: answer
]
