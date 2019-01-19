"
(Bounded) chain complexes.

A chain complex is a sequence of abelian groups or modules C(k) (called k-chains) conected by homomorphisms d(k):C(k)->C(k-1) (called boundary operators or differentials) such that the composition between any two consecutive differentials is the trivial map: d(k) o d{k+1} = 0.

A bounded chain complex is one where only a finite number of C(k) are not {0}.

Chain complexes form a cateogory with chain maps as morphisms. See ChainMap.
"
Class {
	#name : #ChainComplex,
	#superclass : #Domain,
	#category : #'Mathematics-Homology'
}

{ #category : #'instance creation' }
ChainComplex class >> differentials: anArray [
	^ self new differentials: anArray
]

{ #category : #homology }
ChainComplex >> betti [
	^ (0 to: self degree) collect: [:i| self betti: i]
]

{ #category : #homology }
ChainComplex >> betti: k [
	"Answer the k-th Betti number.
	This is the rank of the k-th homology group.
	For singular homology this gives a measure of the number of k-dimensional holes."
	^ (self homology: k) rank
]

{ #category : #homology }
ChainComplex >> boundaries: k [
	"Answer the group of k-boundaries B(k), a subgroup of the group of k-chains C(k).
	This is the image of the k+1-th differential d(k+1)."
	^ (self d: k+1) image
]

{ #category : #operations }
ChainComplex >> cartProd: aChainComplex [
	"Answer the cartesian product (direct sum) of the receiver with the argument."
	^ self notYetImplemented
]

{ #category : #accessing }
ChainComplex >> chains: k [
	"Answer the k-chains group or module."
	^ (self d: k) domain
]

{ #category : #homology }
ChainComplex >> cycles: k [
	"Answer the group of k-cycles Z(k), a subgroup of the group of k-chains C(k).
	This is the kernel of the k-th differential d(k)."
	^ (self d: k) kernel
]

{ #category : #accessing }
ChainComplex >> d: k [
	"Answer the k-th differential or boundary map d(k):C(k)->C(k-1)."
	| D |
	D := self differentials.
	^ D at: D size - k
]

{ #category : #accessing }
ChainComplex >> degree [
	"Answer the maximum degree of a differential. A chain complex of degree n has n+2 differentials d(n+1) to d(0)."
	^ self differentials size - 2
]

{ #category : #accessing }
ChainComplex >> differentials [
	"Answer the differentials, ordered as d(n) -> ... -> d(1) -> d(0)."
	^ self propertyAt: #differentials
]

{ #category : #private }
ChainComplex >> differentials: anArray [
	self propertyAt: #differentials put: anArray
]

{ #category : #operations }
ChainComplex >> dual [
	"Answer the dual of the receiver. This is the cochain complex, taking dual in all objects and arrows reversed."
	^ self class differentials: (self differentials reversed collect: [:each| each adjoint])
]

{ #category : #homology }
ChainComplex >> homology: k [
	"Answer the k-th homology group H(k).
	This is the quotient of the k-cycles Z(k) modulo the k-boundaries B(k)."
	^ (self cycles: k) / (self boundaries: k)
]

{ #category : #testing }
ChainComplex >> isExact [
	0 to: self degree do: [:i|
		(self d: i) image = (self d: i+1) kernel ifFalse: [^ false]].
	^ true
]

{ #category : #printing }
ChainComplex >> printOn: aStream [
	aStream print: self differentials first domain.
	self differentials do: [:each| aStream nextPutAll: '  '; print: each codomain].
]

{ #category : #accessing }
ChainComplex >> scalars [
	^ self propertyAt: #scalars ifAbsentPut: [self differentials anyOne domain scalars]
]

{ #category : #operations }
ChainComplex >> tensorProd: aChainComplex [
	"Answer the tensor product of the receiver with the argument."
	^ self notYetImplemented
]

{ #category : #private }
ChainComplex >> verify [
	| n |
	n := self degree.
	(self d: n+1) kernel isTrivial ifFalse: [^ false halt].
	(self d: 0) image isTrivial ifFalse: [^ false halt].
	n+1 to: 1 by: -1 do: [:i|
		(self d: i) codomain = (self d: i-1) domain ifFalse: [^ false halt].
		(self d: i) image <= (self d: i-1) kernel ifFalse: [^ false halt]].
	^ true
]

{ #category : #comparing }
ChainComplex >> ~ aChainComplex [
	"Answer true if the receiver is isomorphic to the argument."
	^ self notYetImplemented
]
