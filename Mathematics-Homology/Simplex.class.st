"
(Abstract) n-simplices.

It is assumed that the vertices are objects that implement a total ordering with #<= (such as integers, strings, monomials), so that they can be ordered to choose an unambiguos orientation.
"
Class {
	#name : #Simplex,
	#superclass : #Collection,
	#instVars : [
		'vertices'
	],
	#category : #'Mathematics-Homology'
}

{ #category : #'instance creation' }
Simplex class >> new: n [
	"Answer the standard n-simplex {1,...,n}."
	^ self vertices: (1 to: n+1)
]

{ #category : #'instance creation' }
Simplex class >> newFrom: aCollection [
	^ self vertices: aCollection
]

{ #category : #'instance creation' }
Simplex class >> vertices: aCollection [
	^ self new vertices: aCollection
]

{ #category : #operations }
Simplex >> * aSimplex [
	"Answer the join of the receiver with the argument."
	^ self class vertices: (self vertices collect: [:x| {1. x}]), (aSimplex vertices collect: [:y| {2. y}])
]

{ #category : #comparing }
Simplex >> < aSimplex [
	"Answer true if the receiver is strictly contained in aSimplex as a face."
	^ aSimplex > self
]

{ #category : #comparing }
Simplex >> <= aSimplex [
	"Answer true if the receiver is contained in aSimplex as a face."
	^ aSimplex >= self
]

{ #category : #comparing }
Simplex >> = aSimplex [
	"Answer true if the receiver equals the argument."
	^ self vertices = aSimplex vertices

"before we didn't keep vertices sorted, so we could check of two differently oriented simplices were equal:
	| iv v |
	vertices isEmpty ifTrue: [^ aSimplex vertices isEmpty].
	v := vertices first.
	iv := aSimplex vertices indexOf: v ifAbsent: [^ false].
	vertices withIndexDo: [:each :i|
		each = (aSimplex vertices atWrap: i+iv-1) ifFalse: [^ false]].
	^ true"
]

{ #category : #comparing }
Simplex >> > aSimplex [
	"Answer true if the receiver strictly containes aSimplex as a face."
	^ vertices size > aSimplex vertices size and: [vertices includesAllOf: aSimplex vertices]
]

{ #category : #comparing }
Simplex >> >= aSimplex [
	"Answer true if the receiver containes aSimplex as a face."
	^ vertices size >= aSimplex vertices size and: [vertices includesAllOf: aSimplex vertices]
]

{ #category : #converting }
Simplex >> asSkeletonGraph [
	| graph F |
	graph := Graph unordered.
	F := self faces: self dimension.
	graph addAll: self facets.
	F do: [:x| F do: [:y| graph addEdgeFrom: x to: y]].
	^ graph
]

{ #category : #operations }
Simplex >> closure [
	"Answer the simplicial complex with the receiver. By definition of simplicial complex, it also contains all faces of the receiver)."
	^ SimplicialComplex facets: {self}
]

{ #category : #enumerating }
Simplex >> collect: aBlock [
	^ self class vertices: (self vertices collect: aBlock) asSet "we don't assume aBlock is injective, so we have to convert to a Set to remove repetitions"
]

{ #category : #operations }
Simplex >> complementIn: aCollection [
	"Answer the complement of the receiver in the given vertex set.
	This is the simplex formed by the vertices in aCollection *not* in the receiver."
	^ self class vertices: aCollection \ vertices
]

{ #category : #accessing }
Simplex >> dimension [
	^ vertices size - 1
]

{ #category : #enumerating }
Simplex >> do: aBlock [
	^ self vertices do: aBlock
]

{ #category : #operations }
Simplex >> dot: aSimplex [
	"Answer the face common to the receiver and aSimplex, which could be {}."
	^ self class vertices: (self vertices) dot: (aSimplex vertices)
]

{ #category : #faces }
Simplex >> edges [
	^ self faces: 1
]

{ #category : #faces }
Simplex >> faces [
	"Answer all faces of the receiver (including the empty set and the receiver)."
	^ Iterator on: [:aBlock| self facesDo: aBlock]
]

{ #category : #faces }
Simplex >> faces: n [
	"Answer the n-faces of the receiver."
	^ Iterator on: [:aBlock| self faces: n do: aBlock]
]

{ #category : #faces }
Simplex >> faces: n do: aBlock [
	"Iterate over the n-faces of the receiver."
	n = -1 ifTrue: [^ aBlock value: (self class vertices: #())].
	vertices isEmpty ifTrue: [^ self].
	vertices combinations: n+1 atATimeDo: [:each|
		aBlock value: (self class vertices: each asSet)]
]

{ #category : #faces }
Simplex >> facesDo: aBlock [
	"Iterate over all faces of the receiver (including the empty set and the receiver)."
	-1 to: self dimension do: [:i| self faces: i do: aBlock]
]

{ #category : #faces }
Simplex >> facets [
	"Answer the boundary faces of the receiver."
	^ self faces: self dimension - 1
]

{ #category : #comparing }
Simplex >> hash [
	^ vertices inject: 0 into: [:sum :each| sum + each hash] "this is independent of orientation"
]

{ #category : #testing }
Simplex >> includes: anObject [
	^ vertices includes: anObject
]

{ #category : #testing }
Simplex >> intersects: aSimplex [
	^ self vertices intersects: aSimplex vertices
]

{ #category : #testing }
Simplex >> isTrivial [
	"Answer true if this is the empty simplex."
	^ vertices isEmpty
]

{ #category : #printing }
Simplex >> printOn: aStream [
"	self isTrivial ifTrue: [aStream nextPut: Character emptySet. ^ self]."
	aStream nextPut: ${.
	self vertices do: [:each|
		(each isString and: [aStream isText])
			ifTrue: [aStream nextPutAll: each asText]
			ifFalse: [aStream print: each]] separatedBy: [aStream nextPut: $,].
	aStream nextPut: $}
]

{ #category : #faces }
Simplex >> properFaces [
	"Answer all proper faces of the receiver of any dimension (including the empty set)."
	^ Iterator on: [:aBlock| self properFacesDo: aBlock]
]

{ #category : #faces }
Simplex >> properFacesDo: aBlock [
	"Iterate over all proper faces of the receiver (including the empty set)."
	-1 to: self dimension - 1 do: [:i| self faces: i do: aBlock]
]

{ #category : #faces }
Simplex >> ridges [
	^ self faces: self dimension - 2
]

{ #category : #accessing }
Simplex >> size [
	^ vertices size
]

{ #category : #private }
Simplex >> species [
	^ Set
]

{ #category : #accessing }
Simplex >> vertices [
	^ vertices
]

{ #category : #'accessing-private' }
Simplex >> vertices: aCollection [
	vertices := aCollection asSortedCollection
]

{ #category : #accessing }
Simplex >> volume [
	^ self notYetImplemented "see wikipedia"
]

{ #category : #comparing }
Simplex >> ~ aSimplex [
	"Answer true if the receiver and the argument are isomorphic."
	^ self dimension = aSimplex dimension
]
