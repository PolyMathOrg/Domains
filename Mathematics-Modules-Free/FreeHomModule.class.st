"
Free R-modules (or K-vector spaces) of linear maps from a free R-module (or K-vector space) A to another one B, i.e. Hom(A,B). When A = B, it is noted End(A).

See FreeModule and LinearMap.
"
Class {
	#name : #FreeHomModule,
	#superclass : #FreeModule,
	#instVars : [
		'domain',
		'codomain'
	],
	#category : #'Mathematics-Modules-Free'
}

{ #category : #examples }
FreeHomModule class >> example1 [
	"The vector space of linear transformations
	from 3-tuples to 2-tuples, over the rational numbers."
	^ 'QQ^3 hom: QQ^2'
]

{ #category : #examples }
FreeHomModule class >> example2 [
	"The dual of a vector space. This is the space of linear forms."
	^ '(QQ^3) dual'
]

{ #category : #examples }
FreeHomModule class >> example3 [
	"The basis of the dual vector space of 2x2 matrices with rational coefficients.
	The elements of the basis are the coordinate functions of the original vector space."
	^ '(QQ^(2@2)) dual basis'
]

{ #category : #'instance creation' }
FreeHomModule class >> from: aModule to: anotherModule [
	^ self new
		domain: aModule;
		codomain: anotherModule
]

{ #category : #elements }
FreeHomModule >> ! anObject [
	anObject isMatrix ifTrue: [^ 	LinearMap from: domain to: codomain matrix: anObject].
	anObject isEvaluable ifTrue: [^ self evaluating: anObject].
	(self scalars includes: anObject) ifTrue: [^ self scalar: anObject].
	anObject isInteger ifTrue: [^ self scalar: self scalars ! anObject].
	^ super ! anObject
]

{ #category : #accessing }
FreeHomModule >> codomain [
	^ codomain
]

{ #category : #'accessing-private' }
FreeHomModule >> codomain: aVectorSpace [
	codomain := aVectorSpace
]

{ #category : #basis }
FreeHomModule >> coordinatesOf: aLinearMap [
	"Answer the coordinates of aLinearMap with respect to the domain and codomain basis."

	^ self matrices coordinatesOf: (self matrixOf: aLinearMap)
]

{ #category : #accessing }
FreeHomModule >> domain [
	^ domain
]

{ #category : #'accessing-private' }
FreeHomModule >> domain: aVectorSpace [
	domain := aVectorSpace
]

{ #category : #basis }
FreeHomModule >> e: anInteger [
	"Answer the anInteger-th canonical vector."
	^ self ! (self matrices e: anInteger)
]

{ #category : #elements }
FreeHomModule >> evaluating: aBlock [
	^ domain to: codomain evaluating: aBlock
]

{ #category : #elements }
FreeHomModule >> evaluatingWithArguments: aBlock [
	^ self domain to: self codomain evaluatingWithArguments: aBlock
]

{ #category : #elements }
FreeHomModule >> identity [
	^ self ! self matrices identity
]

{ #category : #testing }
FreeHomModule >> includes: aLinearMap [
	^ (aLinearMap isKindOf: LinearMap) and: [aLinearMap domain = self domain and: [aLinearMap codomain = self codomain]]
]

{ #category : #testing }
FreeHomModule >> isDual [
	"Answer true if the elements of the receiver are linear forms."
	^ codomain isKindOf: RingAsModule
]

{ #category : #testing }
FreeHomModule >> isEndomorphisms [
	^ domain = codomain
]

{ #category : #private }
FreeHomModule >> matrices [
	"Answer the vector space of the matrices associated to the transformations of the receiver."

	^ self scalars raisedTo: (self codomain rank @ self domain rank)
]

{ #category : #private }
FreeHomModule >> matrixOf: aLinearMap [
	"Answer the matrix associated to aLinearMap with respect to the domain and codomain basis."
	(self domain matrix = aLinearMap domain matrix and: [aLinearMap codomain matrix = self codomain matrix])
		ifTrue: [^ aLinearMap matrix].
	^ Matrix columns: (self domain basis collect: [:each| (self codomain coordinatesOf: (aLinearMap value: each))])
]

{ #category : #accessing }
FreeHomModule >> names [
	"Answer a list of names for use instead of the elements of the basis when printing linear maps."
	self isDual ifTrue: [^ self domain coordinateNames ifNil: [(1 to: self domain rank) collect: [:i| 'x', i printString sub]]].
	^ super names
]

{ #category : #operations }
FreeHomModule >> opposite [
	^ self class from: self codomain to: self domain
]

{ #category : #converting }
FreeHomModule >> over: aRing [
	"Answer the change of base ring of the receiver."
	^ self class from: (self domain over: aRing) to: (self codomain over: aRing)
]

{ #category : #morphisms }
FreeHomModule >> pairing [
	"Answer the natural pairing."
	self isDual ifFalse: [DomainError signal].
	^ self propertyAt: #pairing ifAbsentPut: [BilinearMap from: (self, self domain) evaluating: [:each| each first value: each second]]
]

{ #category : #printing }
FreeHomModule >> printOn: aStream [
	self isEndomorphisms
		ifTrue: [aStream nextPutAll: 'End'; nextPutAll: self scalars printText sub; nextPut: $(; print: self domain; nextPut: $)]
		ifFalse: [aStream nextPutAll: 'Hom'; nextPutAll: self scalars printText sub; nextPut: $(; print: self domain; nextPut: $,; print: self codomain; nextPut: $)]
]

{ #category : #basis }
FreeHomModule >> rank [
	^ self domain rank * self codomain rank
]

{ #category : #elements }
FreeHomModule >> scalar: aNumber [
	^ self evaluating: [:x| x * aNumber]
]

{ #category : #accessing }
FreeHomModule >> scalars [
	"Answer the algebraic ambient of scalars."

	^ self domain scalars
]

{ #category : #elements }
FreeHomModule >> x [
	"As for polynomials."
	^ self x: 1
]

{ #category : #elements }
FreeHomModule >> x: i [
	"As for polynomials."
	self isDual ifFalse: [DomainError signal].
	^ self e: i
]

{ #category : #elements }
FreeHomModule >> y [
	"As for polynomials."
	^ self x: 2
]

{ #category : #elements }
FreeHomModule >> z [
	"As for polynomials."
	^ self x: 3
]

{ #category : #elements }
FreeHomModule >> zero [
	^ self ! self matrices zero
]
