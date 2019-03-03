Extension { #name : #Collection }

{ #category : #'*mathematics' }
Collection >> < aCollection [
	"Answer true if the receiver is a proper subcollection of aCollection."
	^ self <= aCollection and: [self size < aCollection size]
]

{ #category : #'*mathematics' }
Collection >> <= aCollection [
	"Answer true if the receiver is a subcollection of aCollection."
	(aCollection isKindOf: self species) ifFalse: [^ false].
	self size <= aCollection size ifFalse: [^ false].
	^ self allSatisfy: [:each| aCollection includes: each]
]

{ #category : #'*mathematics' }
Collection >> > aCollection [
	"Answer true if aCollection is a proper subcollection of the receiver."
	^ aCollection < self
]

{ #category : #'*mathematics' }
Collection >> >= aCollection [
	"Answer true if aCollection is a subcollection of the receiver."
	^ aCollection <= self
]

{ #category : #'*mathematics' }
Collection >> \ aCollection [
	"Answer the complement of aCollection in the receiver."
	^ self reject: [:each| aCollection includes: each]
]

{ #category : #'*mathematics-instance creation' }
Collection class >> accumulate: iteratorBlock [
	"Return a new instance of myself by evaluating the iteratorBlock.
	Examples:
		| x oc set |
		x := #( 1 2 3 4 1 ).
		oc := OrderedCollection accumulate: [ :incBlock | x do: incBlock].
		Transcript cr; show: oc printString.
		set := Set accumulate: [ :incBlock | x do: incBlock].
		Transcript cr; show: set printString"

	| collection | 
	collection := self new.
	iteratorBlock value: [ :element | collection add: element].
	^collection
]

{ #category : #'*mathematics-instance creation' }
Collection class >> accumulate: iteratorSymbol on: collection [
	"Return a new instance of myself by sending the iteratorSymbol to the collection.
	Examples:
		| x oc set |
		x := #( 1 2 3 4 1 ).
		oc := OrderedCollection accumulate: #do: on: x.
		Transcript cr; show: oc printString.
		set := Set accumulate: #do: on: x.
		Transcript cr; show: set printString"

	| newCollection | 
	newCollection := self new.
	collection perform: iteratorSymbol with: [ :element | newCollection add: element].
	^newCollection
]

{ #category : #'*mathematics' }
Collection >> anyIfNone: aBlock [
	"Answer a representative sample of the receiver. This method can
	be helpful when needing to preinfer the nature of the contents of 
	semi-homogeneous collections."

	self do: [:each | ^ each].
	^aBlock value
]

{ #category : #'*mathematics' }
Collection >> apply: aFunction [
	^ self collect: aFunction
]

{ #category : #'*mathematics' }
Collection >> atRandom: aRandom bits: bitSize [
	^ self atRandom: aRandom
]

{ #category : #'*mathematics' }
Collection >> atRandomBits: anInteger [
	^ self atRandom
]

{ #category : #'*mathematics' }
Collection >> copyEmpty [
	^ self species new
]

{ #category : #'*mathematics' }
Collection >> copyEmpty: anInteger [
	^ self species new: anInteger
]

{ #category : #'*mathematics' }
Collection >> intersects: aCollection [
	^ self anySatisfy: [:any| aCollection includes: any]
]

{ #category : #'*mathematics' }
Collection >> isFinite [
	^ true
]

{ #category : #'*mathematics' }
Collection >> isInfinite [
	^ false
]

{ #category : #'*mathematics' }
Collection >> plot: aFunction [
	^ FunctionPlotMorph new evaluationPoints: self; function: aFunction
]

{ #category : #'*mathematics' }
Collection >> product [
	^ self fold: [ :a :b | a * b ]
]

{ #category : #'*mathematics' }
Collection >> product: aBlock [
	^ (self collect:aBlock) fold: [ :a :b | a * b ]
]
