"
Cartesian products of sets. See Domain>>,.

Example:
	(ZZ, QQ)

Note that message #◊ is often used for the direct product (of rings or groups, for example), but #, always gives the cartesian product of the underlying sets.

References:
	https://en.wikipedia.org/wiki/Cartesian_product

"
Class {
	#name : #CartesianProduct,
	#superclass : #Domain,
	#instVars : [
		'components'
	],
	#category : #'Mathematics-Sets'
}

{ #category : #'instance creation' }
CartesianProduct class >> components: anArray [
	^ self new components: anArray
]

{ #category : #examples }
CartesianProduct class >> example [
	"The cartesian product of the ring of rational integers
	and the field of rational numbers (as sets)."

	^ ZZ , QQ
]

{ #category : #operations }
CartesianProduct >> , aDomain [
	^ aDomain class == self class
		ifTrue: [self class components: components, aDomain components]
		ifFalse: [self class components: (components copyWith: aDomain)]
]

{ #category : #comparing }
CartesianProduct >> = anObject [
	^ (anObject isKindOf: CartesianProduct)
		and: [ components = anObject components ]
]

{ #category : #accessing }
CartesianProduct >> arity [
	^ components size
]

{ #category : #accessing }
CartesianProduct >> at: anInteger [
	^ components at: anInteger
]

{ #category : #random }
CartesianProduct >> atRandom: aRandom [
	^ components collect: [:each| each atRandom: aRandom]
]

{ #category : #random }
CartesianProduct >> atRandom: aRandom bits: bitSize [
	| n |
	n := bitSize / components size.
	^ components collect: [ :each | each atRandom: aRandom bits: n ]
]

{ #category : #'accessing-private' }
CartesianProduct >> components [
	^ components
]

{ #category : #'accessing-private' }
CartesianProduct >> components: anArray [
	components := anArray
]

{ #category : #enumerating }
CartesianProduct >> do: aBlock [
	(self components allSatisfy: [ :each | each isFinite ])
		ifFalse: [ ^ self upTo: self size rank: self arity do: aBlock ].
	self upToComponent: self arity do: aBlock
]

{ #category : #comparing }
CartesianProduct >> hash [
	^ components hash
]

{ #category : #testing }
CartesianProduct >> includes: anObject [
	anObject isSequenceable
		ifFalse: [ ^ false ].
	components size = anObject size
		ifFalse: [ ^ false ].
	1 to: components size do: [ :i | 
		((components at: i) includes: (anObject at: i))
			ifFalse: [ ^ false ] ].
	^ true
]

{ #category : #testing }
CartesianProduct >> isProduct [
	^ true
]

{ #category : #printing }
CartesianProduct >> printOn: aStream [
	components
		do: [ :each | aStream print: each ]
		separatedBy: [ aStream nextPut: $× ]
]

{ #category : #morphisms }
CartesianProduct >> projection: i [
	^ (self to: (self at: i) evaluating: [:x| x at: i]) name: Character pi asText, i printText sub
]

{ #category : #accessing }
CartesianProduct >> size [
	^ components product: [:each| each size]
]

{ #category : #enumerating }
CartesianProduct >> upTo: max rank: n do: aBlock [
	| k |
	self notYetImplemented.
	n = 0
		ifTrue: [ ^ aBlock value: #() ].
	k := 1.
	(self at: n)
		upTo: max
		do: [ :s | 
			self
				upTo: k
				rank: n - 1
				do: [ :p | 
					aBlock
						value:
							{p.
							s}
					"(self at: n) upTo: k-1 do: [:t| (p includes: s) ifTrue: [aBlock value: (p,t)]]" ].
			k := k + 1 ]
]

{ #category : #enumerating }
CartesianProduct >> upToComponent: k do: aBlock [
	k = 0
		ifTrue: [ aBlock value: Array new.
			^ self ].
	self
		upToComponent: k - 1
		do: [ :each | (self at: k) do: [ :last | aBlock value: (each copyWith: last) ] ]
]
