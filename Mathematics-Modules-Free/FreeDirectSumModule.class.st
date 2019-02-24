"
Free R-modules defined as the direct sum of other free R-modules.
"
Class {
	#name : #FreeDirectSumModule,
	#superclass : #FreeModule,
	#instVars : [
		'components'
	],
	#category : #'Mathematics-Modules-Free'
}

{ #category : #'instance creation' }
FreeDirectSumModule class >> components: anArray [
	^ self new components: anArray
]

{ #category : #examples }
FreeDirectSumModule class >> example [
	"The direct sum of two vector spaces."
	^ 'QQ^3 ê (QQ^2)'
]

{ #category : #accessing }
FreeDirectSumModule >> arity [
	^ components size
]

{ #category : #converting }
FreeDirectSumModule >> asCartesianProduct [
	^ CartesianProduct components: components
]

{ #category : #accessing }
FreeDirectSumModule >> at: anInteger [
	^ components at: anInteger
]

{ #category : #'accessing-private' }
FreeDirectSumModule >> components [
	^ components
]

{ #category : #'accessing-private' }
FreeDirectSumModule >> components: anArray [
	components := anArray
]

{ #category : #basis }
FreeDirectSumModule >> coordinatesOf: anArray [
	"Answer the coordinates of the argument in the canonical basis."
	| answer |
	components with: anArray do: [:V :v|
		answer := answer isNil ifTrue: [V coordinatesOf: v] ifFalse: [answer, (V coordinatesOf: v)]].
	^ answer
]

{ #category : #basis }
FreeDirectSumModule >> e: anInteger [
	| index answer |
	index := anInteger.
	answer := Array new: self arity.
	1 to: self arity do: [:i| | component n |
		component := self at: i.
		n := component rank.
		answer at: i put:
			((index between: 1 and: n)
				ifTrue: [component e: index]
				ifFalse: [component zero]).
		index := index - n].
	^ answer
]

{ #category : #morphisms }
FreeDirectSumModule >> embedding: i [
	^ ((self at: i) to: self evaluating: [:x| components withIndexCollect: [:each :k| k = i ifTrue: [x] ifFalse: [each zero]]]) name: 'i', i printString
]

{ #category : #testing }
FreeDirectSumModule >> includes: anObject [
	anObject isSequenceable ifFalse: [^ false].
	anObject size = components size ifFalse: [^ false].
	components with: anObject do: [:V :x| (V includes: x) ifFalse: [^ false]].
	^ true
]

{ #category : #testing }
FreeDirectSumModule >> isCoproduct [
	^ true
]

{ #category : #testing }
FreeDirectSumModule >> isFreeModule [
	^ components allSatisfy: [:each| each isFreeModule]
]

{ #category : #converting }
FreeDirectSumModule >> over: aRing [
	"Answer the change of base ring of the receiver."
	^ self class components: (components collect: [:each| each over: aRing])
]

{ #category : #printing }
FreeDirectSumModule >> printOn: aStream [
	components do: [:each| aStream print: each] separatedBy: [aStream nextPut: Character oplus]
]

{ #category : #morphisms }
FreeDirectSumModule >> projection: i [
	^ (self to: (self at: i) evaluating: [:x| x at: i]) name: 'Pi' , i printString
]

{ #category : #basis }
FreeDirectSumModule >> rank [
	^ components sum: [:each| each rank]
]

{ #category : #accessing }
FreeDirectSumModule >> scalars [
	components do: [:any| ^ any scalars].
	^ nil
]
