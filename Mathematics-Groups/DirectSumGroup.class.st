"
Direct sums of abelian groups.

Direct sums are equipped with projection homomorphisms to the i-th component (>>projection:) and coprojections or embeddings from the i-th component (>>embedding:).
"
Class {
	#name : #DirectSumGroup,
	#superclass : #AbelianGroup,
	#instVars : [
		'components'
	],
	#category : #'Mathematics-Groups-Abelian'
}

{ #category : #'instance creation' }
DirectSumGroup class >> components: anArray [
	^ self new components: anArray
]

{ #category : #accessing }
DirectSumGroup >> ambient [
	^ self propertyAt: #ambient ifAbsentPut: [(components noneSatisfy: [:each| each isEmbedded]) ifTrue: [self] ifFalse: [self class components: (components collect: [:each| each ambient])]]
]

{ #category : #accessing }
DirectSumGroup >> arity [
	^ components size
]

{ #category : #converting }
DirectSumGroup >> asCartesianProduct [
	^ CartesianProduct components: components
]

{ #category : #accessing }
DirectSumGroup >> at: anInteger [
	^ components at: anInteger
]

{ #category : #random }
DirectSumGroup >> atRandom: aRandom [
	^ components collect: [:each| each atRandom: aRandom]
]

{ #category : #random }
DirectSumGroup >> atRandom: aRandom bits: bitSize [
	| n |
	n := bitSize / self arity.
	^ components collect: [:each| each atRandom: aRandom bits: n]
]

{ #category : #'accessing-private' }
DirectSumGroup >> components [
	^ components
]

{ #category : #'accessing-private' }
DirectSumGroup >> components: anArray [
	components := anArray
]

{ #category : #testing }
DirectSumGroup >> contains: anElement [
	components with: anElement do: [:V :x| (V contains: x) ifFalse: [^ false]].
	^ true
]

{ #category : #morphisms }
DirectSumGroup >> embedding: i [
	^ ((self at: i) to: self evaluating: [:x| components withIndexCollect: [:each :k| k = i ifTrue: [x] ifFalse: [each identity]]]) name: 'i', i asString
]

{ #category : #accessing }
DirectSumGroup >> identity [
	^ components collect: [:each| each identity]
]

{ #category : #testing }
DirectSumGroup >> includes: anObject [
	anObject isSequenceable ifFalse: [^ false].
	anObject size = components size ifFalse: [^ false].
	components with: anObject do: [:V :x| (V includes: x) ifFalse: [^ false]].
	^ true
]

{ #category : #testing }
DirectSumGroup >> isCoproduct [
	^ true
]

{ #category : #testing }
DirectSumGroup >> isProduct [
	^ true
]

{ #category : #printing }
DirectSumGroup >> printOn: aStream [
	components do: [:each| aStream print: each] separatedBy: [aStream nextPut: Character oplus]
]

{ #category : #morphisms }
DirectSumGroup >> projection: i [
	^ (self to: (self at: i) evaluating: [:x| x at: i]) name: 'Pi', i asString
]

{ #category : #accessing }
DirectSumGroup >> size [
	^ components product: [:each| each size]
]

{ #category : #accessing }
DirectSumGroup >> torsion [
	^ DirectSumGroup components: (components collect: [:each| each torsion])
]
