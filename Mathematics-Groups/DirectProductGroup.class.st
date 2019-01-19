"
Direct products of groups. Elements are tuples, and multiplication and addition are defined component wise.
"
Class {
	#name : #DirectProductGroup,
	#superclass : #Group,
	#instVars : [
		'components'
	],
	#category : #'Mathematics-Groups'
}

{ #category : #'instance creation' }
DirectProductGroup class >> components: anArray [
	^ self new components: anArray
]

{ #category : #comparing }
DirectProductGroup >> = anObject [
	^ (anObject isKindOf: DirectProductGroup) and: [anObject components = components]
]

{ #category : #accessing }
DirectProductGroup >> ambient [
	^ self propertyAt: #ambient ifAbsentPut: [(components noneSatisfy: [:each| each isEmbedded]) ifTrue: [self] ifFalse: [self class components: (components collect: [:each| each ambient])]]
]

{ #category : #accessing }
DirectProductGroup >> arity [
	^ components size
]

{ #category : #converting }
DirectProductGroup >> asCartesianProduct [
	^ CartesianProduct components: components
]

{ #category : #accessing }
DirectProductGroup >> at: anInteger [
	^ components at: anInteger
]

{ #category : #random }
DirectProductGroup >> atRandom: aRandom [
	^ self asCartesianProduct atRandom: aRandom
]

{ #category : #random }
DirectProductGroup >> atRandom: aRandom bits: bits [
	^ self asCartesianProduct atRandom: aRandom bits: bits
]

{ #category : #'accessing-private' }
DirectProductGroup >> components [
	^ components
]

{ #category : #'accessing-private' }
DirectProductGroup >> components: anArray [
	components := anArray
]

{ #category : #private }
DirectProductGroup >> computeGenerators [
	| answer |
	answer := OrderedCollection new.
	1 to: self arity do: [:i|
		| p |
		p := self projection: i.
		(self at: i) generators do: [:each| answer add: (p value: each)]].
	^ answer
]

{ #category : #enumerating }
DirectProductGroup >> do: aBlock [
	self asCartesianProduct do: aBlock
]

{ #category : #morphisms }
DirectProductGroup >> embedding: i [
	^ ((self at: i) to: self evaluating: [:x| components withIndexCollect: [:each :k| k = i ifTrue: [x] ifFalse: [each identity]]]) name: 'i', i printText sub
]

{ #category : #comparing }
DirectProductGroup >> hash [
	^ components hash
]

{ #category : #accessing }
DirectProductGroup >> identity [
	^ components collect: [:each| each identity]
]

{ #category : #testing }
DirectProductGroup >> includes: anObject [
	anObject isSequenceable ifFalse: [^ false].
	anObject size = components size ifFalse: [^ false].
	components with: anObject do: [:G :x| (G includes: x) ifFalse: [^ false]].
	^ true
]

{ #category : #accessing }
DirectProductGroup >> inverseMap [
	^ self to: self evaluating: [:x| x withIndexCollect: [:xi :i| (self at: i) inverseMap value: xi]]
]

{ #category : #testing }
DirectProductGroup >> isProduct [
	^ true
]

{ #category : #accessing }
DirectProductGroup >> operation [
	^ GroupAction from: (self, self) to: self evaluatingWithArguments: [:x :y| x withIndexCollect: [:xi :i| (self at: i) operation value: {xi. y at: i}]]
]

{ #category : #printing }
DirectProductGroup >> printOn: aStream [
	components do: [:each| aStream print: each] separatedBy: [aStream nextPut: Character times]
]

{ #category : #morphisms }
DirectProductGroup >> projection: i [
	^ (self to: (self at: i) evaluating: [:x| x at: i]) name: Character pi asText, i printText sub
]

{ #category : #accessing }
DirectProductGroup >> size [
	^ components product: [:each| each size]
]
