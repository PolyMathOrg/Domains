"
An Iterator is a read-only collection that evaluates a block to yield the elements of the collection.
"
Class {
	#name : #Iterator,
	#superclass : #Collection,
	#instVars : [
		'block'
	],
	#category : #'Mathematics-Kernel-Support'
}

{ #category : #'instance creation' }
Iterator class >> on: aBlock [
	^ self new block: aBlock
]

{ #category : #'instance creation' }
Iterator class >> on: anObject performing: aSymbol [
	^ self new block: [:aBlock| anObject perform: aSymbol with: aBlock]
]

{ #category : #adding }
Iterator >> add: anObject [
	"Iterators are read-only"
	self shouldNotImplement
]

{ #category : #private }
Iterator >> block: aBlock [
	block := aBlock
]

{ #category : #enumerating }
Iterator >> do: aBlock [
	block value: aBlock
]

{ #category : #enumerating }
Iterator >> findFirst: aBlock [
	"Answer the index of the first element of the receiver
	for which aBlock evaluates as true."

	| index |
	index := 1.
	self do: [ :el | (aBlock value: el) ifTrue: [^index].  index := index + 1].
	^0
]

{ #category : #enumerating }
Iterator >> findLast: aBlock [
	"Answer the index of the last element of the receiver
	for which aBlock evaluates as true."

	| index last |
	index := 1.
	last := 0.
	self do: [ :el | (aBlock value: el) ifTrue: [last := index].  index := index + 1].
	^last
]

{ #category : #copying }
Iterator >> first: n [
	"Answer the first n elements of the receiver.
	Raise an error if there are not enough elements."
	| answer |
	answer := self species new: n.
	self do: [:each|
		answer size = n ifTrue: [^ answer].
		answer add: each].
	^ self error: 'not enough elements'
]

{ #category : #accessing }
Iterator >> identityIndexOf: anElement [ 
	"Answer the identity index of anElement within the receiver.  If the receiver does
	not contain anElement, answer 0."

	^self identityIndexOf: anElement ifAbsent: [0]
]

{ #category : #accessing }
Iterator >> identityIndexOf: anElement ifAbsent: exceptionBlock [ 
	"Answer the identity index of anElement within the receiver.  If the receiver does
	not contain anElement, answer the result of evaluating the exceptionBlock."

	| index |
	index := 1.
	self do: [ :el | el == anElement ifTrue: [^index].  index := index + 1].
	^exceptionBlock value
]

{ #category : #accessing }
Iterator >> indexOf: anElement [ 
	"Answer the index of anElement within the receiver.  If the receiver does
	not contain anElement, answer 0."

	^self indexOf: anElement ifAbsent: [0]
]

{ #category : #accessing }
Iterator >> indexOf: anElement ifAbsent: exceptionBlock [ 
	"Answer the index of anElement within the receiver.  If the receiver does
	not contain anElement, answer the result of evaluating the exceptionBlock."

	| index |
	index := 1.
	self do: [ :el | el = anElement ifTrue: [^index].  index := index + 1].
	^exceptionBlock value
]

{ #category : #enumerating }
Iterator >> keysAndValuesDo: aBlock [  
	"Evaluate aBlock with each of the receiver's key/value pairs
	(e.g. indexes and elements) as the arguments."

	| index |
	index := 1.
	self do: [:el | aBlock value: index value: el.  index := index + 1]
]

{ #category : #removing }
Iterator >> remove: oldObject ifAbsent: anExceptionBlock [ 
	"Iterators are read-only."
	self shouldNotImplement
]

{ #category : #private }
Iterator >> species [
	^OrderedCollection
]
