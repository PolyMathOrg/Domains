"
Semidirect products of groups.
"
Class {
	#name : #SemidirectProductGroup,
	#superclass : #Group,
	#instVars : [
		'left',
		'right',
		'action'
	],
	#category : #'Mathematics-Groups'
}

{ #category : #'instance creation' }
SemidirectProductGroup class >> left: aGroup right: anotherGroup action: anAction [
	^ self new left: aGroup; right: anotherGroup; action: anAction
]

{ #category : #accessing }
SemidirectProductGroup >> action [
	^ action
]

{ #category : #'accessing-private' }
SemidirectProductGroup >> action: anAction [
	action := anAction
]

{ #category : #accessing }
SemidirectProductGroup >> arity [
	^ 2
]

{ #category : #converting }
SemidirectProductGroup >> asCartesianProduct [
	^ (left, right)
]

{ #category : #random }
SemidirectProductGroup >> atRandom: aRandom [
	^ self project: (self asCartesianProduct atRandom: aRandom)
]

{ #category : #random }
SemidirectProductGroup >> atRandom: aRandom bits: bitSize [
	^ self project: (self asCartesianProduct atRandom: aRandom bits: bitSize)
]

{ #category : #enumerating }
SemidirectProductGroup >> do: aBlock [
	left do: [:g| right do: [:h| aBlock value: (self project: {g.h})]]
]

{ #category : #accessing }
SemidirectProductGroup >> identity [
	^ self project: {left identity. right identity}
]

{ #category : #testing }
SemidirectProductGroup >> isProduct [
	^ true
]

{ #category : #accessing }
SemidirectProductGroup >> left [
	^ left
]

{ #category : #'accessing-private' }
SemidirectProductGroup >> left: aGroup [
	left := aGroup
]

{ #category : #printing }
SemidirectProductGroup >> printOn: aStream [
	aStream print: left; nextPutAll: ' X| '; print: right
]

{ #category : #morphisms }
SemidirectProductGroup >> project: anArray [
	"Project a cartesian product of two elements to their semidirect product."
	^ SemidirectProductElement new
		parent: self;
		left: (anArray at: 1);
		right: (anArray at: 2)
]

{ #category : #morphisms }
SemidirectProductGroup >> projection [
	"Answer the projection from the cartesian product of two groups to their semidirect product."
	^ ((left, right) to: self evaluating: [:each| self project: each]) name: Character pi asString
]

{ #category : #accessing }
SemidirectProductGroup >> right [
	^ right
]

{ #category : #'accessing-private' }
SemidirectProductGroup >> right: aGroup [
	right := aGroup
]

{ #category : #accessing }
SemidirectProductGroup >> size [
	^ left size * right size
]
