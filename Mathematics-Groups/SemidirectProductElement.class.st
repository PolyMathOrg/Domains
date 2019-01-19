Class {
	#name : #SemidirectProductElement,
	#superclass : #Object,
	#instVars : [
		'parent',
		'left',
		'right'
	],
	#category : #'Mathematics-Groups'
}

{ #category : #arithmetic }
SemidirectProductElement >> * aSemidirectProduct [
	^ self parent
		project:
			{parent left operation value: {left. aSemidirectProduct left}.
			parent right operation value: {parent action value: {aSemidirectProduct left. right}. aSemidirectProduct right}}
]

{ #category : #arithmetic }
SemidirectProductElement >> / aSemidirectProduct [
	^ self * aSemidirectProduct reciprocal
]

{ #category : #constants }
SemidirectProductElement >> identity [
	^ self parent identity
]

{ #category : #accessing }
SemidirectProductElement >> left [
	"Answer the left component of the receiver."
	^ left
]

{ #category : #'accessing-private' }
SemidirectProductElement >> left: anObject [
	left := anObject
]

{ #category : #private }
SemidirectProductElement >> parent [
	^ parent
]

{ #category : #'accessing-private' }
SemidirectProductElement >> parent: aSemidirectProductGroup [
	parent := aSemidirectProductGroup
]

{ #category : #printing }
SemidirectProductElement >> printOn: aStream [
	aStream nextPut: $(; print: left; nextPutAll: ', '; print: right; nextPut: $)
]

{ #category : #arithmetic }
SemidirectProductElement >> reciprocal [
	| leftInverse rightInverse |
	leftInverse := parent left inverseMap value: left.
	rightInverse := parent right inverseMap value: right.
	^ parent project: {leftInverse. parent right inverseMap value: (parent action value: {leftInverse. rightInverse})}
]

{ #category : #accessing }
SemidirectProductElement >> right [
	"Answer the right component of the receiver."
	^ right
]

{ #category : #'accessing-private' }
SemidirectProductElement >> right: anObject [
	right := anObject
]
