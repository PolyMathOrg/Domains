Class {
	#name : #MutualAssociation,
	#superclass : #Association,
	#category : #'Mathematics-Graphs-Parts'
}

{ #category : #'instance creation' }
MutualAssociation class >> newFrom: anAssociation [
	^ self with: anAssociation key with: anAssociation value
]

{ #category : #'instance creation' }
MutualAssociation class >> with: anObject with: anotherObject [
	^ self key: anObject value: anotherObject
]

{ #category : #comparing }
MutualAssociation >> = anAssociation [
	(anAssociation isKindOf: Association)
		ifFalse: [^ false].
	^ key = anAssociation key
		ifTrue: [value = anAssociation value]
		ifFalse: [value = anAssociation key and: [key = anAssociation value]]
]

{ #category : #comparing }
MutualAssociation >> hash [
	^ key hash bitXor: value hash
]

{ #category : #printing }
MutualAssociation >> printOn: aStream [
	aStream
		print: key;
		nextPutAll: ' <-> ';
		print: value
]
