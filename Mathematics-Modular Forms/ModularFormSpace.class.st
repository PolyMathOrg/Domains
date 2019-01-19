Class {
	#name : #ModularFormSpace,
	#superclass : #FreeModule,
	#instVars : [
		'weight',
		'group'
	],
	#category : #'Mathematics-Modular Forms'
}

{ #category : #'as yet unclassified' }
ModularFormSpace class >> new: anInteger [
	^ self new weight: anInteger
]

{ #category : #'as yet unclassified' }
ModularFormSpace >> printOn: aStream [
	aStream nextPut: $M; nextPutAll: weight printString sub; nextPut: $(; print: group; nextPut: $)
]

{ #category : #'as yet unclassified' }
ModularFormSpace >> scalars [
	^ CC
]

{ #category : #'as yet unclassified' }
ModularFormSpace >> weight [
	^ weight
]

{ #category : #'as yet unclassified' }
ModularFormSpace >> weight: anInteger [
	weight := anInteger
]
