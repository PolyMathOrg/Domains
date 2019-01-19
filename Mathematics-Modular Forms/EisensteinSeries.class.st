Class {
	#name : #EisensteinSeries,
	#superclass : #ModularForm,
	#instVars : [
		'weight'
	],
	#category : #'Mathematics-Modular Forms'
}

{ #category : #'as yet unclassified' }
EisensteinSeries class >> new: anInteger [
	^ self new weight: anInteger
]

{ #category : #'as yet unclassified' }
EisensteinSeries >> printOn: aStream [
	aStream nextPutAll: 'G', weight printString sub
]

{ #category : #'as yet unclassified' }
EisensteinSeries >> weight [
	^ weight
]

{ #category : #'as yet unclassified' }
EisensteinSeries >> weight: anInteger [
	(anInteger even and: [anInteger >= 4]) ifFalse: [^ self error: 'the weight must be even >= 4'].
	weight := anInteger
]
