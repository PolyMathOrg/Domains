"
Fields of p-adic numbers Qp. These are fraction fields of rings of p-adic integers. See AdicIntegerRing and AdicNumber.
"
Class {
	#name : #AdicField,
	#superclass : #Ring,
	#instVars : [
		'integers'
	],
	#category : #'Mathematics-Etc-Fields-PAdics'
}

{ #category : #'instance creation' }
AdicField class >> p: aPrime [
	^ self new p: aPrime
]

{ #category : #'as yet unclassified' }
AdicField >> characteristic [
	^ 0
]

{ #category : #'as yet unclassified' }
AdicField >> integers [
	^ integers
]

{ #category : #'as yet unclassified' }
AdicField >> isField [
	^ true
]

{ #category : #'as yet unclassified' }
AdicField >> p [
	^ self integers p
]

{ #category : #'as yet unclassified' }
AdicField >> p: aPrime [
	integers := AdicIntegerRing p: aPrime
]

{ #category : #'as yet unclassified' }
AdicField >> printOn: aStream [
	aStream print: QQ; nextPutAll: self p printString sub
]
