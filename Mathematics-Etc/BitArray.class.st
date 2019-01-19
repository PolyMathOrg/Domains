Class {
	#name : #BitArray,
	#superclass : #ArrayedCollection,
	#instVars : [
		'bytes',
		'length'
	],
	#category : #'Mathematics-Etc'
}

{ #category : #'instance creation' }
BitArray class >> new: anInteger [
	^ self new: anInteger bytes: (ByteArray new: (anInteger / 8) ceiling)
]

{ #category : #'instance creation' }
BitArray class >> new: anInteger bytes: aByteArray [
	^ self basicNew bytes: aByteArray length: anInteger
]

{ #category : #'instance creation' }
BitArray class >> random: anInteger [
	| answer |
	answer := self new: anInteger.
	1 to: answer size do: [:i| answer at: i put: 2 atRandom - 1].
	^ answer
]

{ #category : #arithmetic }
BitArray >> * aBitArray [
	| answer |
	answer := self class new: (self size max: aBitArray size).
	1 to: answer byteSize do: [:i|
		answer byteAt: i put: ((self byteAt: i) bitAnd: (aBitArray byteAt: i))].
	^ answer
]

{ #category : #arithmetic }
BitArray >> + aBitArray [
	| answer |
	answer := self class new: (self size max: aBitArray size).
	1 to: answer byteSize do: [:i|
		answer byteAt: i put: ((self byteAt: i) bitXor: (aBitArray byteAt: i))].
	^ answer
]

{ #category : #converting }
BitArray >> asByteArray [
	^ bytes
]

{ #category : #converting }
BitArray >> asInteger [
	"Answer the receiver as a possitive integer."
	| answer i |
	answer := 0.
	i := 0.
	bytes do: [:each| answer := answer + (each bitShift: i). i := i + 8].
	^ answer
]

{ #category : #accessing }
BitArray >> at: anInteger [
	^ (bytes at: anInteger - 1 // 8 + 1 ifAbsent: [^ 0]) bitAt: anInteger - 1 \\ 8 + 1
]

{ #category : #accessing }
BitArray >> at: anInteger put: aBit [
	| i i0 b |
	i := anInteger - 1 // 8 + 1.
	i0 := anInteger - 1 \\ 8 + 1.
	b := bytes at: i.
	(b bitAt: i0) == aBit
		ifFalse: [b := b bitXor: (1 bitShift: i0-1)].
	bytes at: i put: b.
	^ aBit
]

{ #category : #accessing }
BitArray >> byteAt: anInteger [
	^ bytes at: anInteger ifAbsent: [0]
]

{ #category : #accessing }
BitArray >> byteAt: anInteger put: aByte [
	^ bytes at: anInteger put: aByte
]

{ #category : #initialization }
BitArray >> bytes: aByteArray length: anInteger [
	bytes := aByteArray.
	length := anInteger
]

{ #category : #printing }
BitArray >> printOn: aStream [
	1 to: self size do: [:i| aStream print: (self at: i)]
]

{ #category : #accessing }
BitArray >> size [
	^ length
]
