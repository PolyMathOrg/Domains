Class {
	#name : #RandomGenerator,
	#superclass : #Object,
	#instVars : [
		'domain',
		'bits',
		'random'
	],
	#category : #'Mathematics-Kernel-Support'
}

{ #category : #'instance creation' }
RandomGenerator class >> on: aDomain [
	| random |
	random := Random new.
	80 timesRepeat: [random next].
	^ self on: aDomain random: random
]

{ #category : #'instance creation' }
RandomGenerator class >> on: aDomain random: aRandom [
	^ self new domain: aDomain; random: aRandom
]

{ #category : #accessing }
RandomGenerator >> bits: anInteger [
	anInteger >= 1 ifFalse: [^ self error: 'bitsize must be >= 1'].
	bits := anInteger
]

{ #category : #generating }
RandomGenerator >> distinct: n [
	"Answer n distinct elements choosen at random."
	| answer |
	answer := Set new: n.
	[answer size < n] whileTrue: [answer add: self next].
	^ answer
]

{ #category : #accessing }
RandomGenerator >> domain [
	^ domain
]

{ #category : #private }
RandomGenerator >> domain: aDomain [
	domain := aDomain.
	bits := Infinity positive
]

{ #category : #generating }
RandomGenerator >> next [
	^ domain atRandom: random bits: bits
]

{ #category : #generating }
RandomGenerator >> next: n [
	^ (1 to: n) collect: [:each| self next]
]

{ #category : #printing }
RandomGenerator >> printOn: aStream [
	aStream nextPutAll: 'Random('; print: domain; nextPut: $)
]

{ #category : #private }
RandomGenerator >> random: aRandom [
	random := aRandom
]
