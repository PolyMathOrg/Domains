Class {
	#name : #SturmChain,
	#superclass : #Object,
	#instVars : [
		'chain'
	],
	#category : #'Mathematics-Etc'
}

{ #category : #'as yet unclassified' }
SturmChain class >> on: aPolynomial [
	^ self basicNew setPolynomial: aPolynomial
]

{ #category : #'as yet unclassified' }
SturmChain >> countSignChanges: signs [
	| x count |
	x := signs first.
	count := 0.
	signs do: [ :each | each sign ~= x ifTrue: [ count := count + 1 ]. x := each sign ].
	^ count
]

{ #category : #'as yet unclassified' }
SturmChain >> numberOfRealRoots [
	^ self numberOfSignChangesAtMinusInfinity - self numberOfSignChangesAtInfinity
]

{ #category : #'as yet unclassified' }
SturmChain >> numberOfSignChangesAt: aNumber [
	^ self countSignChanges: (chain collect: [ :each | (each value: aNumber) sign])
]

{ #category : #'as yet unclassified' }
SturmChain >> numberOfSignChangesAtInfinity [
	^ self countSignChanges: (chain collect: [ :each | each leadingCoefficient sign ])
]

{ #category : #'as yet unclassified' }
SturmChain >> numberOfSignChangesAtMinusInfinity [
	^ self countSignChanges: (chain collect: [ :each | each leadingCoefficient sign * (each degree odd ifTrue: [-1] ifFalse: [1])])
]

{ #category : #'as yet unclassified' }
SturmChain >> polynomial [
	^ chain first
]

{ #category : #'as yet unclassified' }
SturmChain >> polynomial: aPolynomial [
	chain := OrderedCollection with: aPolynomial with: aPolynomial derivative.
	[ chain last degree > 0 ] whileTrue: [ chain add: ((chain at: chain size - 1) \\ chain last) negated ]
]
