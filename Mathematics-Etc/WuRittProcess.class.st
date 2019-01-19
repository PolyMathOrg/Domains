"
I'm the Ritt-Wu process.

Input: a set of polynomials F = {f1,...,fr} in K[x1,...,xn];
Output: an extended characteristic set (or ascending chain, or Wu characteristic set) of F.

"
Class {
	#name : #WuRittProcess,
	#superclass : #Object,
	#instVars : [
		'polynomials',
		'characteristicSet'
	],
	#category : #'Mathematics-Etc'
}

{ #category : #'as yet unclassified' }
WuRittProcess >> characteristicSet [
	characteristicSet isNil ifTrue: [self run].
	^ characteristicSet
]

{ #category : #'as yet unclassified' }
WuRittProcess >> polynomials: aCollection [
	polynomials := aCollection
]

{ #category : #'as yet unclassified' }
WuRittProcess >> run [
	| F G R F2 r |
	F := polynomials.
	G := Set new. R := Set new.
	[F := F ñ R. F2 := R. R := Set new.
	[F2 notEmpty] whileTrue: ["..."].
	F do: [:f| ((G includes: f) or: [(r := G pseudoRemainderOf: f) isZero]) ifFalse: [R add: r]].
	R isEmpty] whileFalse.
	^ characteristicSet := G
]
