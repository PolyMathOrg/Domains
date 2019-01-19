"
Algebraic extensions seen as modules or vector spaces. See AlgebraicExtension.
"
Class {
	#name : #AlgebraicExtensionAsModule,
	#superclass : #FreeModule,
	#instVars : [
		'extension'
	],
	#category : #'Mathematics-Fields'
}

{ #category : #'instance creation' }
AlgebraicExtensionAsModule class >> on: anAlgebraicExtension [
	^ self new extension: anAlgebraicExtension
]

{ #category : #basis }
AlgebraicExtensionAsModule >> coordinatesOf: anElement [
	"why not just anElement representative coefficients? must complete with 0"
	^ self scalars tuple: self rank evaluating: [:i| anElement representative coefficientAtDegree: i-1]
]

{ #category : #basis }
AlgebraicExtensionAsModule >> e: anInteger [
	^ 'extension x ^ (anInteger-1)'
]

{ #category : #initialization }
AlgebraicExtensionAsModule >> extension: anAlgebraicExtension [
	extension := anAlgebraicExtension
]

{ #category : #basis }
AlgebraicExtensionAsModule >> rank [
	^ extension degree
]

{ #category : #accessing }
AlgebraicExtensionAsModule >> scalars [
	^ extension scalars
]

{ #category : #elements }
AlgebraicExtensionAsModule >> zero [
	^ extension zero
]
