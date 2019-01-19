"
Group homomorphisms defined as conjugation by a given element.
"
Class {
	#name : #Conjugation,
	#superclass : #GroupMap,
	#instVars : [
		'element',
		'elementInverse'
	],
	#category : #'Mathematics-Groups'
}

{ #category : #'instance creation' }
Conjugation class >> by: anElement in: aGroup [
	^ self new domain: aGroup; codomain: aGroup; element: anElement
]

{ #category : #comparing }
Conjugation >> = anObject [
	(anObject isKindOf: Conjugation) ifFalse: [^ super = anObject].
	^ anObject domain = self domain and: [anObject codomain = self codomain and: [self element = anObject element]]
]

{ #category : #'accessing-private' }
Conjugation >> element [
	^ element
]

{ #category : #'accessing-private' }
Conjugation >> element: anElement [
	element := anElement.
	elementInverse := self domain inverseMap value: element
]

{ #category : #comparing }
Conjugation >> hash [
	^ element hash
]

{ #category : #accessing }
Conjugation >> image [
	^ self codomain
]

{ #category : #arithmetic }
Conjugation >> inverse [
	^ self class by: elementInverse in: self domain
]

{ #category : #accessing }
Conjugation >> kernel [
	^ self domain null
]

{ #category : #operations }
Conjugation >> value: anElement [
	| op |
	op := self domain operation.
	^ op value: {op value: {element. anElement}. elementInverse}
]
