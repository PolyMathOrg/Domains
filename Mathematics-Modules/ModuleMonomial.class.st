"
Mnomials in multivariate R-modules (where R is a multivariate ring such as a polynomial ring or an affine ring). They are the product of a monomial in R by a basis element.
"
Class {
	#name : #ModuleMonomial,
	#superclass : #Object,
	#instVars : [
		'parent',
		'monomial',
		'position'
	],
	#category : #'Mathematics-Modules-Multivariate'
}

{ #category : #comparing }
ModuleMonomial >> < aModuleMonomial [
	^ (self >= aModuleMonomial) not
]

{ #category : #comparing }
ModuleMonomial >> <= aModuleMonomial [
	self == aModuleMonomial ifTrue: [^ true].
	^ (self > aModuleMonomial) not
]

{ #category : #comparing }
ModuleMonomial >> = aModuleMonomial [
	^ monomial = aModuleMonomial monomial and: [position = aModuleMonomial position]
]

{ #category : #comparing }
ModuleMonomial >> > aModuleMonomial [
	^ (self compare: aModuleMonomial) > 0
]

{ #category : #comparing }
ModuleMonomial >> >= aModuleMonomial [
	self == aModuleMonomial ifTrue: [^ true].
	^ (self compare: aModuleMonomial) >= 0
]

{ #category : #comparing }
ModuleMonomial >> compare: aModuleMonomial [
	"Answer -1 if the receiver is < than the argument, 0 if they are equal, 1 if it is > than the argument."
	^ self ordering compare: self with: aModuleMonomial
]

{ #category : #comparing }
ModuleMonomial >> hash [
	^ monomial hash + position hash hashMultiply
]

{ #category : #accessing }
ModuleMonomial >> monomial [
	^ monomial
]

{ #category : #'accessing-private' }
ModuleMonomial >> monomial: aMonomial [
	monomial := aMonomial
]

{ #category : #accessing }
ModuleMonomial >> ordering [
	^ parent ordering
]

{ #category : #accessing }
ModuleMonomial >> parent [
	^ parent
]

{ #category : #accessing }
ModuleMonomial >> position [
	^ position
]

{ #category : #'accessing-private' }
ModuleMonomial >> position: anInteger [
	position := anInteger
]

{ #category : #printing }
ModuleMonomial >> printOn: aStream [
	aStream print: monomial; nextPutAll: Character epsilon asText, position printString sub
]

{ #category : #testing }
ModuleMonomial >> | aModuleMonomial [
	"Answer true if the receiver divides the argument."
	^ position = aModuleMonomial position and: [monomial | aModuleMonomial monomial]
]
