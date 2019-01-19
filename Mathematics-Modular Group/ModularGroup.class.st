"
The special linear group SL(2,Z).
"
Class {
	#name : #ModularGroup,
	#superclass : #PrincipalCongruenceSubgroup,
	#category : #'Mathematics-Modular Group'
}

{ #category : #'as yet unclassified' }
ModularGroup >> S [
	^ ModularMap S
]

{ #category : #'as yet unclassified' }
ModularGroup >> T [
	^ ModularMap T
]

{ #category : #'as yet unclassified' }
ModularGroup >> T: n [
	^ ModularMap a: 1 b: n c: 0 d: 1
]

{ #category : #'as yet unclassified' }
ModularGroup >> generators [
	^ {ModularMap T. ModularMap S}
]

{ #category : #'as yet unclassified' }
ModularGroup >> level [
	^ 1
]

{ #category : #'as yet unclassified' }
ModularGroup >> level: anInteger [
	^ self shouldNotImplement
]

{ #category : #'as yet unclassified' }
ModularGroup >> printOn: aStream [
	aStream nextPut: Character Gamma
]

{ #category : #'as yet unclassified' }
ModularGroup >> reduce: aPoint [
	"Given a point in the upper half plane, return an element of the receiver that maps the point to a representative in the standard fundamental domain.
	Reference: Henri Cohen, 'A Course in Computational Algebraic Number Theory', Algorithm 7.4.2."
	| tau A n m |
	tau := aPoint.
	A := self identity.
	[n := tau real rounded.
	tau := tau - n.
	A := '(self T: n negated) î A'.
	m := tau * tau conjugated.
	m >= 1 ifTrue: [^ {tau. A}].
	tau := tau conjugated negated / m.
	'A := self S î A'] repeat
]
