"
Groups of Dirichlet characters modulo n. My elements are group homomorphisms from (Z/nZ)* to C* (see DirichletCharacter).
"
Class {
	#name : #DirichletGroup,
	#superclass : #Group,
	#category : #'Mathematics-Modular Forms'
}

{ #category : #'instance creation' }
DirichletGroup class >> new: anInteger [
	^ self new modulus: anInteger
]

{ #category : #'instance creation' }
DirichletGroup class >> new: anInteger to: aCodomain [
	^ self new modulus: anInteger; codomain: aCodomain
]

{ #category : #'as yet unclassified' }
DirichletGroup >> codomain [
	"Answer the codomain of the characters."
	^ self propertyAt: #codomain ifAbsentPut: [CyclotomicField new: self domain exponent]
]

{ #category : #'as yet unclassified' }
DirichletGroup >> codomain: aCodomain [
	self propertyAt: #codomain put: aCodomain
]

{ #category : #'as yet unclassified' }
DirichletGroup >> decomposition [
	| answer |
	answer := OrderedCollection new.
	self modulus factors withOccurrencesDo:
		[:p :e| answer add: ('self class new: p^e to: self codomain')].
	^ answer
]

{ #category : #'as yet unclassified' }
DirichletGroup >> domain [
	^ self propertyAt: #domain
]

{ #category : #'as yet unclassified' }
DirichletGroup >> hash [
	^ self domain hash hashMultiply + self codomain hash
]

{ #category : #'as yet unclassified' }
DirichletGroup >> modulus [
	^ self domain modulus
]

{ #category : #'as yet unclassified' }
DirichletGroup >> modulus: anInteger [
	self propertyAt: #domain put: (ZZ / anInteger) units
]

{ #category : #'as yet unclassified' }
DirichletGroup >> printOn: aStream [
	aStream nextPut: $(; print: ZZ; nextPut: $/; print: self modulus; nextPutAll: ')', '*' super
]
