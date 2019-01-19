"
Generalizations of monomial orderings to multivariate R-modules (where R is a multivariate ring such as a polynomial ring or an affine ring). They extend the ordering of the coefficients ring R to elements of the R-module.
"
Class {
	#name : #ModuleMonomialOrdering,
	#superclass : #Object,
	#category : #'Mathematics-Modules-Multivariate-Orderings'
}

{ #category : #'as yet unclassified' }
ModuleMonomialOrdering class >> pos [
	^ PositionOverTermOrdering new
]

{ #category : #'as yet unclassified' }
ModuleMonomialOrdering class >> top [
	^ TermOverPositionOrdering new
]

{ #category : #ordering }
ModuleMonomialOrdering >> compare: aModuleMonomial with: anotherModuleMonomial [
	^ self subclassResponsibility
]

{ #category : #ordering }
ModuleMonomialOrdering >> leadingMonomialOf: aPolynomialTuple [
	self subclassResponsibility
]

{ #category : #ordering }
ModuleMonomialOrdering >> printOn: aStream [
	self type isNil
		ifTrue: [super printOn: aStream]
		ifFalse: [aStream nextPutAll: self type]
]

{ #category : #ordering }
ModuleMonomialOrdering >> type [
	^ nil
]
