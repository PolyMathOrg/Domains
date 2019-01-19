Class {
	#name : #MultivariateTuple,
	#superclass : #Tuple,
	#instVars : [
		'parent',
		'components'
	],
	#category : #'Mathematics-Modules-Multivariate'
}

{ #category : #'as yet unclassified' }
MultivariateTuple >> coefficientAt: aModuleMonomial [
	^ (self at: aModuleMonomial position) at: aModuleMonomial monomial
]

{ #category : #'as yet unclassified' }
MultivariateTuple >> leadingCoefficient [
	^ self coefficientAt: self leadingMonomial
]

{ #category : #'as yet unclassified' }
MultivariateTuple >> leadingMonomial [
	^ self ordering leadingMonomialOf: self
]

{ #category : #'as yet unclassified' }
MultivariateTuple >> leadingTerm [
	^ self termAt: self leadingMonomial
]

{ #category : #'as yet unclassified' }
MultivariateTuple >> ordering [
	^ parent ordering
]

{ #category : #'as yet unclassified' }
MultivariateTuple >> parent [
	^ parent
]

{ #category : #'as yet unclassified' }
MultivariateTuple >> termAt: aModuleMonomial [
	^ (self at: aModuleMonomial position) termAt: aModuleMonomial monomial
]
