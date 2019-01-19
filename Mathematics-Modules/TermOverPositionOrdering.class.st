Class {
	#name : #TermOverPositionOrdering,
	#superclass : #ModuleMonomialOrdering,
	#category : #'Mathematics-Modules-Multivariate-Orderings'
}

{ #category : #'as yet unclassified' }
TermOverPositionOrdering >> compare: aModuleMonomial with: anotherModuleMonomial [
	| result |
	(result := aModuleMonomial monomial compare: anotherModuleMonomial monomial) == 0
		ifFalse: [^ result].
	^ (aModuleMonomial position - anotherModuleMonomial position) sign
]

{ #category : #'as yet unclassified' }
TermOverPositionOrdering >> type [
	^ #top
]
