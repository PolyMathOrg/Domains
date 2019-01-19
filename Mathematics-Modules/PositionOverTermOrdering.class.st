Class {
	#name : #PositionOverTermOrdering,
	#superclass : #ModuleMonomialOrdering,
	#category : #'Mathematics-Modules-Multivariate-Orderings'
}

{ #category : #'as yet unclassified' }
PositionOverTermOrdering >> compare: aModuleMonomial with: anotherModuleMonomial [
	| result |
	(result := (aModuleMonomial position - anotherModuleMonomial position) sign	) == 0
		ifFalse: [^ result].
	^ aModuleMonomial monomial compare: anotherModuleMonomial monomial
]

{ #category : #'as yet unclassified' }
PositionOverTermOrdering >> type [
	^ #pos
]
