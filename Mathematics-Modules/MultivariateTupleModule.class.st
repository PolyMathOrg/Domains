Class {
	#name : #MultivariateTupleModule,
	#superclass : #TupleModule,
	#instVars : [
		'ordering'
	],
	#category : #'Mathematics-Modules-Multivariate'
}

{ #category : #'instance creation' }
MultivariateTupleModule class >> new: anInteger over: aRing [
	^ self new: anInteger over: aRing ordering: #top
]

{ #category : #'instance creation' }
MultivariateTupleModule class >> new: anInteger over: aRing ordering: aModuleMonomialOrdering [
	^ self new rank: anInteger; scalars: aRing; ordering: aModuleMonomialOrdering
]

{ #category : #operations }
MultivariateTupleModule >> localization [
	"Answer the localization of the receiver at <x1,...,xn>. This is achieved by choosing a local ordering.
	Objects defined in this localization contain geometric information (usually only) about a Zariski neighbourhood of 0 in K^n, while objects in the global ring contain geometric information whish is valid in the whole affine space K^n."
	self scalars isLocal ifTrue: [^ self].
	^ self class new: self rank over: self scalars localization ordering: self ordering
]

{ #category : #converting }
MultivariateTupleModule >> orderedBy: aModuleMonomialOrdering [
	^ self class new: self rank over: self scalars ordering: aModuleMonomialOrdering
]

{ #category : #accessing }
MultivariateTupleModule >> ordering [
	^ ordering
]

{ #category : #'accessing-private' }
MultivariateTupleModule >> ordering: aModuleMonomialOrdering [
	ordering := aModuleMonomialOrdering isSymbol
		ifTrue: [ModuleMonomialOrdering perform: aModuleMonomialOrdering]
		ifFalse: [aModuleMonomialOrdering]
]
