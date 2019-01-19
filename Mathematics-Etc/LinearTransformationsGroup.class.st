Class {
	#name : #LinearTransformationsGroup,
	#superclass : #TransformationGroup,
	#category : #'Mathematics-Etc'
}

{ #category : #'as yet unclassified' }
LinearTransformationsGroup class >> basis: aLinearBasis matrices: aMatrixGroup [
	^ self new basis: aLinearBasis; matrices: aMatrixGroup
]

{ #category : #'as yet unclassified' }
LinearTransformationsGroup class >> on: aFreeModule matrices: aMatrixGroup [
	^ self basis: aFreeModule basis matrices: aMatrixGroup
]

{ #category : #accessing }
LinearTransformationsGroup >> action [
	"Answer the natural action that sends (f, x) to f(x)."
	^ GroupAction from: (self, self space) to: self space evaluatingWithArguments: [:f :x| f value: x]
]

{ #category : #accessing }
LinearTransformationsGroup >> ambient [
	^ self space automorphisms "the general linear group GL(V)"
]

{ #category : #accessing }
LinearTransformationsGroup >> basis [
	^ self propertyAt: #basis
]

{ #category : #'accessing-private' }
LinearTransformationsGroup >> basis: aLinearBasis [
	self propertyAt: #basis put: aLinearBasis
]

{ #category : #operations }
LinearTransformationsGroup >> center [
	^ self class basis: self basis matrices: self matrices center
]

{ #category : #operations }
LinearTransformationsGroup >> commutator [
	^ self class basis: self basis matrices: self matrices commutator
]

{ #category : #accessing }
LinearTransformationsGroup >> degree [
	^ self matrices degree
]

{ #category : #enumerating }
LinearTransformationsGroup >> do: aBlock [
	| basis |
	basis := self basis.
	self matrices do: [:each| aBlock value: (LinearMap from: basis to: basis matrix: each)]
]

{ #category : #operations }
LinearTransformationsGroup >> hilbertSeries [
	^ self matrices hilbertSeries
]

{ #category : #accessing }
LinearTransformationsGroup >> identity [
	^ LinearMap from: self basis to: self basis matrix: self matrices identity
]

{ #category : #testing }
LinearTransformationsGroup >> includes: aLinearMap [
	(aLinearMap domain basis = self basis and: [aLinearMap codomain basis = self basis])
		ifTrue: [^ self matrices includes: aLinearMap matrix].
	"change of basis"
	^ self notYetImplemented
]

{ #category : #testing }
LinearTransformationsGroup >> isFinite [
	^ self matrices isFinite
]

{ #category : #accessing }
LinearTransformationsGroup >> matrices [
	^ self propertyAt: #matrices
]

{ #category : #'accessing-private' }
LinearTransformationsGroup >> matrices: aMatrixGroup [
	self propertyAt: #matrices put: aMatrixGroup
]

{ #category : #printing }
LinearTransformationsGroup >> printOn: aStream [
	self shortName isNil ifTrue: [^ super printOn: aStream].
	aStream nextPutAll: self shortName; nextPut: $(; print: self space; nextPut: $)
]

{ #category : #accessing }
LinearTransformationsGroup >> scalars [
	^ self matrices scalars
]

{ #category : #printing }
LinearTransformationsGroup >> shortName [
	^ self matrices shortName
]

{ #category : #accessing }
LinearTransformationsGroup >> size [
	^ self matrices size
]

{ #category : #accessing }
LinearTransformationsGroup >> space [
	^ self basis size = self basis ambient dimension
		ifTrue: [self basis ambient]
		ifFalse: [self basis span]
]
