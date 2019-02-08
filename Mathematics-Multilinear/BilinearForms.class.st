Class {
	#name : #BilinearForms,
	#superclass : #FreeModule,
	#instVars : [
		'vectorSpace',
		'domain'
	],
	#category : #'Mathematics-Multilinear'
}

{ #category : #'instance creation' }
BilinearForms class >> on: aVectorSpace [
	^ self new vectorSpace: aVectorSpace
]

{ #category : #operations }
BilinearForms >> alternate [
	"Answer the subspace of alternating bilinear forms."

	^ self notYetImplemented 
]

{ #category : #accessing }
BilinearForms >> codomain [
	^ self scalars 
]

{ #category : #basis }
BilinearForms >> coordinatesOf: aBilinearForm [
	"Answer the coordinates of aBilinearForm with respect to the domain canonical basis."

	^ self matrices coordinatesOf: (self matrixOf: aBilinearForm) 
]

{ #category : #accessing }
BilinearForms >> domain [ 
	^ vectorSpace , vectorSpace
]

{ #category : #basis }
BilinearForms >> e: anInteger [
	"Answer the anInteger-th canonical vector."
 
	^ BilinearForm
		fromHalf: vectorSpace
		matrix: (self matrices e: anInteger)
]

{ #category : #elements }
BilinearForms >> evaluating: aBlock [
	^ BilinearForm from: self domain evaluating: aBlock
]

{ #category : #private }
BilinearForms >> matrices [
	"Answer the vector space of the matrices associated to the bilinear forms of the receiver."
	^ 'self scalars ^ (vectorSpace dimension @ vectorSpace dimension)'
]

{ #category : #private }
BilinearForms >> matrixOf: aBilinearForm [
	"Answer the matrix associated to aBilinearForm with respect to the canonical basis."
	^ self matrices
		evaluating: [:i :j|
			aBilinearForm value: (vectorSpace e: i) value: (vectorSpace e: j)]
]

{ #category : #elements }
BilinearForms >> newFrom: anObject [
	^ self evaluating: anObject
]

{ #category : #printing }
BilinearForms >> printOn: aStream [
	aStream nextPutAll: 'Bil('; print: vectorSpace; nextPut: $)
]

{ #category : #basis }
BilinearForms >> rank [
	^ vectorSpace rank squared
]

{ #category : #accessing }
BilinearForms >> scalars [
	^ vectorSpace scalars
]

{ #category : #operations }
BilinearForms >> symmetric [
	"Answer the subspace of symmetric bilinear forms."
	^ self notYetImplemented
]

{ #category : #'accessing-private' }
BilinearForms >> vectorSpace: aVectorSpace [
	vectorSpace := aVectorSpace
]
