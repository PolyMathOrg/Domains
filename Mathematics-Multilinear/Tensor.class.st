"
Elements of tensor product modules (see TensorProductModule).

Tensors are represented as sparse formal sums of formal products of basis elements.
"
Class {
	#name : #Tensor,
	#superclass : #FormalSum,
	#category : #'Mathematics-Multilinear'
}

{ #category : #printing }
Tensor >> printLiteral: anArray on: aStream [
	(1 to: anArray size) do: [:i| aStream nextPutAll: ((parent at: i) names at: (anArray at: i))] separatedBy: [aStream nextPut: Character otimes]
]

{ #category : #operations }
Tensor >> quote: aTensor [ "í"
	^ 'self parent í aTensor parent compose: {self. aTensor}'
]

{ #category : #'as yet unclassified' }
Tensor >> type [
	^ parent type
]
