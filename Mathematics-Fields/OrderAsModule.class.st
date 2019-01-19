"
Orders of number fields seen as free Z-modules. They are embedded in the ambient vector space corresponding to the ambient number field of the order. See Order.
"
Class {
	#name : #OrderAsModule,
	#superclass : #FreeModule,
	#instVars : [
		'order'
	],
	#category : #'Mathematics-Fields-Number Fields'
}

{ #category : #'instance creation' }
OrderAsModule class >> on: anOrder [
	^ self new order: anOrder
]

{ #category : #basis }
OrderAsModule >> coordinatesOf: anElement [
	^ anElement representative coefficients
]

{ #category : #basis }
OrderAsModule >> e: anInteger [
	^ order basis at: anInteger
]

{ #category : #accessing }
OrderAsModule >> order [
	^ order
]

{ #category : #'accessing-private' }
OrderAsModule >> order: anOrder [
	order := anOrder
]

{ #category : #basis }
OrderAsModule >> rank [
	^ order basis size
]

{ #category : #accessing }
OrderAsModule >> scalars [
	^ ZZ
]
