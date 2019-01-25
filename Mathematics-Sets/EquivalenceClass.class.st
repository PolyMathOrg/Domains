"
Given a set X and an equivalence relation ~, the equivalence class of an element a is the set of elements equivalent to a: [a] = {x in X such that x ~ a}. An member of an equivalence class is called a 'representative'.

Elements of quotient objects (elements of QuotientRings, QuotientSpaces, etc) are polymorphic with EquivalenceClass.

See EquivalenceRelation.

References:
	https://en.wikipedia.org/wiki/Equivalence_class
"
Class {
	#name : #EquivalenceClass,
	#superclass : #Domain,
	#instVars : [
		'representative'
	],
	#category : #'Mathematics-Sets'
}

{ #category : #'instance creation' }
EquivalenceClass class >> representative: anElement relation: anEquivalenceRelation [
	^ self new
		representative: anElement;
		relation: anEquivalenceRelation
]

{ #category : #comparing }
EquivalenceClass >> = anEquivalenceClass [
	^ anEquivalenceClass includes: self representative
]

{ #category : #enumerating }
EquivalenceClass >> do: aBlock [
	self relation domain
		do: [ :each | 
			(self relation
				includes:
					{each.
					self representative})
				ifTrue: [ aBlock value: each ] ]
]

{ #category : #comparing }
EquivalenceClass >> hash [
	^ self class hash
]

{ #category : #testing }
EquivalenceClass >> includes: anElement [
	^ self relation
		includes:
			{anElement.
			self representative}
]

{ #category : #printing }
EquivalenceClass >> printOn: aStream [
	aStream
		nextPut: $[;
		print: self representative;
		nextPut: $]
]

{ #category : #accessing }
EquivalenceClass >> relation [
	^ self propertyAt: #relation
]

{ #category : #'accessing-private' }
EquivalenceClass >> relation: anEquivalenceRelation [
	self propertyAt: #relation put: anEquivalenceRelation
]

{ #category : #accessing }
EquivalenceClass >> representative [
	^ representative
]

{ #category : #'accessing-private' }
EquivalenceClass >> representative: anElement [
	representative := anElement
]
