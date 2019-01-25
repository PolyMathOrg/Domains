"
Quotient of a set by an equivalence relation. The elements are equivalence classes. See EquivalenceRelation and EquivalenceClass.
"
Class {
	#name : #QuotientSet,
	#superclass : #Domain,
	#category : #'Mathematics-Sets'
}

{ #category : #'instance creation' }
QuotientSet class >> mod: anEquivalenceRelation [
	^ self new relation: anEquivalenceRelation
]

{ #category : #accessing }
QuotientSet >> base [
	^ self relation domain
]

{ #category : #enumerating }
QuotientSet >> do: aBlock [
	| visited |
	visited := Set new.
	self base
		do: [ :each | 
			| x |
			x := self project: each.
			visited add: x ifAbsent: [ aBlock value: x ] ]
]

{ #category : #testing }
QuotientSet >> isQuotient [
	^ true
]

{ #category : #printing }
QuotientSet >> printOn: aStream [
	aStream
		print: self relation domain;
		nextPut: $/;
		print: self relation
	"	| domain |
	domain := self relation domain.
	(domain printString allSatisfy: [:each|each isAlphaNumeric])
		ifTrue: [aStream print: domain]
		ifFalse: [aStream nextPut: $(; print: domain; nextPut: $)].
	aStream nextPut: $/; print: self relation"
]

{ #category : #morphisms }
QuotientSet >> project: anElement [
	^ EquivalenceClass representative: anElement relation: self relation
]

{ #category : #morphisms }
QuotientSet >> projection [
	^ (Function from: self base to: self evaluating: [:v| self project: v]) name: Character pi asString
]

{ #category : #accessing }
QuotientSet >> relation [
	^ self propertyAt: #relation
]

{ #category : #'accessing-private' }
QuotientSet >> relation: anEquivalenceRelation [
	self propertyAt: #relation put: anEquivalenceRelation
]
