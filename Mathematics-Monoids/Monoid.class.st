"
Monoids consist of a set, an associative binary operation and an identity element. So, they are semigroups with identity.
"
Class {
	#name : #Monoid,
	#superclass : #Semigroup,
	#category : #'Mathematics-Monoids'
}

{ #category : #copying }
Monoid >> copyEmpty [
	^ super copyEmpty identity: self identity
]

{ #category : #accessing }
Monoid >> identity [
	^ self propertyAt: #identity
]

{ #category : #'accessing-private' }
Monoid >> identity: anElement [
	self propertyAt: #identity put: anElement
]

{ #category : #testing }
Monoid >> isMonoid [
	^ true
]
