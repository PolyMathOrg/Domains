"
Orders in a number field, i.e. subrings of a number field that as Z-modules are finitely generated and of maximal rank (with rank equal to the degree of the number field). See NumberField.
"
Class {
	#name : #Order,
	#superclass : #Ring,
	#category : #'Mathematics-Fields-Number Fields'
}

{ #category : #'accessing-private' }
Order >> ambient: aNumberField [
	self propertyAt: #ambient put: aNumberField
]

{ #category : #converting }
Order >> asModule [
	^ OrderAsModule on: self
]

{ #category : #accessing }
Order >> basis [
	^ self propertyAt: #basis
]

{ #category : #accessing }
Order >> degree [
	^ self ambient degree
]

{ #category : #accessing }
Order >> dimension [
	"Answer the Krull dimension of the receiver."
	^ 1
]

{ #category : #accessing }
Order >> generators [
	"Answer the generators of the receiver as a ring."
	^ self notYetImplemented
]

{ #category : #operations }
Order >> integralClosure [
	^ self isMaximal ifTrue: [self] ifFalse: [self ambient integers]
]

{ #category : #testing }
Order >> isIntegrallyClosedDomain [
	^ self isMaximal
]

{ #category : #testing }
Order >> isNoetherian [
	^ true
]

{ #category : #accessing }
Order >> rank [
	"Answer the rank of the receiver as Z-module, which is the degree of the number field over Q."
	^ self ambient degree
]
