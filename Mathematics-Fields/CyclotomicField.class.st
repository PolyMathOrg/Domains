"
Cyclotomic fields, i.e. number fields obtained by adjoining a complex primitive root of unity to Q. The n-th cyclotomic field is obtained by adjoining a primitive n-th root of unity to the rational numbers.
"
Class {
	#name : #CyclotomicField,
	#superclass : #NumberField,
	#category : #'Mathematics-Fields-Number Fields'
}

{ #category : #examples }
CyclotomicField class >> example [
	^ CyclotomicField new: 7
]

{ #category : #'instance creation' }
CyclotomicField class >> new: anInteger [
	^ self new order: anInteger
]

{ #category : #morphisms }
CyclotomicField >> automorphisms [
	"this is easy to implement, it's isomorphic to (Z/nZ)*"
	self notYetImplemented
]

{ #category : #accessing }
CyclotomicField >> discriminant [
	| n phi |
	n := self order.
	phi := n phi.
	^ (-1  raisedTo: (phi / 2)) * (n  raisedTo:  phi) / ((n factors asSet collect:  [:p| p  raisedTo: (phi / (p - 1))]) fold: [:a :b| a*b])
]

{ #category : #accessing }
CyclotomicField >> integers [
	"Answer the ring of integers of the receiver."
	^ CyclotomicRing on: self
]

{ #category : #accessing }
CyclotomicField >> integralBasis [
	^ '(0 to: self degree - 1) collect: [:k| self x ^ k]'
]

{ #category : #testing }
CyclotomicField >> isAbelianExtension [
	"Cyclotomic fields are Abelian extensions."
	^ true
]

{ #category : #testing }
CyclotomicField >> isGaloisExtension [
	^ true
]

{ #category : #testing }
CyclotomicField >> isMonogenic [
	^ true
]

{ #category : #accessing }
CyclotomicField >> order [
	^ self propertyAt: #order
]

{ #category : #'accessing-private' }
CyclotomicField >> order: anInteger [
	anInteger > 2 ifFalse: [^ self error: 'the order of a cyclotomic field must be > 2'].
	self propertyAt: #order put: anInteger.
	self polynomial: ((QQ polynomialsIn: {'Zeta' , anInteger printString}) cyclotomic: anInteger)
]

{ #category : #printing }
CyclotomicField >> printOn: aStream [
	aStream print: self scalars; nextPut: $(; nextPut: Character zeta; nextPutAll: self order printString sub; nextPut: $)
]
