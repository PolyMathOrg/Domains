"
Residue classes of polynomials modulo an ideal. They are elements of a quotient polynomial ring (an affine algebra, see AffineRing). They correspond to regular functions on an affine variety (see AffineVariety).
"
Class {
	#name : #RegularFunction,
	#superclass : #ResidueClass,
	#category : #'Mathematics-Schemes-Affine'
}

{ #category : #'as yet unclassified' }
RegularFunction >> leadingCoefficient [
	^ representative leadingCoefficient
]

{ #category : #'as yet unclassified' }
RegularFunction >> leadingMonomial [
	^ representative leadingMonomial
]

{ #category : #'as yet unclassified' }
RegularFunction >> value: anObject [
	^ representative value: anObject
]

{ #category : #evaluating }
RegularFunction >> valueWithArguments: anArray [
	^ representative valueWithArguments: anArray
]
