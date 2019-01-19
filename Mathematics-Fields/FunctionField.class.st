"
Algebraic function fields, i.e. finite (and thus algebraic) field extensions of a rational function field. Function fields can also be viewed as vector spaces over the coefficients field.

"
Class {
	#name : #FunctionField,
	#superclass : #AlgebraicExtension,
	#category : #'Mathematics-Fields'
}

{ #category : #'as yet unclassified' }
FunctionField >> genus [
	^ self notYetImplemented
]

{ #category : #testing }
FunctionField >> isGlobalField [
	^ self scalars isGaloisField
]

{ #category : #testing }
FunctionField >> isPerfectField [
	"A field is perfect if either it has characteristic 0 or has characteristic p and every element in the field has a p-th root in the field."
	^ self characteristic = 0
]
