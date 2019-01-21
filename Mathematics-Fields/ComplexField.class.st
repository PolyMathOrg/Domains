"
The singletion global instance CC is the field of complex numbers.
"
Class {
	#name : #ComplexField,
	#superclass : #Ring,
	#category : #'Mathematics-Fields'
}

{ #category : #initialization }
ComplexField class >> initialize [
	super initialize.
	Smalltalk at: #CC put: self new
]

{ #category : #comparing }
ComplexField >> = anObject [
	^ anObject class == self class
]

{ #category : #comparing }
ComplexField >> > aDomain [
	^ (aDomain isKindOf: RationalField) or: [(aDomain isKindOf: RationalIntegerRing) or: [aDomain isKindOf: RealField]]
]

{ #category : #accessing }
ComplexField >> characteristic [
	^ 0
]

{ #category : #accessing }
ComplexField >> conjugation [
	^ self to: self evaluating: [:x| x conjugated]
]

{ #category : #enumerating }
ComplexField >> do: aBlock [
	^ self shouldNotImplement
]

{ #category : #comparing }
ComplexField >> hash [
	^ self class hash
]

{ #category : #testing }
ComplexField >> includes: anObject [
	^ anObject isComplex
]

{ #category : #testing }
ComplexField >> isAlgebraicallyClosed [
	^ true
]

{ #category : #testing }
ComplexField >> isComplex [
	^ true
]

{ #category : #testing }
ComplexField >> isField [
	^ true
]

{ #category : #testing }
ComplexField >> isLocalField [
	^ true
]

{ #category : #accessing }
ComplexField >> one [
	^ 1
]

{ #category : #printing }
ComplexField >> printOn: aStream [
	aStream nextPutAll: 'CC'
]

{ #category : #accessing }
ComplexField >> size [
	^ Aleph new: 0
]

{ #category : #accessing }
ComplexField >> zero [
	^ 0
]
