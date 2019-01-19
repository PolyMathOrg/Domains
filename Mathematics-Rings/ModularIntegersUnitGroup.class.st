"
(Z/nZ)*, i.e. the multiplicaive group of units modulo n for some integer n. This group is generated by a primitive root modulo n.
"
Class {
	#name : #ModularIntegersUnitGroup,
	#superclass : #UnitGroup,
	#category : #'Mathematics-Rings-Finite'
}

{ #category : #accessing }
ModularIntegersUnitGroup >> generator [
	^ ring primitiveRoot
]

{ #category : #accessing }
ModularIntegersUnitGroup >> generators [
	^ {self generator}
]

{ #category : #accessing }
ModularIntegersUnitGroup >> modulus [
	^ ring modulus
]

{ #category : #accessing }
ModularIntegersUnitGroup >> size [
	^ self propertyAt: #size ifAbsentPut: [self modulus phi]
]