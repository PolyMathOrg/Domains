"
Fractional ideals of number fields.
"
Class {
	#name : #FractionalIdeal,
	#superclass : #Lattice,
	#category : #'Mathematics-Fields-Number Fields'
}

{ #category : #'instance creation' }
FractionalIdeal class >> over: aRing generators: aCollection [
	^ self new scalars: aRing; generators: aCollection
]

{ #category : #accessing }
FractionalIdeal >> ambient [
	^ self scalars fractions asSelfModule
]

{ #category : #accessing }
FractionalIdeal >> denominator [
	"Answer the denominator ideal of the receiver, which is an integral ideal."
	^ (self + self ambient oneIdeal) inverse
]

{ #category : #accessing }
FractionalIdeal >> denominator2 [
	^ self propertyAt: #denominator ifAbsentPut: [self generators collect: [:each| each denominator] andFold: [:a :b| a lcm: b]]
]

{ #category : #testing }
FractionalIdeal >> isIntegral [
	^ self scalars isUnit: self denominator
]

{ #category : #testing }
FractionalIdeal >> isMaximal [
	^ self isPrime and: [self isZero not]
]

{ #category : #testing }
FractionalIdeal >> isPrime [
	^ self factors size = 1
]

{ #category : #accessing }
FractionalIdeal >> numerator [
	"Answer the numerator ideal of the receiver, which is an integral ideal."
	| denominator |
	denominator := self denominator.
	^ self scalars * (self generators collect: [:each| each * denominator])
]

{ #category : #printing }
FractionalIdeal >> printOn: aStream [
	aStream nextPut: $<.
	(self generators asSortedCollection: [:a :b| a printString <= b printString])
		do: [:each| aStream print: each] separatedBy: [aStream nextPutAll: ', '].
	aStream nextPut: $>
]
