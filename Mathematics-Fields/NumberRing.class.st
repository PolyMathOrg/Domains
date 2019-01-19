"
Rings of integers of number fields (i.e. maximal orders). They are the integral closure of Z (the rational integers) in a number field. See NumberField.

"
Class {
	#name : #NumberRing,
	#superclass : #Order,
	#category : #'Mathematics-Fields-Number Fields'
}

{ #category : #'instance creation' }
NumberRing class >> on: aNumberField [
	^ self new ambient: aNumberField
]

{ #category : #accessing }
NumberRing >> basis [
	^ self ambient integralBasis
]

{ #category : #operations }
NumberRing >> fractions [
	^ self ambient
]

{ #category : #testing }
NumberRing >> isDedekindDomain [
	"Rings of integers of number fields are Dedekind domains."
	^ true
]

{ #category : #testing }
NumberRing >> isMaximal [
	^ true
]

{ #category : #testing }
NumberRing >> isPID [
	"A Dedekind domain is a UFD iff it is a PID."
	^ self isUFD
]

{ #category : #testing }
NumberRing >> isUFD [
	"A Dedekind domain is a UFD iff it is a PID."
	^ self isPID
]

{ #category : #printing }
NumberRing >> printOn: aStream [
	aStream nextPut: Character ZZ; nextPutAll: self ambient printString sub
"	aStream nextPutAll: 'O' italic; nextPut: $(; print: field; nextPut: $)"
]
