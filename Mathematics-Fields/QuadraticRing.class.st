"
Rings of integers of quadratic number fields. See QuadraticField.
"
Class {
	#name : #QuadraticRing,
	#superclass : #NumberRing,
	#category : #'Mathematics-Fields-Number Fields'
}

{ #category : #testing }
QuadraticRing >> isEuclidean [
	self field d negative ifFalse: [self notYetImplemented].
	(#(-11 -7 -3 -2 -1) includes: self ambient d) ifFalse: [^ false].
	self notYetImplemented
]

{ #category : #testing }
QuadraticRing >> isIntegralDomain [
	^ true
]

{ #category : #testing }
QuadraticRing >> isNormEuclidean [
	^ #(-11 -7 -3 -2 -1 2 3 5 6 7 11 13 17 19 21 29 33 37 41 57 73) includes: self ambient d
]

{ #category : #testing }
QuadraticRing >> isPID [
	self field d negative ifTrue: [^ #(-1 -2 -3 -7 -11 -19 -43 -67 -163) includes: self ambient d].
	^ self ambient classNumber = 1
]

{ #category : #printing }
QuadraticRing >> printOn: aStream [
	| K a |
	K := self ambient.
	a := K d \\ 4 = 1 ifTrue: [K x + K one / (K one * 2)] ifFalse: [K x].
	aStream print: ZZ; nextPut: $[; print: a; nextPut: $]
]
