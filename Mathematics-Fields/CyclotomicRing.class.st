"
Rings of integers of cyclotomic number fields. See CyclotomicField.
"
Class {
	#name : #CyclotomicRing,
	#superclass : #NumberRing,
	#category : #'Mathematics-Fields-Number Fields'
}

{ #category : #printing }
CyclotomicRing >> printOn: aStream [
	aStream print: ZZ; nextPut: $[; print: self ambient x; nextPut: $]
]
