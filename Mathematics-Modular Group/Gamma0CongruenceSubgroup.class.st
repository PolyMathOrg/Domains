"
Subgroups of SL(2,Z) associated with matrices of the form:
  [a b]   [* *]
  [c d] = [0 *] (mod n).
"
Class {
	#name : #Gamma0CongruenceSubgroup,
	#superclass : #CongruenceSubgroup,
	#category : #'Mathematics-Modular Group'
}

{ #category : #'as yet unclassified' }
Gamma0CongruenceSubgroup >> even [
	^ true
]

{ #category : #'as yet unclassified' }
Gamma0CongruenceSubgroup >> index [
	"Answer the index of the receiver in the modular group."
	| answer |
	answer := 1.
	self level factors withOccurrencesDo: [:p :e| 'answer := answer * (p ^ e + (p ^ (e - 1)))'].
	^ answer
	
]

{ #category : #'as yet unclassified' }
Gamma0CongruenceSubgroup >> numberOfCusps [
	| n |
	n := self level.
	^ n divisors sum: [:d| (d gcd: n // d) phi]
]

{ #category : #'as yet unclassified' }
Gamma0CongruenceSubgroup >> printOn: aStream [
	aStream nextPut: Character Gamma; nextPutAll: '0' sub; nextPut: $(; print: self level; nextPut: $)
]
