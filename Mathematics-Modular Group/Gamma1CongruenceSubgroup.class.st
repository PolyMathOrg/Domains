"
Subgroups of SL(2,Z) associated with matrices of the form:
  [a b]   [1 *]
  [c d] = [0 1] (mod n).
"
Class {
	#name : #Gamma1CongruenceSubgroup,
	#superclass : #CongruenceSubgroup,
	#category : #'Mathematics-Modular Group'
}

{ #category : #'as yet unclassified' }
Gamma1CongruenceSubgroup >> even [
	^ self level = 1 or: [self level = 2]
]

{ #category : #'as yet unclassified' }
Gamma1CongruenceSubgroup >> printOn: aStream [
	aStream nextPut: Character Gamma; nextPutAll: '1' sub; nextPut: $(; print: self level; nextPut: $)
]
