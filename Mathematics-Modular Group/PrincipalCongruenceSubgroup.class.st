"
Principal congruence subgroups of SL(2,Z), i.e. subgroups of SL(2,Z) associated with matrices of the form:
  [a b]   [1 0]
  [c d] = [0 1] (mod n).

They are the kernel of the quotient projection SL(2,Z) -> SL(2,Z/nZ) for some positive integer n (which is called the level of the congruence subgroup). Since they are kernels, my instances are normal subgroups.
"
Class {
	#name : #PrincipalCongruenceSubgroup,
	#superclass : #CongruenceSubgroup,
	#category : #'Mathematics-Modular Group'
}

{ #category : #'as yet unclassified' }
PrincipalCongruenceSubgroup >> * aGroup [
	(aGroup isKindOf: PrincipalCongruenceSubgroup)
		ifFalse: [^ super * aGroup].
	^ self class new: (self level gcd: aGroup level)
]

{ #category : #'as yet unclassified' }
PrincipalCongruenceSubgroup >> dot: aGroup [ " ï "
	"Answer the intersection of the receiver and the argument."
	(aGroup isKindOf: PrincipalCongruenceSubgroup)
		ifFalse: [^ super dot: aGroup].
	^ self class new: (self level lcm: aGroup level)
]

{ #category : #'as yet unclassified' }
PrincipalCongruenceSubgroup >> index [
	"Answer the index of the receiver in the modular group."
	| answer |
	answer := 1.
	self level factors withOccurrencesDo: [:p :e| 'answer := answer * (p ^ (e*3 - 2) * (p*p - 1))'].
	^ answer
]

{ #category : #'as yet unclassified' }
PrincipalCongruenceSubgroup >> numberOfCusps [
	| count |
	self level = 1 ifTrue: [^ 1].
	self level = 2 ifTrue: [^ 3].
	count := 1.
	self level factors withOccurrencesDo: [:p :e| 'count := count * (p ^ (e*2) - (p ^ (e*2 - 2)))'].
	^ count // 2
]

{ #category : #'as yet unclassified' }
PrincipalCongruenceSubgroup >> numberOfIrregularCusps [
	^ 0
]

{ #category : #'as yet unclassified' }
PrincipalCongruenceSubgroup >> printOn: aStream [
	aStream nextPut: Character Gamma.
	self level ~= 1 ifTrue: [aStream nextPut: $(; print: self level; nextPut: $)]
]
