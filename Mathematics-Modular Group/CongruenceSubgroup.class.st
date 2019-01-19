"
Congruence subgroups of the modular group SL(2,Z), i.e. subgroups that contain the kernel of SL(2,Z) -> SL(2,Z/nZ) for some positive integer n (which is called the level of the congruence subgroup). See also ModularGroup.
"
Class {
	#name : #CongruenceSubgroup,
	#superclass : #ArithmeticGroup,
	#category : #'Mathematics-Modular Group'
}

{ #category : #'instance creation' }
CongruenceSubgroup class >> new: anInteger [
	^ self new level: anInteger
]

{ #category : #operations }
CongruenceSubgroup >> curve [
	"Answer the modular curve associated to the receiver. This is the orbit space of H/G (the upper half plane modulo the receiver) compactified canonically by adding the cusps."
	^ self notYetImplemented
]

{ #category : #operations }
CongruenceSubgroup >> cusps [
	"Answer the set of cusps of the receiver, i.e. the set of orbits of P^1(Q) under the action of the group. This set is finite."
	^ self notYetImplemented
]

{ #category : #operations }
CongruenceSubgroup >> genus [
	^ self curve genus
"(1 + projectiveIndex) / 12 - nu2 / 4 - nu3 / 4 - ncusps/2"
]

{ #category : #'as yet unclassified' }
CongruenceSubgroup >> indexOf: aSubgroup [
	^ (aSubgroup isKindOf: CongruenceSubgroup) ifTrue: [aSubgroup index / self index] ifFalse: [super indexOf: aSubgroup]
]

{ #category : #testing }
CongruenceSubgroup >> isEven [
	self flag: #fix. "this makes sense for the homogeneous group only, ~ SL(2,Z)"
	^ self includes: self identity negated
]

{ #category : #testing }
CongruenceSubgroup >> isOdd [
	self flag: #fix. "this makes sense for the homogeneous group only, ~ SL(2,Z)"
	^ self even not
]

{ #category : #accessing }
CongruenceSubgroup >> level [
	^ self propertyAt: #level
]

{ #category : #'accessing-private' }
CongruenceSubgroup >> level: anInteger [
	self propertyAt: #level put: anInteger
]

{ #category : #operations }
CongruenceSubgroup >> widthOf: aCusp [
	"Algorithm 1.19 (Width of a cusp) in Stein's 'Modular Forms, A Computational Approach'."
	| gamma |
	aCusp isInfinite
		ifTrue:
			[gamma := self identity]
		ifFalse:
			[| a b xgcd |
			a := aCusp numerator.
			b := aCusp denominator.
			xgcd := a xgcd: b.
			gamma := Matrix rows: {ZZ tuple: {a. b}. ZZ tuple: {xgcd at: 2. xgcd at: 3}}].
	"..."
]
