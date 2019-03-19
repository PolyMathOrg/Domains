"
Elements of a quotient ring. They are residue classes of elements of a ring modulo an ideal. See QuotientRing.
"
Class {
	#name : #ResidueClass,
	#superclass : #Object,
	#instVars : [
		'representative',
		'parent'
	],
	#category : #'Mathematics-Rings'
}

{ #category : #'instance creation' }
ResidueClass class >> in: aQuotientRing representative: anObject [
	^ self new
		parent: aQuotientRing;
		representative: anObject
]

{ #category : #operations }
ResidueClass >> * anObject [
	anObject isInteger ifTrue: [^ parent project: representative * anObject].
	(parent includes: anObject)
		ifTrue: [^ parent project: representative * anObject representative].
	^ self * (parent ! anObject)
]

{ #category : #operations }
ResidueClass >> + anObject [
	(parent includes: anObject)
		ifTrue: [^ parent project: representative + anObject representative].
	^ self + (parent ! anObject)
]

{ #category : #converting }
ResidueClass >> , aTuple [
	^ (parent tuple: 1 evaluating: [:i| self]), aTuple
]

{ #category : #operations }
ResidueClass >> - aResidueClass [
	^ self + aResidueClass negated
]

{ #category : #operations }
ResidueClass >> / aResidueClass [
	^ self * aResidueClass reciprocal
]

{ #category : #operations }
ResidueClass >> /// aResidueClass [
	"Answer the exact division of the receiver by the argument."
	^ parent project: representative /// aResidueClass representative
]

{ #category : #comparing }
ResidueClass >> = anObject [
	(self class = anObject class and: [parent = anObject parent])
		ifTrue: [^ self contains: anObject representative].
	"could we instead assume the representative is unique?:
		ifTrue: [^ representative = anObject representative]."
	^ self = (parent ! anObject)
]

{ #category : #converting }
ResidueClass >> adaptToInteger: rcvr andSend: selector [
	^ parent project: (rcvr perform: selector with: representative)
]

{ #category : #accessing }
ResidueClass >> bitSize [
	^ representative bitSize 
]

{ #category : #conjugation }
ResidueClass >> conjugated [
	^ 'self ^ self parent characteristic'
]

{ #category : #conjugation }
ResidueClass >> conjugates [
	^ Iterator on: [:aBlock| self conjugatesDo: aBlock]
]

{ #category : #conjugation }
ResidueClass >> conjugatesDo: aBlock [
	"Iterate over the conjugancy class of the receiver, i.e. all the conjugates including the receiver."
	| alpha |
	alpha := self.
	[aBlock value: alpha.
	'alpha := alpha ^ self relations scalars characteristic'.
	alpha = self] whileFalse
]

{ #category : #testing }
ResidueClass >> contains: anObject [
	^ parent relations contains: anObject - representative
]

{ #category : #operations }
ResidueClass >> gcd: aResidueClass [
	^ parent project: (representative gcd: aResidueClass representative)
]

{ #category : #comparing }
ResidueClass >> hash [
	^ parent hash
"could we instead assume the representative is unique?:
	^ representative hash"
]

{ #category : #testing }
ResidueClass >> includes: anObject [
	^ (parent base includes: anObject) and: [self contains: anObject]
]

{ #category : #testing }
ResidueClass >> is: aSymbol [
	^ aSymbol == #ResidueClass or: [super is: aSymbol]
]

{ #category : #testing }
ResidueClass >> isNilpotent [
	"Answer true if self^n = 0 for some integer n >= 1."
	^ parent isNilpotent: self
]

{ #category : #testing }
ResidueClass >> isUnit [
	"Answer true if the receiver is invertible."

	^ parent isUnit: self 
]

{ #category : #testing }
ResidueClass >> isZero [
	"^ (ideal remainderOf: representative) isZero"

	^ representative isZero 
]

{ #category : #testing }
ResidueClass >> isZeroDivisor [
	^ parent isZeroDivisor: self 
]

{ #category : #operations }
ResidueClass >> lcm: aResidueClass [
	^ parent project: (representative lcm: aResidueClass representative)
]

{ #category : #accessing }
ResidueClass >> lift [
	^ self representative
]

{ #category : #accessing }
ResidueClass >> modulus [
	^ parent modulus
]

{ #category : #operations }
ResidueClass >> negated [
	^ parent project: representative negated
]

{ #category : #constants }
ResidueClass >> one [
	^ parent one
]

{ #category : #private }
ResidueClass >> parent [
	^ parent
]

{ #category : #'accessing-private' }
ResidueClass >> parent: aQuotientRing [
	parent := aQuotientRing
]

{ #category : #printing }
ResidueClass >> printOn: aStream [
	aStream print: representative"; nextPutAll: ' mod '; print: ideal"
]

{ #category : #operations }
ResidueClass >> raisedTo: anInteger [
	"Answer the receiver raised to the power anInteger."

	anInteger = 1
		ifTrue: [ ^ self ].
	anInteger = 0
		ifTrue: [ ^ self one ].
	anInteger < 0
		ifTrue: [ ^ (self raisedTo: anInteger negated) reciprocal ].
	^ (self squared raisedTo: anInteger // 2)
		* (self raisedTo: anInteger \\ 2)
]

{ #category : #operations }
ResidueClass >> reciprocal [
	^ parent inverseOf: self
]

{ #category : #accessing }
ResidueClass >> relations [
	^ parent relations
]

{ #category : #accessing }
ResidueClass >> representative [
	^ representative
]

{ #category : #'accessing-private' }
ResidueClass >> representative: anObject [
	representative := anObject
]

{ #category : #operations }
ResidueClass >> squared [
	^ parent project: representative squared
]

{ #category : #constants }
ResidueClass >> zero [
	^ parent zero
]
