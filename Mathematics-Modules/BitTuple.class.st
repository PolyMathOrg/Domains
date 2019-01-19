"
Tuples of integer residue classes modulo 2, i.e. a binary tuple, a bit string, or a tuple of bits. The coefficients field is Z/2Z.

Example:
	""A handy way to create a binary tuple:""
	(1,0,1,1,0,1,1,1) % 2

"
Class {
	#name : #BitTuple,
	#superclass : #Tuple,
	#instVars : [
		'integer',
		'size'
	],
	#classVars : [
		'One',
		'Zero'
	],
	#category : #'Mathematics-Modules-Tuples'
}

{ #category : #'instance creation' }
BitTuple class >> coefficients: anArray [
	| answer |
	answer := self new: anArray size.
	anArray withIndexDo: [:each :i| answer at: i put: each].
	^ answer
]

{ #category : #'instance creation' }
BitTuple class >> fromInteger: anInteger [
	^ self new: anInteger highBit fromInteger: anInteger
]

{ #category : #initialization }
BitTuple class >> initialize [
	| Z2 |
	super initialize.
	Z2 := ZZ / 2.
	One := Z2 one.
	Zero := Z2 zero
]

{ #category : #'instance creation' }
BitTuple class >> new [
	^ self shouldNotImplement
]

{ #category : #'instance creation' }
BitTuple class >> new: anInteger [
	^ self new: anInteger fromInteger: 0
]

{ #category : #'instance creation' }
BitTuple class >> new: anInteger evaluating: aBlock [
	| integer |
	integer := 0.
	anInteger to: 1 by: -1 do:
		[:i| integer := (integer bitShift: 1) bitXor: (aBlock value: i) representative].
	^ self new: anInteger fromInteger: integer
]

{ #category : #'instance creation' }
BitTuple class >> new: n fromInteger: anInteger [
	^ self basicNew integer: anInteger size: n
]

{ #category : #'instance creation' }
BitTuple class >> newFrom: anObject [
	anObject isInteger ifTrue: [^ self fromInteger: anObject].
	^ self coefficients: anObject
]

{ #category : #operations }
BitTuple >> * aBit [
	^ ((aBit isInteger and: [aBit even]) or: [aBit isZero]) ifTrue: [self zero] ifFalse: [self]
]

{ #category : #operations }
BitTuple >> + aBitTuple [
	^ self class new: (self size max: aBitTuple size) fromInteger: (integer bitXor: aBitTuple asInteger)
]

{ #category : #copying }
BitTuple >> , anObject [
	(anObject isTuple or: [anObject isArray])
		ifFalse: [^ self copyWith: anObject].
	anObject class = self class
		ifTrue: [^ self class new: size + anObject size fromInteger: (integer bitXor: (anObject asInteger bitShift: size))].
	^ self , (self class coefficients: anObject)
]

{ #category : #operations }
BitTuple >> - aBitTuple [
	^ self + aBitTuple
]

{ #category : #comparing }
BitTuple >> = aTuple [
	self class = aTuple class ifFalse: [^ super = aTuple].
	^ size = aTuple size and: [integer = aTuple asInteger]
]

{ #category : #operations }
BitTuple >> >>> anInteger [
	^ self class new: (size + anInteger max: 0) fromInteger: (integer bitShift: anInteger)
]

{ #category : #enumerating }
BitTuple >> anySatisfy: aBlock [
	"Optimized. There are only two possible elements that could satisfy aBlock (1 or 0)."
	self isEmpty ifTrue: [^ false].
	(self isZero not and: [aBlock value: One]) ifTrue: [^ true].
	^ (aBlock value: Zero) and: [super anySatisfy: [:any| any = Zero]]
]

{ #category : #converting }
BitTuple >> asInteger [
	^ integer
]

{ #category : #accessing }
BitTuple >> at: anInteger [
	^ (integer bitAt: anInteger) = 1 ifTrue: [One] ifFalse: [Zero]
]

{ #category : #accessing }
BitTuple >> at: anInteger put: aBit [
	| bit |
	anInteger > size ifTrue: [self error: 'index out of bounds'].
	bit := aBit.
	bit isInteger ifTrue: [bit := bit even ifTrue: [Zero] ifFalse: [One]].
"		ifFalse: [(Zero = bit or: [One = bit]) ifFalse: [DomainError signal]]."
	(self at: anInteger) = bit
		ifFalse: [integer := integer bitXor: 1 << (anInteger - 1)].
	^ bit
]

{ #category : #operations }
BitTuple >> convolution: aBitTuple [
	| a b c |
	a := integer.
	b := aBitTuple asInteger.
	c := 0.
	1 to: a highBit do: [:i|
		(a bitAt: i) = 1 ifTrue: [c := c bitXor: b].
		b := b bitShift: 1].
	^ self class new: (self size + aBitTuple size - 1 max: 0) fromInteger: c
]

{ #category : #copying }
BitTuple >> copyFrom: start to: stop [ 
	"Answer a copy of a subset of the receiver, starting from element at 
	index start until element at index stop."

	| newSize |
	newSize := stop - start + 1 max: 0.
	start = 1 ifTrue: [^ self class new: newSize fromInteger: integer].
	^ self class new: newSize fromInteger: (integer bitShift: 1 - start)
]

{ #category : #copying }
BitTuple >> copyWith: aBit [
	| answer |
	answer := self copy size: self size + 1.
	aBit = One ifTrue: [answer at: self size + 1 put: One. ^ answer].
	aBit = Zero ifFalse: [DomainError signal].
	^ answer
]

{ #category : #operations }
BitTuple >> dot: aBitTuple [
	^ (integer bitAnd: aBitTuple asInteger) bitParity = 0 ifTrue: [Zero] ifFalse: [One]

"	^ self hadamard: aBitTuple :: sum
"

"	| x |
	x := self asInteger bitAnd: aBitTuple asInteger.
	[x > 1]
		whileTrue: [x := x >> (x highBit // 2) bitAnd: x].
	^ x"
]

{ #category : #operations }
BitTuple >> hadamard: aBitTuple [
	"Answer the entrywise product with the argument, also called Hadamard product."
	^ self class new: (self size min: aBitTuple size) fromInteger: (integer bitAnd: aBitTuple asInteger)
]

{ #category : #comparing }
BitTuple >> hash [
	^ integer hash
]

{ #category : #initialization }
BitTuple >> integer: anInteger size: anotherInteger [
	integer := anInteger.
	size := anotherInteger.
	size negative ifTrue: [self halt]
]

{ #category : #testing }
BitTuple >> isZero [
	^ integer == 0
]

{ #category : #testing }
BitTuple >> isZeroAt: anInteger [
	^ (integer bitAt: anInteger) == 0
]

{ #category : #operations }
BitTuple >> lift [
	"Answer a representative integer tuple."
	^ ZZ tuple: self size evaluating: [:i| integer bitAt: i]
]

{ #category : #operations }
BitTuple >> negated [
	^ self
]

{ #category : #operations }
BitTuple >> norm [
	^ self sum
]

{ #category : #operations }
BitTuple >> norm2 [
	^ self sum
]

{ #category : #operations }
BitTuple >> parity [
	"Answer 1 if the receiver has an odd number of bits on, 0 if it has an even number of bits on."
	| n parity |
	integer = 0 ifTrue: [^ 0].
"	n := integer >> (integer lowBit - 1). skip initial zeros, we could also skip chunks of zeros in the middle"
	n := integer.
	parity := 0.
	[n = 0] whileFalse: [parity := parity bitXor: (n bitAnd: 1). n := n >> 1].
	^ parity
]

{ #category : #operations }
BitTuple >> polynomialValue: anObject [
	Zero = anObject ifTrue: [^ self at: 1].
	One = anObject ifFalse: [^ super polynomialValue: anObject].
	^ self sum
]

{ #category : #printing }
BitTuple >> printOn: aStream [
	1 to: self size do: [:i| aStream print: (self at: i)]
]

{ #category : #accessing }
BitTuple >> representative [
	"Answer a representative integer tuple."
	^ ZZ tuple: self size evaluating: [:i| integer bitAt: i]
]

{ #category : #operations }
BitTuple >> reversed [
	^ self class new: self size fromInteger: (integer bitReverse: self size)
]

{ #category : #accessing }
BitTuple >> scalars [
	^ One parent
]

{ #category : #operations }
BitTuple >> shift: anInteger [
	^ self class new: size fromInteger: (integer bitShift: anInteger)
]

{ #category : #accessing }
BitTuple >> size [
	^ size
]

{ #category : #initialization }
BitTuple >> size: anInteger [
	size := anInteger.
	size negative ifTrue: [self halt]
]

{ #category : #operations }
BitTuple >> sum [
	"Answer the sum of the bits, i.e. the parity."
	^ integer bitParity = 0 ifTrue: [Zero] ifFalse: [One]
]

{ #category : #operations }
BitTuple >> weight [
	"Answer the Hamming weight of the receiver, i.e. the number of entries that are not zero."
	^ self asInteger bitCount
]

{ #category : #operations }
BitTuple >> zero [
	^ self class new: self size fromInteger: 0
]
