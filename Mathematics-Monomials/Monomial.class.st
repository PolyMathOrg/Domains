"
(Commutative) power products of one or many variables. They form a monoid (see FreeAbelianMonoid). Their formal linear combinations over a ring are Polynomials (see also PolynomialRing).

See also Word for the non-commutative analog, and FormalSum for the additive analog.
"
Class {
	#name : #Monomial,
	#superclass : #Object,
	#instVars : [
		'exponents',
		'parent',
		'degree'
	],
	#category : #'Mathematics-Monomials'
}

{ #category : #'instance creation' }
Monomial class >> exponents: anArray [
	^ self basicNew exponents: anArray
]

{ #category : #'instance creation' }
Monomial class >> new [
	^ self shouldNotImplement
]

{ #category : #'instance creation' }
Monomial class >> new: anInteger [
	^ self exponents: ((Array new: anInteger) atAllPut: 0; yourself)
]

{ #category : #'instance creation' }
Monomial class >> new: anInteger x: i [
	"Answer a new instance of the receiver with only one indeterminate: the argument i."
	^ self new: anInteger x: i to: 1
]

{ #category : #'instance creation' }
Monomial class >> new: anInteger x: i to: k [
	"Answer a new instance of the receiver with only one indeterminate, xi, raised to n."
	^ self exponents: ((Array new: anInteger) atAllPut: 0; at: i put: k; yourself)
]

{ #category : #operations }
Monomial >> * aMonomial [
	| b bn c |
	b := aMonomial exponents.
	bn := aMonomial exponents size.
	exponents size = bn ifFalse: [^ self error: 'not same size'].
	c := Array new: bn.
	1 to: bn do: [:i| c at: i put: (exponents at: i) + (b at: i)].
	^ self parent exponents: c
]

{ #category : #operations }
Monomial >> / aMonomial [
	"Answer the exact division of the receiver by the argument."
	| b bn c |
	b := aMonomial exponents.
	bn := aMonomial exponents size.
	exponents size = bn ifFalse: [^ self error: 'not same size'].
	c := Array new: bn.
	1 to: bn do: [:i| c at: i put: (exponents at: i) - (b at: i)].
	^ self parent exponents: c
]

{ #category : #comparing }
Monomial >> < aMonomial [
	^ (self >= aMonomial) not
]

{ #category : #comparing }
Monomial >> <= aMonomial [
	self == aMonomial ifTrue: [^ true].
	^ (self > aMonomial) not
]

{ #category : #comparing }
Monomial >> = aMonomial [
	| b |
	self == aMonomial ifTrue: [^ true].
	aMonomial isInteger ifTrue: [^ self degree = aMonomial].
"	^ exponents = aMonomial exponents"
	b := aMonomial exponents.
	exponents size = b size ifFalse: [^ false].
	1 to: exponents size do: [:i| (exponents at: i) = (b at: i) ifFalse: [^ false]].
	^ true
]

{ #category : #comparing }
Monomial >> > aMonomial [
	^ (self compare: aMonomial) > 0
]

{ #category : #comparing }
Monomial >> >= aMonomial [
	self == aMonomial ifTrue: [^ true].
	^ (self compare: aMonomial) >= 0
]

{ #category : #accessing }
Monomial >> at: anIndeterminate [
	^ exponents at: anIndeterminate
]

{ #category : #accessing }
Monomial >> bitSize [
	^ exponents inject: 0 into: [:x :each| x + each bitSize]
]

{ #category : #comparing }
Monomial >> compare: aMonomial [
	"Answer -1 if the receiver is < than the argument, 0 if they are equal, 1 if it is > than the argument."
	^ self ordering compare: self with: aMonomial
]

{ #category : #operations }
Monomial >> complete: anInteger in: anIndeterminate [
	"Answer a copy of the receiver of degree anInteger completing with a power of the indeterminate anotherInteger."
	| n |
	(n := self degree) = anInteger ifTrue: [^ self].
	^ self parent exponents: (exponents copy at: anIndeterminate put: anInteger - n + (self at: anIndeterminate); yourself)
]

{ #category : #copying }
Monomial >> copyWith: anIndeterminate to: anInteger [
	^ self parent exponents: (exponents copy at: anIndeterminate put: anInteger; yourself)
]

{ #category : #copying }
Monomial >> copyWithout: anIndeterminate [
	"Answer a copy of the receiver with the given indeterminate removed."
	^ self parent exponents: (exponents copy at: anIndeterminate put: 0; yourself)
]

{ #category : #operations }
Monomial >> degree [
	"Answer the total degree of the receiver."
	^ degree ifNil: [degree := exponents isEmpty ifTrue: [0] ifFalse: [exponents sum]]
]

{ #category : #operations }
Monomial >> degreeIn: anIndeterminate [
	"Answer the degree of the receiver in the given indeterminate, i.e. the power to which the indeterminate appears in the receiver."

	^ self at: anIndeterminate
]

{ #category : #operations }
Monomial >> dehomogenizedIn: anIndeterminate [
	| newExponents |
	newExponents := Array new: exponents size.
	newExponents replaceFrom: 1 to: anIndeterminate - 1 with: exponents startingAt: 1.
	newExponents replaceFrom: anIndeterminate to: exponents size - 1 with: exponents startingAt: anIndeterminate + 1.
	newExponents at: exponents size put: 0.
	^ self parent exponents: newExponents
]

{ #category : #accessing }
Monomial >> exponents [
	^ exponents
]

{ #category : #private }
Monomial >> exponents: anArray [
	exponents := anArray
]

{ #category : #operations }
Monomial >> gcd: aMonomial [
	"Answer the greatest common divisor of the receiver and the argument."
	exponents size <= aMonomial exponents size ifFalse: [^ aMonomial gcd: self].
	^ self parent exponents: (exponents withIndexCollect: [:each :i| each min: (aMonomial at: i)])
]

{ #category : #testing }
Monomial >> has: anIndeterminate [
	^ (self at: anIndeterminate) ~= 0
]

{ #category : #comparing }
Monomial >> hash [
	| answer |
	answer := self lastIndeterminate.
	1 to: exponents size do: [:i|
		| e |
		(e := exponents at: i) = 0
			ifFalse: [answer := answer hashMultiply + e hash]].
	^ answer
]

{ #category : #accessing }
Monomial >> indeterminates [
	"Answer the list of indeterminates effectively present in this monomial (with non-zero exponent). This is called the 'support' of a monomial."
	^ (1 to: exponents size) select: [:i| (exponents at: i) ~= 0]
]

{ #category : #testing }
Monomial >> isIdentity [
	^ exponents allSatisfy: [:each| each = 0]
]

{ #category : #testing }
Monomial >> isPurePower [
	"Answer true if the receiver is a power of a single indeterminate."
	| count |
	count := 0.
	exponents do: [:each| each == 0 ifFalse: [count := count + 1]. count > 1 ifTrue: [^ false]].
	^ count = 1
]

{ #category : #testing }
Monomial >> isSquareFree [
	^ exponents allSatisfy: [:each| each == 0 or: [each == 1]]
]

{ #category : #testing }
Monomial >> isUnivariateIn: anIndeterminate [
	^ exponents isEmpty or: [(self at: anIndeterminate) = self degree]
]

{ #category : #accessing }
Monomial >> lastIndeterminate [
	"Answer the leading indeterminate of the receiver (the last indeterminate effectively present)."
	^ exponents findLast: [:one| one ~= 0]
]

{ #category : #operations }
Monomial >> lcm: aMonomial [
	"Answer the least common multiple of the receiver and the argument."
	exponents size >= aMonomial exponents size ifFalse: [^ aMonomial lcm: self].
	^ self parent exponents: (exponents withIndexCollect: [:each :i| each max: (aMonomial at: i)])
]

{ #category : #converting }
Monomial >> orderedBy: aMonomialOrdering [
	^ (self parent orderedBy: aMonomialOrdering) ! self
]

{ #category : #accessing }
Monomial >> ordering [
	^ parent ordering
]

{ #category : #private }
Monomial >> parent [
	^ parent
]

{ #category : #private }
Monomial >> parent: aFreeAbelianMonoid [
	parent := aFreeAbelianMonoid
]

{ #category : #operations }
Monomial >> permutedBy: aPermutation [
	"Permute the variables of the receiver. The argument can be an Array (permutation in 'image format'). For example given a monomial in x,z,y, #(1 2 3) doesn't change anything, #(2 1 3) exchanges variables x and y."
	| answer |
	answer := self parent identity.
	exponents withIndexDo: [:exp :i|
		exp = 0 ifFalse: [answer := answer * (self parent x: (aPermutation at: i) to: exp)]].
	^ answer
]

{ #category : #copying }
Monomial >> postCopy [
	exponents := exponents copy.
	degree := nil
]

{ #category : #printing }
Monomial >> printExponent: anInteger on: aStream [
	| exponent |
	(exponent := anInteger printString) = '1'
		ifTrue: [^ self].
	aStream isText
		ifTrue:
			[aStream nextPutAll: exponent super.
			^ self].
	aStream nextPut: $^.
	exponent size = 1
		ifTrue: [aStream nextPutAll: exponent]
		ifFalse: [aStream nextPut: ${; nextPutAll: exponent; nextPut: $}]
]

{ #category : #printing }
Monomial >> printIndeterminate: indeterminate on: aStream [
	indeterminate isInteger
		ifFalse: [aStream nextPutAll: indeterminate displayStringOrText. ^ self].
	aStream isText
		ifTrue: [aStream nextPut: $x; nextPutAll: indeterminate printString sub]
		ifFalse:[aStream nextPutAll: '{x', indeterminate printString, '}']
]

{ #category : #printing }
Monomial >> printOn: aStream [
	self degree = 0 ifTrue: [aStream print: 1. ^ self].
	(self ordering indeterminates select: [:i| (self at: i) ~= 0])
		do: [:i|
			| x |
			x := self parent names ifNil: [i] ifNotNil: [:names| names at: i ifAbsent: [i]].
			self printIndeterminate: x on: aStream.
			self printExponent: (self at: i) on: aStream]
]

{ #category : #operations }
Monomial >> raisedTo: anInteger [

	^ self parent exponents: exponents * anInteger
]

{ #category : #operations }
Monomial >> root: anInteger [
	^ self parent exponents: exponents / anInteger
]

{ #category : #operations }
Monomial >> root: anInteger in: anIndeterminate [
	^ self parent exponents: (exponents copy at: anIndeterminate put: (self at: anIndeterminate) / anInteger; yourself)
]

{ #category : #operations }
Monomial >> substitute: aBlock [
	"Answer the receiver after substituting indeterminates by aBlock."
	| answer |
	answer := self parent identity.
	exponents withIndexDo: [:exp :i|
		exp = 0 ifFalse: [answer := answer * (self parent x: (aBlock value: i) to: exp)]].
	^ answer
]

{ #category : #accessing }
Monomial >> support [
	"Answer the list of indeterminates effectively present in this monomial (with non-zero exponent)."
	^ self indeterminates
]

{ #category : #operations }
Monomial >> value: anObject [
	| answer next |
	1 to: exponents size do: [:i|
		next := (anObject at: i) raiseTo: (exponents at: i).
		answer := answer ifNil: [next] ifNotNil: [next * answer]].
	^ answer
]

{ #category : #operations }
Monomial >> without: anIndeterminate [
	^ (self has: anIndeterminate) ifFalse: [self] ifTrue: [self copyWithout: anIndeterminate]
]

{ #category : #testing }
Monomial >> | aMonomial [
	"Answer true if the receiver divides the argument."
"	self degree > aMonomial degree ifTrue: [^ false]. <- this doesn't seem to help"
	1 to: exponents size do: [:i|
		(exponents at: i) > (aMonomial at: i) ifTrue: [^ false]].
	^ true
]
