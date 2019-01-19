"
Formal sums (or formal linear combinations) of arbitrary objects with coefficients over a given ring R. They are like arbitrarily-indexed Tuples. They form free R-modules (see FormalSumsModule), or abelian groups when the coefficients ring R is the rational integers (see FreeAbelianGroup).
"
Class {
	#name : #FormalSum,
	#superclass : #Object,
	#instVars : [
		'coefficients',
		'parent'
	],
	#category : #'Mathematics-Modules-Tuples'
}

{ #category : #'instance creation' }
FormalSum class >> associations: aCollection [
	^ self coefficients: (aCollection as: Dictionary)
]

{ #category : #'instance creation' }
FormalSum class >> coefficients: aDictionary [
	^ self basicNew coefficients: aDictionary
]

{ #category : #'instance creation' }
FormalSum class >> new [
	^ self coefficients: Dictionary new
]

{ #category : #'instance creation' }
FormalSum class >> new: anInteger [
	^ self coefficients: (Dictionary new: anInteger)
]

{ #category : #operations }
FormalSum >> * aNumber [
	^ self collect: [:each| each*aNumber]
]

{ #category : #operations }
FormalSum >> + aFormalSum [
	| other answer |
	self size <= aFormalSum size
		ifTrue: [answer := aFormalSum copy. other := self]
		ifFalse: [answer := self copy. other := aFormalSum].
	other associationsDo: [:each| answer at: each key add: each value].
	^ answer
]

{ #category : #operations }
FormalSum >> - aFormalSum [
	| answer |
	self size <= aFormalSum size
		ifTrue:
			[answer := aFormalSum negated.
			self associationsDo: [:each| answer at: each key add: each value]]
		ifFalse:
			[answer := self copy.
			aFormalSum associationsDo: [:each| answer at: each key add: each value negated]].
	^ answer
]

{ #category : #operations }
FormalSum >> / aNumber [
	^ self collect: [:each| each / aNumber]
]

{ #category : #operations }
FormalSum >> // aNumber [
	^ self collect: [:each| each // aNumber]
]

{ #category : #operations }
FormalSum >> /// aNumber [
	^ self collect: [:each| each /// aNumber]
]

{ #category : #comparing }
FormalSum >> = aFormalSum [
	^ coefficients = aFormalSum coefficients
]

{ #category : #operations }
FormalSum >> \\ aNumber [
	^ self collect: [:each| each \\ aNumber]
]

{ #category : #enumreating }
FormalSum >> associationsDo: aBlock [
	coefficients associationsDo: aBlock
]

{ #category : #accessing }
FormalSum >> at: anObject [
	^ coefficients at: anObject ifAbsent: [self scalars zero]
]

{ #category : #accessing }
FormalSum >> at: key add: value [
	^ coefficients at: key addAndRemoveIfZero: value
]

{ #category : #accessing }
FormalSum >> at: anObject ifAbsent: aBlock [
	^ coefficients at: anObject ifAbsent: aBlock
]

{ #category : #accessing }
FormalSum >> at: anObject ifPresent: aBlock [
	^ coefficients at: anObject ifPresent: aBlock
]

{ #category : #accessing }
FormalSum >> at: key put: value [
	value isZero ifTrue: [coefficients removeKey: key ifAbsent: []. ^ value].
	^ coefficients at: key put: value
]

{ #category : #accessing }
FormalSum >> bitSize [
	| answer |
	answer := 0.
	coefficients keysAndValuesDo: [:key :value| answer := answer + key bitSize + value bitSize].
	^ answer
]

{ #category : #private }
FormalSum >> coefficients [
	^ coefficients
]

{ #category : #private }
FormalSum >> coefficients: aDictionary [
	coefficients := aDictionary.
	coefficients associationsDo: [:each| each value isZero ifTrue: [self error: 'the coefficinets dictionary contains zeroes']]
]

{ #category : #enumreating }
FormalSum >> coefficientsDo: aBlock [
	coefficients do: aBlock
]

{ #category : #enumreating }
FormalSum >> collect: aBlock [ 
	| newCoefficients |
	newCoefficients := Dictionary new: self size.
	self associationsDo: [:each| | newValue |
		(newValue := aBlock value: each value) isZero ifFalse: [newCoefficients at: each key put: newValue]].
	^ (self class coefficients: newCoefficients) parent: parent
]

{ #category : #enumreating }
FormalSum >> collectNoZero: aBlock [
	"The result of aBlock must never be zero."
	^ self copy associationsDo: [:each| each value: (aBlock value: each value)]
]

{ #category : #operations }
FormalSum >> convolution: aFormalSum [
	| newCoefficients |
	newCoefficients := Dictionary new: self size + aFormalSum size.
	self associationsDo: [:each|
		aFormalSum associationsDo: [:other|
			newCoefficients at: each key * other key addAndRemoveIfZero: each value * other value]].
	^ (self class coefficients: newCoefficients) parent: parent
]

{ #category : #accessing }
FormalSum >> denominator [
	| answer |
	self scalars isLocalization ifFalse: [^ self scalars one].
	answer := self scalars integers one.
	self do: [:each| answer := each denominator lcm: answer].
	^ answer
]

{ #category : #enumreating }
FormalSum >> do: aBlock [
	coefficients do: aBlock
]

{ #category : #operations }
FormalSum >> dot: aFormalSum [
	| answer |
	self size <= aFormalSum size ifFalse: [^ aFormalSum dot: self].
	answer := self scalars zero.
	coefficients associationsDo: [:each|
		aFormalSum at: each key ifPresent: [:value2| answer := answer + (each value*value2)]].
	^ answer
]

{ #category : #operations }
FormalSum >> hadamard: aFormalSum [
	"Answer the pointwise product with the argument, also called Hadamard product."
	| answer |
	self size <= aFormalSum size ifFalse: [^ aFormalSum hadamard: self]. "assuming it's commutative"
	answer := self copyEmpty.
	coefficients associationsDo: [:each| | key |
		key := each key.
		answer at: key put: each value * (aFormalSum at: key)].
	^ answer
]

{ #category : #comparing }
FormalSum >> hash [
	^ coefficients hash
]

{ #category : #testing }
FormalSum >> isZero [
	^ coefficients isEmpty
]

{ #category : #accessing }
FormalSum >> keys [
	^ coefficients keys
]

{ #category : #enumreating }
FormalSum >> keysAndValuesDo: aBlock [
	coefficients keysAndValuesDo: aBlock
]

{ #category : #enumreating }
FormalSum >> keysDo: aBlock [
	coefficients keysDo: aBlock
]

{ #category : #accessing }
FormalSum >> lift [
	"If the coefficients ring is a quotient R/I, answer a representative of the receiver over R. See >>%."
	^ self apply: self scalars lifting
]

{ #category : #operations }
FormalSum >> negated [
	^ self collectNoZero: [:each| each negated]
]

{ #category : #accessing }
FormalSum >> numerator [
	self scalars isLocalization ifFalse: [^ self].
	^ self * self denominator over: self scalars integers
]

{ #category : #converting }
FormalSum >> over: aRing [
	| newCoefficients |
	self scalars = aRing ifTrue: [^ self].
	newCoefficients := Dictionary new: self size.
	self associationsDo: [:each| | newValue |
		(newValue := aRing ! each value) isZero
			ifFalse: [newCoefficients add: (each copy value: newValue)]].
	^ (self class coefficients: newCoefficients) parent: (parent over: aRing)
]

{ #category : #private }
FormalSum >> parent [
	^ parent
]

{ #category : #private }
FormalSum >> parent: aDomain [
	parent := aDomain
]

{ #category : #copying }
FormalSum >> postCopy [
	coefficients := coefficients copy
]

{ #category : #printing }
FormalSum >> printCoefficient: coefficient on: aStream [
	| c |
	((c := coefficient) printString first = $- "or: [coefficient isNumber and: [coefficient negative]]")
		ifTrue: [aStream nextPut: $-. c := c negated].
	((c isKindOf: Polynomial) and: [c isMonomial])
		ifTrue: [aStream print: c. ^ self].
	(c printString allSatisfy: [:each| each isAlphaNumeric or: ['{}()/' includes: each]])
		ifTrue: [aStream print: c. ^ self].
	aStream nextPut: $(; print: c; nextPut: $)
]

{ #category : #printing }
FormalSum >> printLiteral: anObject on: aStream [
	((anObject isKindOf: Word) and: [anObject isEmpty])
		ifTrue: [^ self].
	anObject isInteger
		ifTrue:
			[aStream isText
				ifTrue: [aStream nextPut: $x; nextPutAll: anObject printString sub]
				ifFalse: [aStream nextPutAll: '{x', anObject printString, '}'].
			^ self].
	(aStream isText and: [anObject isString])
			ifTrue: [aStream nextPutAll: anObject asText]
			ifFalse: [aStream print: anObject]
]

{ #category : #printing }
FormalSum >> printOn2: aStream [
	aStream nextPut: $(.
	(Iterator on: self performing: #associationsDo:)
		do: [:each| aStream print: each] separatedBy: [aStream nextPutAll: ', '].
	aStream nextPut: $)
]

{ #category : #printing }
FormalSum >> printOn: aStream [
	| elements c |
	self isZero ifTrue: [aStream nextPutAll: '0'. ^ self].
	elements := self keys asSortedCollection: [:a :b| a printString <= b printString].
	c := self at: elements first.
	c printString first = $-
		ifTrue: [c := c negated. aStream nextPut: $-].
	c ~= self scalars one ifTrue: [self printCoefficient: c on: aStream].
	self printLiteral: elements first on: aStream.
	elements allButFirst do: [:each|
		c := self at: each.
		c printString first = $-
			ifTrue: [aStream nextPutAll: ' - '. c := c negated]
			ifFalse: [aStream nextPutAll: ' + '].
		c ~= c one ifTrue: [self printCoefficient: c on: aStream].
		self printLiteral: each on: aStream]
]

{ #category : #accessing }
FormalSum >> representative [
	"If the coefficients ring is a quotient R/I, answer a representative of the receiver over R. See >>%."
	^ self apply: self scalars projection section
]

{ #category : #accessing }
FormalSum >> scalars [
	^ parent scalars
]

{ #category : #accessing }
FormalSum >> size [
	^ coefficients size
]

{ #category : #enumreating }
FormalSum >> withIndexDo: elementAndIndexBlock [ 
	"Just like with:do: except that the iteration index supplies the second argument to the block."
	coefficients keysAndValuesDo: [:key :value| elementAndIndexBlock value: value value: key]
]

{ #category : #accessing }
FormalSum >> zero [
	^ parent zero
]
