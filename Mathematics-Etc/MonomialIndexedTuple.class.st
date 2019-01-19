"
My instances are formal sums of monomials.

Internally, they are represented by a list of associations monomial -> value. The list is kept sorted by the underlying monomial ordering.
"
Class {
	#name : #MonomialIndexedTuple,
	#superclass : #Collection,
	#instVars : [
		'scalars',
		'associations'
	],
	#category : #'Mathematics-Etc'
}

{ #category : #'instance creation' }
MonomialIndexedTuple class >> associations: aCollection over: aRing [
	^ self basicNew scalars: aRing; associations: aCollection
]

{ #category : #'instance creation' }
MonomialIndexedTuple class >> new: anInteger over: aRing [
	^ self basicNew scalars: aRing; associations: (OrderedCollection new: anInteger)
]

{ #category : #'instance creation' }
MonomialIndexedTuple class >> over: aRing [
	^ self basicNew scalars: aRing; associations: OrderedCollection new
]

{ #category : #operations }
MonomialIndexedTuple >> * aNumber [
	^ self collect: [:each| each*aNumber]
]

{ #category : #operations }
MonomialIndexedTuple >> + aMonomialTuple [
	| newAssociations |
	newAssociations := OrderedCollection new: self size + aMonomialTuple size.
	newAssociations resetTo: 1.
	self sum: associations with: aMonomialTuple associations into: newAssociations.
	^ self class associations: newAssociations over: scalars
]

{ #category : #operations }
MonomialIndexedTuple >> - aMonomialTuple [
	^ self + aMonomialTuple negated
]

{ #category : #operations }
MonomialIndexedTuple >> / aNumber [
	self flag: #fix.
	^ self collectNoZero: [:each| each / aNumber] "this could be slow, could take reciprocal many times"
]

{ #category : #operations }
MonomialIndexedTuple >> // aNumber [
	^ self collect: [:each| each // aNumber]
]

{ #category : #operations }
MonomialIndexedTuple >> /// aNumber [
	^ self collect: [:each| each /// aNumber]
]

{ #category : #comparing }
MonomialIndexedTuple >> = aMonomialTuple [
	self size = aMonomialTuple size ifFalse: [^ false].
	self == aMonomialTuple ifTrue: [^ true].
	^ associations = aMonomialTuple associations
]

{ #category : #operations }
MonomialIndexedTuple >> \\ aNumber [
	^ self collect: [:each| each \\ aNumber]
]

{ #category : #'accessing-private' }
MonomialIndexedTuple >> associations [
	^ associations
]

{ #category : #'accessing-private' }
MonomialIndexedTuple >> associations: aCollection [
"	(aCollection class == OrderedCollection) ifFalse: [^ self error: 'not an OrderedCollection']."
	associations := aCollection
]

{ #category : #enumerating }
MonomialIndexedTuple >> associationsDo: aBlock [
	associations do: aBlock
]

{ #category : #accessing }
MonomialIndexedTuple >> at: aMonomial [
	^ self at: aMonomial ifAbsent: [scalars zero]
]

{ #category : #accessing }
MonomialIndexedTuple >> at: aMonomial add: aNumber [
	associations isEmpty ifTrue: [aNumber isZero ifFalse: [associations add: aMonomial -> aNumber]. ^ self].
	associations
		findBinaryIndex: [:each| (each key compare: aMonomial) negated]
		do: [:index| | association newValue |
			association := associations at: index.
			(newValue := association value + aNumber) isZero
				ifTrue: [associations removeIndex: index]
				ifFalse: [association value: newValue "associations at: index put: aMonomial -> newValue"]]
		ifNone: [:low :high| aNumber isZero ifFalse: [associations add: aMonomial -> aNumber beforeIndex: high]]
]

{ #category : #accessing }
MonomialIndexedTuple >> at: aMonomial ifAbsent: exceptionBlock [
	^ associations findBinary: [:each| (each key compare: aMonomial) negated] do: [:each| each value] ifNone: [:high :low| exceptionBlock value]
]

{ #category : #accessing }
MonomialIndexedTuple >> at: key ifPresent: presentBlock [
	"Lookup the given key in the receiver. If it is present, answer the value of evaluating the given block with the value associated with the key. Otherwise, answer nil."

	| v |
	v := self at: key ifAbsent: [ ^ nil ].
	^ presentBlock value: v
]

{ #category : #accessing }
MonomialIndexedTuple >> at: aMonomial put: aNumber [
	associations isEmpty ifTrue: [aNumber isZero ifFalse: [associations add: aMonomial -> aNumber]. ^ self].
	associations
		findBinaryIndex: [:each| (each key compare: aMonomial) negated]
		do: [:index| aNumber isZero ifTrue: [associations removeIndex: index] ifFalse: [(associations at: index) value: aNumber]]
		ifNone: [:low :high| aNumber isZero ifFalse: [associations add: aMonomial -> aNumber beforeIndex: high]].
	^ aNumber
]

{ #category : #enumerating }
MonomialIndexedTuple >> collect: aBlock [
	| newAssociations |
	newAssociations := OrderedCollection new: associations size.
	associations do: [:each| | newValue |
		(newValue := aBlock value: each value) isZero
			ifFalse: [newAssociations add: (each copy value: newValue)]].
	^ self class associations: newAssociations over: scalars
]

{ #category : #enumerating }
MonomialIndexedTuple >> collectNoZero: aBlock [
	^ self class associations: (associations collect: [:each| each copy value: (aBlock value: each value)]) over: scalars
]

{ #category : #operations }
MonomialIndexedTuple >> convolution22: aMonomialTuple [
	| a b b2 c1 c2 c t |
	self size <= aMonomialTuple size
		ifTrue: [a := associations. b := aMonomialTuple associations]
		ifFalse: [a := aMonomialTuple associations. b := associations].
	c1 := OrderedCollection new: a size + b size.
	c2 := OrderedCollection new: a size + b size.
	c := c1.
	b2 := Array new: b size.
	a do: [:ai|
		1 to: b size do: [:i| | bi |
			bi := b at: i.
			b2 at: i put: ai key * bi key -> (ai value * bi value)].
		t := c1 == c ifTrue: [c2] ifFalse: [c1].
		t resetTo: 1.
		c := self sum: c with: b2 into: t].
	^ self class associations: c over: scalars
]

{ #category : #operations }
MonomialIndexedTuple >> convolution2: aMonomialTuple [
	| a b answer temp |
	self size <= aMonomialTuple size
		ifTrue: [a := associations. b := aMonomialTuple associations]
		ifFalse: [a := aMonomialTuple associations. b := associations].
	answer := self class over: scalars.
	temp := Array new: b size.
	a do: [:each|
		1 to: b size do: [:i| | other | other := b at: i. temp at: i put: other key * each key -> (other value * each value)].
		answer := answer + (self class associations: temp over: scalars)].
	^ answer
]

{ #category : #operations }
MonomialIndexedTuple >> convolution3: aMonomialTuple [
	| dictionary newAssociations |
	dictionary := Dictionary new: self size + aMonomialTuple size.
	self associationsDo: [:each|
		aMonomialTuple associationsDo: [:other|
			dictionary at: each key * other key add: each value * other value]].
	newAssociations := OrderedCollection new: dictionary size.
	newAssociations resetTo: 1.
	dictionary associationsDo: [:each| each value isZero ifFalse: [newAssociations add: each]].
	newAssociations sort.
	^ self class associations: newAssociations over: scalars
]

{ #category : #operations }
MonomialIndexedTuple >> convolution4: aMonomialTuple [
	| a b c |
	self size <= aMonomialTuple size
		ifTrue: [a := associations. b := aMonomialTuple associations]
		ifFalse: [a := aMonomialTuple associations. b := associations].
	(a size < 25 and: [a size * 2 < b size])
		ifTrue:
			[| c1 c2 b2 t |
			c1 := OrderedCollection new: a size + b size.
			c2 := OrderedCollection new: a size + b size.
			c := c1.
			b2 := Array new: b size.
			a do: [:ai|
				1 to: b size do: [:i| | bi |
					bi := b at: i.
					b2 at: i put: ai key * bi key -> (ai value * bi value)].
				t := c1 == c ifTrue: [c2] ifFalse: [c1].
				t resetTo: 1.
				c := self sum: c with: b2 into: t]]
		ifFalse: "if the sizes are not right, it's faster to use a hash table"
			[| dictionary |
			dictionary := Dictionary new: a size + b size.
			a do: [:ai|
				b do: [:bi|
				dictionary at: ai key * bi key add: ai value * bi value]].
			c := OrderedCollection new: dictionary size.
			c resetTo: 1.
			dictionary associationsDo: [:each| each value isZero ifFalse: [c add: each]].
			c sort].
	^ self class associations: c over: scalars
]

{ #category : #operations }
MonomialIndexedTuple >> convolution: aMonomialTuple [
	| dictionary newAssociations |
	dictionary := Dictionary new: self size + aMonomialTuple size.
	self associationsDo: [:each|
		aMonomialTuple associationsDo: [:other|
			dictionary at: each key * other key add: each value * other value]].
	newAssociations := OrderedCollection new: dictionary size.
	newAssociations resetTo: 1.
	dictionary associationsDo: [:each| each value isZero ifFalse: [newAssociations add: each]].
	newAssociations sort.
	^ self class associations: newAssociations over: scalars
]

{ #category : #copying }
MonomialIndexedTuple >> copy [
	^ self class associations: (associations collect: [:each| each copy]) over: scalars
]

{ #category : #operations }
MonomialIndexedTuple >> dividedByMonomial: aMonomial [
	"The monomial ordering is preserved by this operation."
	^ self class associations: (associations collect: [:each| each key / aMonomial -> each value]) over: scalars
]

{ #category : #enumerating }
MonomialIndexedTuple >> do: aBlock [
	self associationsDo: [:each| aBlock value: each value]
]

{ #category : #operations }
MonomialIndexedTuple >> dot: aMonomialTuple [
	| answer |
	self flag: #fix. "optimize"
	self size <= aMonomialTuple size ifFalse: [^ aMonomialTuple dot: self].
	answer := scalars zero.
	associations do: [:each| aMonomialTuple at: each key ifPresent: [:value2| answer := answer + (each value*value2)]].
	^ answer
]

{ #category : #comparing }
MonomialIndexedTuple >> hash [
	^ associations hash
]

{ #category : #testing }
MonomialIndexedTuple >> isZero [
	^ associations isEmpty
]

{ #category : #enumerating }
MonomialIndexedTuple >> keysAndValuesDo: aBlock [
	associations do: [:each| aBlock value: each key value: each value]
]

{ #category : #enumerating }
MonomialIndexedTuple >> keysDo: aBlock [
	associations do: [:each| aBlock value: each key]
]

{ #category : #accessing }
MonomialIndexedTuple >> lastKey [
	^ associations isEmpty ifFalse: [associations last key]
]

{ #category : #accessing }
MonomialIndexedTuple >> lastValue [
	^ associations isEmpty ifFalse: [associations last value]
]

{ #category : #operations }
MonomialIndexedTuple >> multipliedByMonomial: aMonomial [
	"The monomial ordering is preserved by this operation."
	^ self class associations: (associations collect: [:each| each key * aMonomial -> each value]) over: scalars
]

{ #category : #operations }
MonomialIndexedTuple >> negated [
	^ self class associations: (associations collect: [:each| each copy value: each value negated]) over: scalars
]

{ #category : #converting }
MonomialIndexedTuple >> over: aRing [
	| newAssociations |
	self scalars = aRing ifTrue: [^ self].
	newAssociations := OrderedCollection new: associations size.
	associations do: [:each| | newValue |
		(newValue := aRing ! each value) isZero
			ifFalse: [newAssociations add: (each copy value: newValue)]].
	^ self class associations: newAssociations over: aRing
]

{ #category : #printing }
MonomialIndexedTuple >> printCoefficient: coefficient on: aStream [
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
MonomialIndexedTuple >> printOn2: aStream [
	aStream nextPut: $(.
	associations do: [:each| aStream print: each] separatedBy: [aStream nextPutAll: ', '].
	aStream nextPut: $)
]

{ #category : #printing }
MonomialIndexedTuple >> printOn: aStream [
	| c |
	self isZero ifTrue: [aStream nextPutAll: '0'. ^ self].
	c := associations last value.
	c printString first = $-
		ifTrue: [c := c negated. aStream nextPut: $-].
	c ~= scalars one ifTrue: [self printCoefficient: c on: aStream].
	associations last key isIdentity
		ifFalse: [aStream print: associations last key].
	associations allButLast reverseDo: [:each|
		c := each value.
		c printString first = $-
			ifTrue: [aStream nextPutAll: ' - '. c := c negated]
			ifFalse: [aStream nextPutAll: ' + '].
		c ~= c one ifTrue: [self printCoefficient: c on: aStream].
		each key isIdentity
			ifFalse: [aStream print: each key]]
]

{ #category : #accessing }
MonomialIndexedTuple >> scalars [
	^ scalars
]

{ #category : #'accessing-private' }
MonomialIndexedTuple >> scalars: aRing [
	scalars := aRing
]

{ #category : #accessing }
MonomialIndexedTuple >> size [
	^ associations size
]

{ #category : #private }
MonomialIndexedTuple >> sum: someAssociations with: otherAssociations into: newAssociations [
	| stream1 stream2 |
	stream1 := someAssociations readStream.
	stream2 := otherAssociations readStream.
	[stream1 atEnd or: [stream2 atEnd]]
		whileFalse:
			[| cmp |
			cmp := stream1 peek key compare: stream2 peek key.
			cmp < 0
				ifTrue: [newAssociations add: stream1 next copy]
				ifFalse: [cmp > 0
					ifTrue: [newAssociations add: stream2 next copy]
					ifFalse:
						[| a b newValue |
						a := stream1 next.
						b := stream2 next.
						(newValue := a value + b value) isZero
							ifFalse: [newAssociations add: (a copy value: newValue)]]]].
	[stream1 atEnd] whileFalse: [newAssociations add: stream1 next copy].
	[stream2 atEnd] whileFalse: [newAssociations add: stream2 next copy].
	^ newAssociations
]
