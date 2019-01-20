"
A word is a (noncommutative) formal product of a finite ordered list of objects. They are elements of a FreeMonoid.

See also Monomial for the commutative analog, and FormalSum for the additive analog.
"
Class {
	#name : #Word,
	#superclass : #Object,
	#instVars : [
		'syllables'
	],
	#category : #'Mathematics-Monoids'
}

{ #category : #'instance creation' }
Word class >> empty [
	^ self syllables: #()
]

{ #category : #'instance creation' }
Word class >> new [
	^ self shouldNotImplement 
]

{ #category : #'instance creation' }
Word class >> syllables: anArray [
	^ self basicNew syllables: anArray 
]

{ #category : #'instance creation' }
Word class >> x: i [
	^ self x: i to: 1 
]

{ #category : #'instance creation' }
Word class >> x: i to: k [
	"Answer a new instance of the receiver with only one indeterminate, xi, raised to n."

	k = 0
		ifTrue: [ ^ self empty ].
	^ self syllables: {(i -> k)}
]

{ #category : #arithmetic }
Word >> * aWord [
	| x y |
	self isEmpty ifTrue: [^ aWord].
	aWord isEmpty ifTrue: [^ self].
	syllables last key = aWord syllables first key
		ifFalse: [^ self class syllables: syllables, aWord syllables].
	x := syllables as: OrderedCollection.
	y := aWord syllables as: OrderedCollection.
	[x notEmpty and: [y notEmpty and: [x last key = y first key]]]
		whileTrue:
			[| xn y1 exponent |
			xn := x removeLast.
			y1 := y removeFirst.
			(exponent := xn value + y1 value) = 0
				ifFalse: [^ self class syllables: (x, {Association key: xn key value: exponent}, y) asArray]].
	^ self class syllables: (x, y) asArray
]

{ #category : #arithmetic }
Word >> / aWord [
	^ self * aWord reciprocal
]

{ #category : #comparing }
Word >> < aWord [
	^ (self >= aWord) not
]

{ #category : #comparing }
Word >> <= aWord [
	self == aWord ifTrue: [^ true].
	^ (self > aWord) not
]

{ #category : #comparing }
Word >> = aWord [
	^ syllables = aWord syllables
]

{ #category : #comparing }
Word >> > aWord [
	^ (self compare: aWord) > 0
]

{ #category : #comparing }
Word >> >= aWord [
	self == aWord ifTrue: [^ true].
	^ (self compare: aWord) >= 0
]

{ #category : #comparing }
Word >> compare: aWord [
	"Answer -1 if the receiver is < than the argument, 0 if they are equal, 1 if it is > than the argument.
	This is the noncommutative graded-lexicographical ordering."
	| result stream1 stream2 a1 a2 r1 r2 r x1 x2 |
	(result := (self length - aWord length) sign) = 0 ifFalse: [^ result].
	self isEmpty ifTrue: [^ 0].
	stream1 := syllables readStream.
	stream2 := aWord syllables readStream.
	r1 := 0.
	r2 := 0.
	[r1 > 0 ifFalse: [a1 := stream1 next. x1 := a1 key. r1 := a1 value].
	r2 > 0 ifFalse: [a2 := stream2 next. x2 := a2 key. r2 := a2 value].
	r := r1 min: r2.
	x1 < x2 ifTrue: [^ -1].
	x1 = x2 ifFalse: [^ 1].
	r1 := r1 - r.
	r2 := r2 - r.
	stream1 atEnd and: [stream2 atEnd]] whileFalse.
	^ 0
]

{ #category : #copying }
Word >> copyWithout: anObject [
	^ self class syllables: (self syllables select: [:each| each key ~= anObject])
]

{ #category : #enumerating }
Word >> do: aBinaryBlock [
	syllables do: [:each| aBinaryBlock value: each key value: each value]
]

{ #category : #comparing }
Word >> hash [
	^ syllables hash
]

{ #category : #testing }
Word >> isEmpty [
	^ syllables isEmpty
]

{ #category : #testing }
Word >> isStandard [
	"Answer true if the receiver is a standard word, i.e. if the symbols appear in ascending order."
	syllables size < 2 ifTrue: [^ true].
	1 to: syllables size - 1 do: [:i|
		(syllables at: i) key < (syllables at: i+1) key
			ifFalse: [^ false]].
	^ true
]

{ #category : #accessing }
Word >> length [
	syllables isEmpty ifTrue: [^ 0].
	^ syllables sum: [:each| each value abs]
]

{ #category : #printing }
Word >> printExponent: anInteger on: aStream [
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
Word >> printIndeterminate: indeterminate on: aStream [
	indeterminate isInteger
		ifFalse:
			[indeterminate class = self class
				ifTrue: [aStream nextPut: $(; print: indeterminate; nextPut: $)]
				ifFalse: [(aStream isText and: [indeterminate isString])
					ifTrue: [aStream nextPutAll: indeterminate asText]
					ifFalse: [aStream print: indeterminate]]. ^ self].
	aStream isText
		ifTrue: [aStream nextPut: $x; nextPutAll: indeterminate printString sub]
		ifFalse: [aStream nextPutAll: '{x', indeterminate printString, '}']
]

{ #category : #printing }
Word >> printOn: aStream [
	self isEmpty ifTrue: [aStream nextPut: Character epsilon. ^ self].
	self do: [:i :exp|
		exp = 0
			ifFalse:
				[self printIndeterminate: i on: aStream.
				self printExponent: exp on: aStream]]
]

{ #category : #arithmetic }
Word >> raisedTo: anInteger [
	anInteger = 1 ifTrue: [^ self].
	anInteger = 0 ifTrue: [^ self class empty].
	anInteger < 0 ifTrue: [^ 'self reciprocal ^ anInteger negated'].
	^ 'self squared ^ (anInteger // 2) * (self ^ (anInteger \\ 2))'
]

{ #category : #arithmetic }
Word >> reciprocal [
	^ self class syllables: (syllables collect: [:each| Association key: each key value: each value negated]) reversed
]

{ #category : #arithmetic }
Word >> reversed [
	^ self class syllables: syllables reversed
]

{ #category : #arithmetic }
Word >> squared [
	^ self * self
]

{ #category : #accessing }
Word >> syllables [
	^ syllables
]

{ #category : #'accessing-private' }
Word >> syllables: anArray [
	syllables := anArray
]

{ #category : #accessing }
Word >> value [
	^ 'syllables product: [:each| each key ^ each value]'
]

{ #category : #accessing }
Word >> value: anObject [
	| answer next |
	'syllables do: [:each|
			next := (anObject at: each key) ^ each value.
			answer := answer ifNil: [next] ifNotNil: [next * answer]]'.
	^ answer
]
