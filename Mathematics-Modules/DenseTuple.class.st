"
Gneral n-tuples internally represented as an Array. These are the tuples used by default for an arbitrary ring.
"
Class {
	#name : #DenseTuple,
	#superclass : #Tuple,
	#instVars : [
		'coefficients',
		'scalars'
	],
	#category : #'Mathematics-Modules-Tuples'
}

{ #category : #'instance creation' }
DenseTuple class >> coefficients: anArray over: aRing [
	^ self basicNew coefficients: anArray asArray; scalars: aRing
]

{ #category : #'instance creation' }
DenseTuple class >> new [
	^ self shouldNotImplement
]

{ #category : #'instance creation' }
DenseTuple class >> new: anInteger over: aRing [
	^ self coefficients: (Array new: anInteger) over: aRing
]

{ #category : #operations }
DenseTuple >> + aTuple [
	| zero |
	self size = aTuple size ifTrue: [^ scalars tuple: self size evaluating: [:i| (self at: i) + (aTuple at: i)]].
	zero := (self at: 1 ifAbsent: [aTuple at: 1]) zero.
	^ scalars tuple: (self size max: aTuple size) evaluating: [:i| (self at: i ifAbsent: [zero]) + (aTuple at: i ifAbsent: [zero])]
]

{ #category : #copying }
DenseTuple >> , anObject [
	(anObject isTuple or: [anObject isArray])
		ifTrue: [^ self class coefficients: (coefficients, anObject asArray) over: scalars].
	^ self class coefficients: (coefficients copyWith: anObject) over: scalars
]

{ #category : #operations }
DenseTuple >> - aTuple [
	| zero |
	self size = aTuple size ifTrue: [^ scalars tuple: self size evaluating: [:i| (self at: i) - (aTuple at: i)]].
	zero := (self at: 1 ifAbsent: [aTuple at: 1]) zero.
	^ scalars tuple: (self size max: aTuple size) evaluating: [:i| (self at: i ifAbsent: [zero]) - (aTuple at: i ifAbsent: [zero])]
]

{ #category : #enumerating }
DenseTuple >> allSatisfy: aBlock [
	^ coefficients allSatisfy: aBlock
]

{ #category : #enumerating }
DenseTuple >> anySatisfy: aBlock [
	^ coefficients anySatisfy: aBlock
]

{ #category : #converting }
DenseTuple >> asArray [
	^ coefficients
]

{ #category : #accessing }
DenseTuple >> at: anInteger [
	^ coefficients at: anInteger
]

{ #category : #accessing }
DenseTuple >> at: anInteger ifAbsent: aBlock [
	^ coefficients at: anInteger ifAbsent: aBlock
]

{ #category : #'accessing-private' }
DenseTuple >> at: anInteger put: anObject [
	^ coefficients at: anInteger put: anObject
]

{ #category : #initialization }
DenseTuple >> coefficients: anArray [
	coefficients := anArray
]

{ #category : #enumerating }
DenseTuple >> collect: aBlock [
	^ self class coefficients: (coefficients collect: aBlock) over: scalars
]

{ #category : #operations }
DenseTuple >> convolution: aTuple [
	| array |
	self isEmpty ifTrue: [^ self].
	aTuple isEmpty ifTrue: [^ aTuple].
	array := Array new: self size + aTuple size - 1.
	array atAllPut: self scalars zero.
	self withIndexDo: [:xi :i|
		xi isZero ifFalse:
			[aTuple withIndexDo: [:yj :j|
				array at: i+j-1 add: xi*yj]]].
	^ self class coefficients: array over: self scalars
]

{ #category : #copying }
DenseTuple >> copy [
	^ self class coefficients: coefficients copy over: scalars
]

{ #category : #copying }
DenseTuple >> copyFrom: start to: stop [
	^ self class coefficients: (coefficients copyFrom: start to: stop) over: scalars
]

{ #category : #copying }
DenseTuple >> copyWith: anElement [
	^ self class coefficients: (coefficients copyWith: anElement) over: scalars
]

{ #category : #enumerating }
DenseTuple >> do: aBlock [
	coefficients do: aBlock
]

{ #category : #enumerating }
DenseTuple >> findFirst: aBlock [
	^ coefficients findFirst: aBlock
]

{ #category : #enumerating }
DenseTuple >> findLast: aBlock [
	^ coefficients findLast: aBlock
]

{ #category : #testing }
DenseTuple >> includes: anObject [
	^ coefficients includes: anObject
]

{ #category : #accessing }
DenseTuple >> last [
	^ self at: self size
]

{ #category : #enumerating }
DenseTuple >> reverseDo: aBlock [
	coefficients reverseDo: aBlock
]

{ #category : #operations }
DenseTuple >> reversed [
	^ self class coefficients: coefficients reversed over: scalars
]

{ #category : #accessing }
DenseTuple >> scalars [
	^ scalars
]

{ #category : #'accessing-private' }
DenseTuple >> scalars: aRing [
	scalars := aRing
]

{ #category : #operations }
DenseTuple >> shift: anInteger [
	| newElements zero n |
	anInteger == 0 ifTrue: [^ self].
	newElements := Array new: self size.
	zero := (self at: 1) - (self at: 1).
	n := self size min: anInteger max: self size negated.
	n > 0
		ifTrue:
			[1 to: n do: [:i| newElements at: i put: zero].
			1+n to: self size do: [:i| newElements at: i put: (self at: i-n)]]
		ifFalse:
			[self size + n + 1 to: self size do: [:i| newElements at: i put: zero].
			1 to: self size + n do: [ :i | newElements at: i put: (self at: i-n)]].
	^ self class coefficients: newElements over: scalars
]

{ #category : #accessing }
DenseTuple >> size [
	^ coefficients size
]

{ #category : #'accessing-private' }
DenseTuple >> swap: i with: j [
	coefficients swap: i with: j
]

{ #category : #enumerating }
DenseTuple >> withIndexDo: aBlock [
	coefficients withIndexDo: aBlock
]

{ #category : #operations }
DenseTuple >> wrap: n [
	"Perform a cyclic right shift."
	| newElements |
	newElements := Array new: self size.
	0 to: self size - 1 do: [:i| newElements at: i+1 put: (self at: i-n \\ self size + 1) ].
	^ self class withAll: newElements
]
