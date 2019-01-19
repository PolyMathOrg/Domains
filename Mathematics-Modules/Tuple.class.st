"
n-tuples with coefficients in some ring R, i.e. finite ordered lists of n elements of R indexed by integers 1 to n. They are the elements of the R-module R^n.

Some subclasses implement special kinds of tuples for concrete rings, such as Z/mZ and Z/2Z. These special tuples have a compact representation that saves memory and allows fast arithmetic. Many parts of the system (such as linear algebra and polynomials) ultimately rely on tuples.

Tuples are commonly created by sending a message to the ring where the coefficients belong to. For example:
	""Two ways to create the 4-tuple (1,2,4,8) with integer coefficients:""
	ZZ tuple: #(1 2 4 8).
	ZZ tuple: 4 evaluating: [:i| i squared].

It is also handy to create tuples by sending the message #, to a number. For example:
  (1,2,4,8)
However, when created in this way, even if all the coefficients are Integers, the tuple will be considered a rational tuple (with coefficients in the field of rational numbers QQ), so the above example is equivalent to:
	QQ tuple: #(1 2 4 8)

"
Class {
	#name : #Tuple,
	#superclass : #Object,
	#category : #'Mathematics-Modules-Tuples'
}

{ #category : #operations }
Tuple >> % anInteger [
	| ring |
	self flag: #fix. "optimize. this is slow because creates lots of residue class objects"
	ring := ZZ % anInteger.
	anInteger = 2 ifTrue: [^ BitTuple new: self size evaluating: [:i| ring project: (self at: i)]].
	^ ModularTuple new: self size over: ring evaluating: [:i| ring project: (self at: i)]
]

{ #category : #operations }
Tuple >> * anObject [
	anObject isTuple
		ifTrue: [^ self scalars tuple: (self size min: anObject size) evaluating: [:i| (self at: i) * (anObject at: i)]].
	^ self collect: [:each| each * anObject]
]

{ #category : #operations }
Tuple >> - aTuple [
	^ self + aTuple negated
]

{ #category : #operations }
Tuple >> / aNumber [
	^ self collect: [:each| each / aNumber]
]

{ #category : #operations }
Tuple >> // aNumber [
	^ self collect: [:each| each // aNumber]
]

{ #category : #operations }
Tuple >> /// aNumber [
	^ self collect: [:each| each /// aNumber]
]

{ #category : #operations }
Tuple >> << anInteger [
	^ self >> anInteger negated
]

{ #category : #operations }
Tuple >> <<< anInteger [
	^ self >>> anInteger negated
]

{ #category : #comparing }
Tuple >> = anObject [
	self == anObject ifTrue: [^ true].
	anObject isTuple ifFalse: [^ false].
	self size = anObject size ifFalse: [^ false].
	1 to: self size do: [:i|
		(self at: i) = (anObject at: i) ifFalse: [^ false]].
	^ true
]

{ #category : #operations }
Tuple >> >> anInteger [
	^ self shift: anInteger
]

{ #category : #operations }
Tuple >> >>> anInteger [
	anInteger == 0 ifTrue: [^ self].
	anInteger < 0 ifTrue: [^ self copyFrom: anInteger negated + 1 to: self size].
	^ (self scalars tuple: anInteger constant: self scalars zero), self
]

{ #category : #operations }
Tuple >> \\ aNumber [
	^ self collect: [:each| each \\ aNumber]
]

{ #category : #converting }
Tuple >> adaptToCollection: aCollection andSend: selector [
	self size = aCollection size ifFalse: [^ self error: 'sizes don''t match'].
	^ aCollection withIndexCollect: [:each :index| each perform: selector with: (self at: index)]
]

{ #category : #converting }
Tuple >> adaptToNumber: aNumber andSend: selector [
	selector == #* ifTrue:[^ self collect: [:each| aNumber * each]].
	^ super adaptToNumber: aNumber andSend: selector
]

{ #category : #converting }
Tuple >> adaptToRealAlgebraic: aNumber andSend: selector [
	^ self adaptToNumber: aNumber andSend: selector
]

{ #category : #operations }
Tuple >> add: aTuple by: aNumber [
	self add: aTuple by: aNumber startingAt: 1
]

{ #category : #operations }
Tuple >> add: aTuple by: aNumber from: startIndex to: stopIndex [
	startIndex to: stopIndex do: [:i|
		self at: i put: (aTuple at: i) * aNumber + (self at: i)]
]

{ #category : #operations }
Tuple >> add: aTuple by: aNumber startingAt: startIndex [
	self add: aTuple by: aNumber from: startIndex to: (self size min: aTuple size)
]

{ #category : #enumerating }
Tuple >> allSatisfy: aBlock [
	"Evaluate aBlock with the elements of the receiver.
	If aBlock returns false for any element return false.
	Otherwise return true."

	self do: [:each | (aBlock value: each) ifFalse: [^ false]].
	^ true
]

{ #category : #enumerating }
Tuple >> anySatisfy: aBlock [
	"Evaluate aBlock with the elements of the receiver.
	If aBlock returns true for any element return true.
	Otherwise return false"

	self do:[:item | (aBlock value: item) ifTrue: [^ true]].
	^ false
]

{ #category : #operations }
Tuple >> apply: aMorphism [
	"Apply a homomorphism to the coefficients of the receiver."
	aMorphism isBlock ifTrue: [^ self collect: aMorphism].
	^ aMorphism codomain tuple: self size evaluating: [:i| aMorphism value: (self at: i)]
]

{ #category : #converting }
Tuple >> asArray [
	^ self as: Array
]

{ #category : #converting }
Tuple >> asColumnMatrix [
	^ Matrix columns: {self}
]

{ #category : #converting }
Tuple >> asRowMatrix [
	^ Matrix rows: {self}
]

{ #category : #converting }
Tuple >> asTuple [
	^ self
]

{ #category : #accessing }
Tuple >> at: index ifAbsent: exceptionBlock [
	"Answer the element at my position index. If I do not contain an element
	at index, answer the result of evaluating the argument, exceptionBlock."

	(index between: 1 and: self size) ifTrue: [^ self at: index].
	^ exceptionBlock value
]

{ #category : #accessing }
Tuple >> bitSize [
	| answer |
	answer := 0.
	self do: [:each| answer := answer + each bitSize].
	^ answer
]

{ #category : #enumerating }
Tuple >> collect: aBlock [
	^ self scalars tuple: self size evaluating: [:i| aBlock value: (self at: i)]
]

{ #category : #operations }
Tuple >> conjugated [
	^ self collect: [:each| each conjugated]
]

{ #category : #operations }
Tuple >> content [
	"Answer the GCD of the coefficients of the receiver.
	In a field, it is convenient to define the content as 1."
	| answer |
	self scalars isField
		ifTrue:
			[^ self scalars isFractionRing
				ifTrue:
					[| c |
					c := self coefficients inject: self scalars one into: [:lcm :each| lcm lcm: each denominator].
					(self coefficients inject: self scalars zero into: [:gcd :each| gcd gcd: each * c]) / c]
				ifFalse: [self scalars one]].
	answer := self scalars zero.
	self coefficients do: [:each| answer := answer gcd: each].
	^ answer
]

{ #category : #enumerating }
Tuple >> count: aBlock [
	| count |
	count := 0.
	self do: [:each| (aBlock value: each) ifTrue: [count := count + 1]].
	^ count
]

{ #category : #accessing }
Tuple >> denominator [
	| answer |
	self scalars isLocalization ifFalse: [^ self scalars one].
	answer := self scalars integers one.
	self do: [:each| answer := each denominator lcm: answer].
	^ answer
]

{ #category : #enumerating }
Tuple >> do: aBlock [
	1 to: self size do: [:each| aBlock value: (self at: each)]
]

{ #category : #enumerating }
Tuple >> do: elementBlock separatedBy: separatorBlock [
	| beforeFirst | 
	"Evaluate the elementBlock for all elements in the receiver,
	and evaluate the separatorBlock between."

	beforeFirst := true.
	self do: [ :element |
		beforeFirst
			ifTrue: [beforeFirst := false]
			ifFalse: [separatorBlock value].
		elementBlock value: element]
]

{ #category : #operations }
Tuple >> dot: aTuple [
	| answer |
	answer := (self at: 1) * (aTuple at: 1).
	2 to: (self size min: aTuple size) do: [:i| answer := answer + ((self at: i) * (aTuple at: i))].
	^ answer
]

{ #category : #enumerating }
Tuple >> findFirst: aBlock [
	"Return the index of my first element for which aBlock evaluates as true."

	| index |
	index := 0.
	[(index := index + 1) <= self size] whileTrue:
		[(aBlock value: (self at: index)) ifTrue: [^index]].
	^ 0
]

{ #category : #enumerating }
Tuple >> findLast: aBlock [
	"Return the index of my last element for which aBlock evaluates as true."

	| index |
	index := self size + 1.
	[(index := index - 1) >= 1] whileTrue:
		[(aBlock value: (self at: index)) ifTrue: [^index]].
	^ 0
]

{ #category : #accessing }
Tuple >> first [
	^ self at: 1
]

{ #category : #operations }
Tuple >> hadamard: aTuple [
	"Answer the entrywise product with the argument, also called Hadamard product."
	^ self scalars tuple: (self size min: aTuple size) evaluating: [:i| (self at: i) * (aTuple at: i)]
]

{ #category : #comparing }
Tuple >> hash [
	| hash |
	hash := 0.
	1 to: self size do: [:i | hash := (hash + (self at: i) hash) hashMultiply].
	^hash
]

{ #category : #operations }
Tuple >> height [
	| answer |
	answer := 1.
	self do: [:each| answer := answer max: each height].
	^ answer
]

{ #category : #converting }
Tuple >> homogenized [
	^ self homogenizedIn: self size + 1
]

{ #category : #converting }
Tuple >> homogenizedIn: anInteger [
	^ (self copyFrom: 1 to: anInteger - 1), self scalars one, (self copyFrom: anInteger to: self size)
]

{ #category : #testing }
Tuple >> includes: anObject [ 
	"Answer whether anObject is one of the receiver's elements."

	self do: [:each| each = anObject ifTrue: [^ true]].
	^ false
]

{ #category : #enumerating }
Tuple >> inject: thisValue into: binaryBlock [ 
	| nextValue |
	nextValue := thisValue.
	self do: [:each | nextValue := binaryBlock value: nextValue value: each].
	^ nextValue
]

{ #category : #testing }
Tuple >> is: aSymbol [
	^ aSymbol == #Tuple or: [super is: aSymbol]
]

{ #category : #testing }
Tuple >> isEmpty [
	^ self size = 0
]

{ #category : #testing }
Tuple >> isSequenceable [
	^ true
]

{ #category : #testing }
Tuple >> isTuple [
	^ true
]

{ #category : #testing }
Tuple >> isZero [
	^ self allSatisfy: [:each| each isZero]
]

{ #category : #testing }
Tuple >> isZeroAt: anInteger [
	^ (self at: anInteger) isZero
]

{ #category : #accessing }
Tuple >> last [
	^ self at: self size
]

{ #category : #accessing }
Tuple >> lastNonZero [
	"Answer the index of the last non-zero entry, or 0."
	self size to: 1 by: -1 do: [:i| (self at: i) isZero ifFalse: [^ i]].
	^ 0
]

{ #category : #accessing }
Tuple >> lastNonZeroDivisor [
	"Answer the index of the last non zero-divisor entry, or 0."
	self size to: 1 by: -1 do: [:i| (self scalars isZeroDivisor: (self at: i)) ifFalse: [^ i]].
	^ 0
]

{ #category : #accessing }
Tuple >> lift [
	"If the coefficients ring is a quotient R/I, answer a representative of the receiver over R. See >>%."
	^ self apply: self scalars lifting
]

{ #category : #operations }
Tuple >> multiplyBy: aNumber [
	self multiplyBy: aNumber startingAt: 1
]

{ #category : #operations }
Tuple >> multiplyBy: aNumber from: startIndex to: stopIndex [
	startIndex to: stopIndex do: [:i|
		self at: i put: (self at: i) * aNumber]
]

{ #category : #operations }
Tuple >> multiplyBy: aNumber startingAt: startIndex [
	self multiplyBy: aNumber from: startIndex to: self size
]

{ #category : #operations }
Tuple >> negated [
	^ self collect: [:each| each negated]
]

{ #category : #operations }
Tuple >> norm [
	^ self norm2 squareRoot
]

{ #category : #operations }
Tuple >> norm2 [
	^ self dot: self
]

{ #category : #accessing }
Tuple >> numerator [
	self scalars isLocalization ifFalse: [^ self].
	^ self * self denominator over: self scalars integers
]

{ #category : #converting }
Tuple >> over: aRing [
	self scalars = aRing ifFalse: [^ aRing tuple: self size evaluating: [:i| aRing ! (self at: i)]]
]

{ #category : #accessing }
Tuple >> parent [
	"Answer the tuple module where the receiver lives."
	^ 'self scalars ^ self size'
]

{ #category : #operations }
Tuple >> polynomialDivisionBy: aTuple [
	| quo rem lc n m |
	aTuple isZero ifTrue: [^ (ZeroDivide dividend: self) signal].
	quo := self zero.
	rem := self copy.
	m := aTuple lastNonZero. "m = degree(self)+1"
	lc := aTuple at: m.
	[(n := rem lastNonZero) >= m] "n = degree(rem)+1"
		whileTrue:
			[| i c |
			i := n-m+1.
			c := (rem at: n) / lc.
			quo at: i put: (quo at: i) + c.
			1 to: m do: [:j| rem at: j+i-1 put: (rem at: j+i-1) - ((aTuple at: j)*c)]].
	^ {quo. rem}
]

{ #category : #operations }
Tuple >> polynomialValue: anObject [
	"Evaluate the receiver (as an univariate polynomial) at the given argument using Horner's method."
	| answer one |
	answer := anObject zero.
	one := anObject one.
	self reverseDo: [:each| answer := anObject * answer + (one * each)].
	^ answer
]

{ #category : #operations }
Tuple >> primitive [
	"Answer the primitive part of the receiver."
	^ self isZero ifTrue: [self] ifFalse: [self /// self content]
]

{ #category : #printing }
Tuple >> printCoefficientsOn: aStream [
	| separator |
	separator := (self anySatisfy: [:any| any printString includesAnyOf: ', ']) ifTrue: [', '] ifFalse: [','].
	self do: [:x| aStream print: x] separatedBy: [aStream nextPutAll: separator]
]

{ #category : #printing }
Tuple >> printOn: aStream [
	aStream nextPut: $(.
	self printCoefficientsOn: aStream.
	aStream nextPut: $)
]

{ #category : #enumerating }
Tuple >> product [
	^ self product: [:each| each]
]

{ #category : #enumerating }
Tuple >> product: aBlock [
	^ self inject: self scalars one into: [:nextValue :each| nextValue * (aBlock value: each)]
]

{ #category : #operations }
Tuple >> quote:aTuple [ "í"
	^ self scalars matrix: self size @ aTuple size evaluating: [:i :j| (self at: i)*(aTuple at: j)]
]

{ #category : #converting }
Tuple >> readStream [
	^ ReadStream on: self
]

{ #category : #enumerating }
Tuple >> reverseDo: aBlock [
	self size to: 1 by: -1 do: [:each| aBlock value: (self at: each)]
]

{ #category : #accessing }
Tuple >> scalars [
	"Answer the ring of scalars (or ring of coefficients) of the receiver."
	^ self parent scalars
]

{ #category : #enumerating }
Tuple >> sum [
	^ self sum: [:each| each]
]

{ #category : #enumerating }
Tuple >> sum: aBlock [
	^ self inject: self scalars zero into: [:nextValue :each| nextValue + (aBlock value: each)]
]

{ #category : #operations }
Tuple >> support [
	^ (1 to: self size) reject: [:each| (self at: each) isZero]
]

{ #category : #operations }
Tuple >> weight [
	"Answer the Hamming weight of the receiver, i.e. the number of entries that are not zero."
	^ self count: [:each| each isZero not]
]

{ #category : #enumerating }
Tuple >> withIndexCollect: aBlock [
	^ self scalars tuple: self size evaluating: [:i| aBlock value: (self at: i) value: i]
]

{ #category : #enumerating }
Tuple >> withIndexDo: aBlock [
	1 to: self size do: [:index| aBlock value: (self at: index) value: index]
]

{ #category : #operations }
Tuple >> wrap: n [
	"Perform a cyclic right shift."
	^ self scalars tuple: self size evaluating: [:i| (self at: i-1-n \\ self size + 1)]
]

{ #category : #accessing }
Tuple >> x [
	^ self at: 1
]

{ #category : #accessing }
Tuple >> y [
	^ self at: 2
]

{ #category : #accessing }
Tuple >> z [
	^ self at: 3
]

{ #category : #accessing }
Tuple >> zero [
	^ self apply: [:each| each zero]
]

{ #category : #comparing }
Tuple >> ~ aTuple [
	"Answer true if the receiver and the argument are equivalent as homogeneous tuples."
	| index x y |
	self scalars isIntegralDomain ifFalse: [^ DomainError signal: 'not an integral domain'].
	"^ self scalars units anySatisfy: [:any| self * any = aTuple]"
	index := self lastNonZero.
	index = 0 ifTrue: [^ false].
	x := self at: index.
	y := aTuple at: index.
	y isZero ifTrue: [^ false].
	1 to: self size do: [:i|
		(self at: i) * y = ((aTuple at: i) * x) ifFalse: [^ false]].
	^ true
]
