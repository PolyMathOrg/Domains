"
Tuples with coefficients in an integer residue class ring (or field) Z/mZ. See ModularInteger, ModularIntegerRing, PrimeField.

Example:
	""A handy way to create a tuple of integers modulo 3:""
	(1,2,3,4) % 3

"
Class {
	#name : #ModularTuple,
	#superclass : #Tuple,
	#instVars : [
		'representatives',
		'scalars'
	],
	#category : #'Mathematics-Modules-Tuples'
}

{ #category : #'instance creation' }
ModularTuple class >> arrayClassForModulus: anInteger [
	anInteger <= 255 ifTrue: [^ ByteArray].
	anInteger <= 16rFFFFFFFF ifTrue: [^ WordArray].
	^ Array
]

{ #category : #'instance creation' }
ModularTuple class >> coefficients: anArray over: aModularIntegers [
	^ self new: anArray size over: aModularIntegers evaluating: [:i| anArray at: i]
]

{ #category : #'instance creation' }
ModularTuple class >> new: anInteger over: aModularIntegers [
	| array |
	array := (self arrayClassForModulus: aModularIntegers modulus) new: anInteger.
	^ self representatives: array over: aModularIntegers
]

{ #category : #'instance creation' }
ModularTuple class >> new: anInteger over: aModularIntegers evaluating: aBlock [
	| array |
	array := (self arrayClassForModulus: aModularIntegers modulus) new: anInteger.
	1 to: anInteger do: [:i| array at: i put: (aBlock value: i) representative].
	^ self representatives: array over: aModularIntegers
]

{ #category : #'instance creation' }
ModularTuple class >> representatives: anArray over: aModularIntegers [
	^ self basicNew scalars: aModularIntegers; representatives: anArray
]

{ #category : #operations }
ModularTuple >> * aNumber [
	| modulus x array |
	x := aNumber isInteger ifTrue: [aNumber] ifFalse: [aNumber representative].
	modulus := scalars modulus.
	array := representatives copy.
	1 to: self size do: [:i| array at: i put: (array at: i) * x \\ modulus].
	^ self class representatives: array over: scalars
]

{ #category : #operations }
ModularTuple >> + aTuple [
	| modulus a an b bn c |
	(an := self size) <= (bn := aTuple size) ifFalse: [^ aTuple + self].
	modulus := scalars modulus.
	a := representatives.
	b := aTuple representatives.
	c := representatives class new: bn.
	1 to: an do: [:i|
		c at: i put: (a at: i) + (b at: i) \\ modulus].
	c replaceFrom: an+1 to: bn with: b startingAt: an+1.
	^ self class representatives: c over: scalars
]

{ #category : #copying }
ModularTuple >> , anObject [
	self class = anObject class
		ifTrue:
			[scalars = anObject scalars ifFalse: [^ DomainError signal].
			^ self class representatives: representatives, anObject representatives over: scalars].
	scalars modulus = anObject modulus ifFalse: [^ DomainError signal].
	^ self class representatives: (representatives copyWith: anObject representative) over: scalars
]

{ #category : #comparing }
ModularTuple >> = aTuple [
	self class = aTuple class ifFalse: [^ super = aTuple halt].
	^ scalars = aTuple scalars and: [representatives = aTuple representatives]
]

{ #category : #operations }
ModularTuple >> add: aTuple by: aNumber from: startIndex to: stopIndex [
	| modulus representatives2 x |
	(self class = aTuple class "and: [scalars = aTuple scalars]")
		ifFalse: [^ super add: aTuple by: aNumber from: startIndex to: stopIndex].
	modulus := scalars modulus.
	representatives2 := aTuple representatives.
	x := aNumber representative.
	0 = x ifTrue: [^ self].
	startIndex to: stopIndex do: [:i|
		representatives at: i put: (representatives2 at: i) * x + (representatives at: i) \\ modulus]
]

{ #category : #accessing }
ModularTuple >> at: anInteger [
	^ scalars representative: (representatives at: anInteger ifAbsent: [^ scalars zero])
]

{ #category : #accessing }
ModularTuple >> at: anInteger put: aModularInteger [
	aModularInteger isInteger ifTrue: [^ representatives at: anInteger put: aModularInteger \\ scalars modulus].
	representatives at: anInteger put: aModularInteger representative.
	^ aModularInteger
]

{ #category : #operations }
ModularTuple >> convolution: aTuple [
	| modulus array |
	self isEmpty ifTrue: [^ self].
	aTuple isEmpty ifTrue: [^ aTuple].
	modulus := scalars modulus.
	array := representatives class new: self size + aTuple size - 1.
	array atAllPut: 0. "in case it's Array"
	representatives withIndexDo: [:xi :i|
		xi = 0 ifFalse:
			[aTuple representatives withIndexDo: [:yj :j| | index |
				index := i+j-1.
				array at: index put: xi*yj + (array at: index) \\ modulus]]].
	^ self class representatives: array over: scalars
]

{ #category : #copying }
ModularTuple >> copy [
	^ self class representatives: representatives copy over: scalars
]

{ #category : #copying }
ModularTuple >> copyFrom: start to: stop [
	^ self class representatives: (representatives copyFrom: start to: stop) over: scalars
]

{ #category : #copying }
ModularTuple >> copyWith: anElement [
	^ self class representatives: (representatives copyWith: anElement representative) over: scalars
]

{ #category : #operations }
ModularTuple >> dot: aTuple [
	| modulus representatives2 answer |
	(aTuple class = self class and: [scalars = aTuple scalars])
		ifFalse: [^ super dot: aTuple].
	modulus := scalars modulus.
	representatives2 := aTuple representatives.
	answer := 0.
	1 to: (representatives size min: representatives2 size) do: [:i|
		answer := (representatives at: i) * (representatives2 at: i) + answer \\ modulus].
	^ scalars representative: answer
]

{ #category : #operations }
ModularTuple >> hadamard: aTuple [
	| modulus array representatives2 |
	(self class = aTuple class and: [scalars = aTuple scalars])
		ifFalse: [^ super hadamard: aTuple].
	modulus := scalars modulus.
	array := representatives class new: (self size min: aTuple size).
	representatives2 := aTuple representatives.
	1 to: array size do: [:i| array at: i put: (representatives at: i) * (representatives2 at: i) \\ modulus].
	^ self class representatives: array over: scalars
]

{ #category : #comparing }
ModularTuple >> hash [
	^ representatives hash
]

{ #category : #testing }
ModularTuple >> isZero [
	1 to: representatives size do: [:i| (representatives at: i) == 0 ifFalse: [^ false]].
	^ true
]

{ #category : #testing }
ModularTuple >> isZeroAt: anInteger [
	^ (representatives at: anInteger) == 0
]

{ #category : #accessing }
ModularTuple >> lastNonZero [
	"Answer the index of the last non-zero entry, or 0."
	representatives size to: 1 by: -1 do: [:i| (representatives at: i) = 0 ifFalse: [^ i]].
	^ 0
]

{ #category : #accessing }
ModularTuple >> lastNonZeroDivisor [
	"Answer the index of the last non zero divisor entry, or 0."
	| m |
	m := scalars modulus.
	representatives size to: 1 by: -1 do: [:i| ((representatives at: i) gcd: m) = 1 ifTrue: [^ i]].
	^ 0
]

{ #category : #accessing }
ModularTuple >> lift [
	"Answer a representative integer tuple."
	| m h |
	m := scalars modulus.
	h := m >> 1.
	^ ZZ tuple: self size evaluating: [:i| | r | r := representatives at: i. r <= h ifTrue: [r] ifFalse: [r - m]]
]

{ #category : #'accessing-private' }
ModularTuple >> modulus [
	^ scalars modulus
]

{ #category : #operations }
ModularTuple >> multiplyBy: aNumber from: startIndex to: stopIndex [
	| modulus x |
	modulus := scalars modulus.
	x := aNumber representative.
	startIndex to: stopIndex do: [:i|
		representatives at: i put: (representatives at: i) * x \\ modulus]
]

{ #category : #operations }
ModularTuple >> negated [
	| modulus array |
	array := representatives copy.
	modulus := scalars modulus.
	1 to: self size do: [:i| array at: i put: (array at: i) negated \\ modulus].
	^ self class representatives: array over: scalars
]

{ #category : #operations }
ModularTuple >> polynomialDivisionBy: aTuple [
	| quo rem lcInv n m b modulus |
	aTuple isZero ifTrue: [^ (ZeroDivide dividend: self) signal].
	quo := self zero.
	rem := self copy.
	m := aTuple lastNonZero. "m = degree(self)+1"
	lcInv := (aTuple at: m) reciprocal.
	b := aTuple representatives.
	modulus := self modulus.
	[(n := rem lastNonZero) >= m] "n = degree(rem)+1"
		whileTrue:
			[| i c r |
			i := n-m+1.
			c := ((rem at: n) * lcInv) representative.
			quo at: i put: (quo at: i) + c.
			r := rem representatives.
			1 to: m do: [:j| r at: j+i-1 put: (r at: j+i-1) - ((b at: j)*c) \\ modulus]].
	^ {quo. rem}
]

{ #category : #operations }
ModularTuple >> polynomialValue: anObject [
	| modulus x answer |
	((anObject isKindOf: ModularInteger) and: [anObject modulus = (modulus := self modulus)])
		ifFalse: [^ super polynomialValue: anObject].
	x := anObject representative.
	answer := 0.
	representatives reverseDo: [:each| answer := x * answer + each \\ modulus].
	^ scalars representative: answer
]

{ #category : #printing }
ModularTuple >> printOn: aStream [
	self modulus > 16 ifTrue: [^ super printOn: aStream].
	1 to: self size do: [:i| (representatives at: i) printOn: aStream base: 16]
]

{ #category : #accessing }
ModularTuple >> representative [
	"Answer a representative integer tuple."
	^ ZZ tuple: representatives
]

{ #category : #'accessing-private' }
ModularTuple >> representatives [
	^ representatives
]

{ #category : #'accessing-private' }
ModularTuple >> representatives: anArray [
	representatives := anArray
"	representatives do: [:each| (each between: 0 and: modulus) ifFalse: [self halt]]"
]

{ #category : #operations }
ModularTuple >> reversed [
	^ self class representatives: representatives reversed over: scalars
]

{ #category : #accessing }
ModularTuple >> scalars [
	^ scalars
]

{ #category : #'accessing-private' }
ModularTuple >> scalars: aModularIntegers [
	scalars := aModularIntegers
]

{ #category : #accessing }
ModularTuple >> size [
	^ representatives size
]

{ #category : #operations }
ModularTuple >> weight [
	"Answer the Hamming weight of the receiver, i.e. the number of entries that are not zero."
	^ representatives count: [:each| each ~~ 0]
]
