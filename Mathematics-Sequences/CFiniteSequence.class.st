"
Constant-recursive (or C-recursive or C-finite) sequences, i.e. sequences satisfying homogeneous linear recurrences with constant coefficients:
	a(n) = c_1 a(n-1) + ... + c_d a(n-d)

These sequences are closed under:
- addition a(n)+b(n)
- (Hadamard or termwise) multiplication a(n)*b(n)
- convolution (Cauchy multiplication)
- interlacing {a(1),b(1),a(2),b(2),...}
- scalar multiplication a(n)*c
- (left) shift a(n+k), k>0
- indefinite sumation a(1)+a(2)+...+a(n)
- multisection a(mn+r), 0 <= r < m.

Power series whose coefficients are linear recursive sequences are closed under:
- addition
- multiplication
- derivation

Example:
	CFiniteSequence fibonacci.
	CFiniteSequence fibonacci generatingFunction

Example:
	| f |
	f := CFiniteSequence fibonacci * CFiniteSequence pellNumbers.
	f minimalPolynomial

"
Class {
	#name : #CFiniteSequence,
	#superclass : #Sequence,
	#instVars : [
		'coefficients',
		'initialValues'
	],
	#category : #'Mathematics-Sequences'
}

{ #category : #examples }
CFiniteSequence class >> fibonacci [
	"The Fibonacci sequence defined as a C-finite sequence."
	^ CFiniteSequence initialValues: #(0 1) coefficients: #(1 1)
]

{ #category : #examples }
CFiniteSequence class >> geometric: aNumber [
	(aNumber isInteger or: [aNumber isFraction])
		ifFalse: [^ DomainError signal: 'argument is not rational'].
	^ CFiniteSequence to: QQ initialValues: #(1) coefficients: {aNumber}
]

{ #category : #examples }
CFiniteSequence class >> id [
	"The identity sequence id(n) := n, defined by a recurrence."
	^ CFiniteSequence to: QQ initialValues: #(1 2) coefficients: #(-1 2)
]

{ #category : #'instance creation' }
CFiniteSequence class >> initialValues: anArray coefficients: anotherArray [
	^ self to: ZZ initialValues: anArray coefficients: anotherArray
]

{ #category : #examples }
CFiniteSequence class >> jacobsthalNumbers [
	"The Jacobsthal numbers."
	^ CFiniteSequence initialValues: #(0 1) coefficients: #(2 1)
]

{ #category : #examples }
CFiniteSequence class >> lucasNumbers [
	"The Lucas numbers."
	^ CFiniteSequence initialValues: #(2 1) coefficients: #(1 1)
]

{ #category : #examples }
CFiniteSequence class >> pellNumbers [
	"The Pell numbers."
	^ CFiniteSequence initialValues: #(0 1) coefficients: #(1 2)
]

{ #category : #'instance creation' }
CFiniteSequence class >> to: codomain constant: anObject [
	^ self to: codomain initialValues: {anObject} coefficients: {anObject one}
]

{ #category : #'instance creation' }
CFiniteSequence class >> to: codomain evaluating: aBlock maxOrder: n [
	| initialValues bm f |
	initialValues := (1 to: 2*n) collect: aBlock.
	bm := ModifiedBerlekampMassey new
		field: (codomain isField ifTrue: [codomain] ifFalse: [codomain fractions]);
		input: initialValues.
	f := bm minimalPolynomial.
	^ self to: codomain initialValues: (initialValues copyFrom: 1 to: f degree) minimalPolynomial:f
]

{ #category : #'instance creation' }
CFiniteSequence class >> to: codomain initialValues: anArray characteristicPolynomial: aPolynomial [
	^ self to: codomain initialValues: anArray coefficients: aPolynomial tail negated coefficients
]

{ #category : #'instance creation' }
CFiniteSequence class >> to: aCodomain initialValues: anArray coefficients: anotherArray [
	^ self new codomain: aCodomain; initialValues: anArray; coefficients: anotherArray
]

{ #category : #'instance creation' }
CFiniteSequence class >> to: codomain initialValues: anArray minimalPolynomial: aPolynomial [
	| answer |
	answer := self to: codomain initialValues: anArray characteristicPolynomial: aPolynomial.
	answer propertyAt: #minimal put: answer.
	^ answer
]

{ #category : #'instance creation' }
CFiniteSequence class >> to: codomain initialValues: initialArray periodic: periodArray [
	| coefficients |
	coefficients := Array new: initialArray size + periodArray size.
	coefficients atAllPut: periodArray first zero.
	coefficients at: initialArray size + 1 put: periodArray first one.
	^ self to: codomain initialValues: initialArray, periodArray coefficients: coefficients
]

{ #category : #'instance creation' }
CFiniteSequence class >> to: codomain periodic: anArray [
	| coefficients |
	coefficients := Array new: anArray size.
	coefficients atAllPut: anArray first zero.
	coefficients at: 1 put: anArray first one.
	^ self to: codomain initialValues: anArray coefficients: coefficients
]

{ #category : #operations }
CFiniteSequence >> * anObject [
	(anObject isKindOf: self class)
		ifTrue: [^ self class to: self codomain evaluating: super * anObject maxOrder: self order * anObject order].
	(self codomain includes: anObject)
		ifTrue: [^ self class to: self codomain evaluating: super * anObject maxOrder: self order].
	^ super * anObject
]

{ #category : #operations }
CFiniteSequence >> + aSequence [
	(aSequence isKindOf: self class) ifFalse: [^ super + aSequence].
	^ self class to: self codomain evaluating: super + aSequence maxOrder: self order + aSequence order
]

{ #category : #comparing }
CFiniteSequence >> = aSequence [
	| f g |
	(aSequence isKindOf: CFiniteSequence)
		ifFalse: [^ super = aSequence].
	f := self minimal.
	g := aSequence minimal.
	^ f coefficients = g coefficients and: [f initialValues = g initialValues]
]

{ #category : #accessing }
CFiniteSequence >> at: n [
	self order = 0 ifTrue: [^ self codomain zero].
	n <= initialValues size ifTrue: [^ initialValues at: n].
	^' (self matrix ^ (n - self order) * initialValues) last'
"	answer := 0.
	1 to: self order do: [:i |
		answer := (self at: n - self order + i - 1) * (coefficients at: i) + answer].
	^ answer"
]

{ #category : #accessing }
CFiniteSequence >> characteristicPolynomial [
	^ self codomain polynomials coefficients: (coefficients negated copyWith: self codomain one)
]

{ #category : #accessing }
CFiniteSequence >> coefficients [
	^ coefficients
]

{ #category : #'accessing-private' }
CFiniteSequence >> coefficients: anArray [
	coefficients := anArray
]

{ #category : #operations }
CFiniteSequence >> convolution: aSequence [
	(aSequence isKindOf: self class) ifFalse: [^ super convolution: aSequence].
	^ self class to: self codomain evaluating: (super convolution: aSequence) maxOrder: self order * aSequence order
]

{ #category : #series }
CFiniteSequence >> generatingFunction [
	| r s |
	"Answer the generating function of the receiver, which is a rational function that equals its ordinary generating series."
	s := self characteristicPolynomial reversed.
	r := self codomain polynomials coefficients:
		((0 to: self order - 1) collect: [:j|
			(self at: j+1) - ((1 to: j) sum: [:i| (s coefficientAtDegree: i) * (self at: j-i+1)])]).
	^ r / s
]

{ #category : #accessing }
CFiniteSequence >> initialValues [
	^ initialValues
]

{ #category : #'accessing-private' }
CFiniteSequence >> initialValues: anArray [
	initialValues := anArray.
	initialValues isTuple ifFalse: [initialValues := self codomain tuple: initialValues]
]

{ #category : #testing }
CFiniteSequence >> isMinimal [
	^ self minimalPolynomial = self characteristicPolynomial
]

{ #category : #testing }
CFiniteSequence >> isZero [
	^ self minimal order = 0
]

{ #category : #accessing }
CFiniteSequence >> matrix [
	^ self propertyAt: #matrix ifAbsentPut: [self characteristicPolynomial companion transposed]
]

{ #category : #operations }
CFiniteSequence >> minimal [
	^ self propertyAt: #minimal ifAbsentPut: [self class to: self codomain evaluating: self maxOrder: self order]
]

{ #category : #accessing }
CFiniteSequence >> minimalPolynomial [
	^ self minimal characteristicPolynomial
]

{ #category : #operations }
CFiniteSequence >> negated [
	^ self class to: self codomain evaluating: super negated maxOrder: self order
]

{ #category : #accessing }
CFiniteSequence >> order [
	^ coefficients size
]

{ #category : #printing }
CFiniteSequence >> printLimit [
	^ self order + 10 min: super printLimit
]

{ #category : #operations }
CFiniteSequence >> shift: anInteger [
	anInteger > 0 ifTrue: [^ super shift: anInteger].
	^ self class to: self codomain evaluating: (super shift: anInteger) maxOrder: self order squared
]

{ #category : #operations }
CFiniteSequence >> squared [
	| n |
	n := self order.
	^ self class to: self codomain evaluating: super squared maxOrder: n*(n-1)/2
]

{ #category : #accessing }
CFiniteSequence >> startIndex [
	^ 1
]

{ #category : #operations }
CFiniteSequence >> sum [
	"Answer the indefinite sum of the receiver."
	^ self class to: self codomain evaluating: super sum maxOrder: self order squared
]
