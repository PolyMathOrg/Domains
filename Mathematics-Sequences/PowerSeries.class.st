"
Univariate formal power series.

Examples:
	PowerSeries coefficients: Sequence fibonacci.
	Sequence fibonacci generatingSeries.
	PowerSeries cos squared + PowerSeries sin squared.

Structure:
 coefficients	Sequence -- the coefficients of the power series

"
Class {
	#name : #PowerSeries,
	#superclass : #Object,
	#instVars : [
		'parent',
		'coefficients'
	],
	#category : #'Mathematics-Sequences'
}

{ #category : #'instance creation' }
PowerSeries class >> coefficients: aSequence [
	^ self new coefficients: aSequence
]

{ #category : #examples }
PowerSeries class >> cos [
	^ self
		coefficients:
			(Sequence
				to: QQ
				evaluating: [ :n | 
					n even
						ifTrue: [ 0 ]
						ifFalse: [ | k |
							k := (n - 1) / 2.
							(-1 raisedTo: k) / (2 * k) factorial ] ])
]

{ #category : #examples }
PowerSeries class >> exp [
	^ self coefficients: (Sequence to: QQ evaluating: [:n| 1 / n factorial])
]

{ #category : #'instance creation' }
PowerSeries class >> fromPolynomial: aPolynomial [
	^ self coefficients: (CFiniteSequence to: aPolynomial scalars initialValues: aPolynomial coefficients periodic: {aPolynomial scalars zero})
]

{ #category : #examples }
PowerSeries class >> sin [
	^ self
		coefficients:
			(Sequence
				to: QQ
				evaluating: [ :n | 
					n odd
						ifTrue: [ 0 ]
						ifFalse: [ | k |
							k := n / 2 - 1.
							(-1 raisedTo: k) / (2 * k + 1) factorial ] ])
]

{ #category : #examples }
PowerSeries class >> taylorSeriesOf: aFunction at: x0 [
	| f n |
	f := aFunction.
	n := 0.
	^ self coefficients:
		(Sequence
			to: aFunction codomain
			streamming:
				[| value |
				value := (f value: x0) / n factorial.
				f := f derivative.
				n := n + 1.
				value])
]

{ #category : #arithmetic }
PowerSeries >> * anObject [
	(self scalars includes: anObject)
		ifTrue: [^ self class coefficients: coefficients * anObject].
	(anObject isKindOf: self class)
		ifTrue: [^ self class coefficients: (coefficients convolution: anObject coefficients)].
	(anObject isKindOf: Polynomial)
		ifTrue: [^ self * (self class fromPolynomial: anObject)].
	^ DomainError signal
]

{ #category : #arithmetic }
PowerSeries >> + anObject [
	(self scalars includes: anObject)
		ifTrue: [^ self class coefficients: coefficients + (CFiniteSequence to: self scalars initialValues: {anObject} periodic: {anObject zero})].
	(anObject isKindOf: self class)
		ifTrue: [^ self class coefficients: coefficients + anObject coefficients].
	(anObject isKindOf: Polynomial)
		ifTrue: [^ self + (self class fromPolynomial: anObject)].
	^ DomainError signal
]

{ #category : #arithmetic }
PowerSeries >> - anObject [
	^ self + anObject negated
]

{ #category : #arithmetic }
PowerSeries >> / anObject [
	^ self * anObject reciprocal
]

{ #category : #comparing }
PowerSeries >> = anObject [
	^ (anObject isKindOf: PowerSeries) and: [self coefficients = anObject coefficients]
]

{ #category : #converting }
PowerSeries >> asRationalFunction [
	^ coefficients generatingFunction
]

{ #category : #accessing }
PowerSeries >> coefficients [
	^ coefficients
]

{ #category : #'accessing-private' }
PowerSeries >> coefficients: aSequence [
	coefficients := aSequence
]

{ #category : #operations }
PowerSeries >> derivative [
	^ self class coefficients: coefficients << 1 * CFiniteSequence identity
]

{ #category : #comparing }
PowerSeries >> hash [
	^ coefficients hash
]

{ #category : #accessing }
PowerSeries >> indeterminate [
	^ 1
]

{ #category : #arithmetic }
PowerSeries >> inverse [
	| b1 a |
	a := coefficients.
	b1 := (a at: 1) reciprocal.
	^ self class coefficients:
		(Sequence
			to: self scalars
			recurrence:
				[:b :n|
				n=1
					ifTrue: [b1]
					ifFalse: [b1 negated * ((2 to: n) sum: [:i| (a at: i+1) * (b at: n-i+1)])]])
]

{ #category : #testing }
PowerSeries >> isUnit [
	^ self scalars isUnit: self independentCoefficient
]

{ #category : #testing }
PowerSeries >> isZero [
	^ coefficients isZero
]

{ #category : #arithmetic }
PowerSeries >> negated [
	^ self class coefficients: coefficients negated
]

{ #category : #accessing }
PowerSeries >> parent [
	^ parent
]

{ #category : #'accessing-private' }
PowerSeries >> parent: aPowerSeriesRing [
	parent := aPowerSeriesRing
]

{ #category : #printing }
PowerSeries >> printOn: aStream [
	| P f n |
	n := coefficients printLimit.
	P := coefficients codomain polynomials.
	'f := P coefficients: (coefficients copyFrom: coefficients startIndex to: coefficients startIndex + n) :: orderedBy: #llex.'
	aStream print: f; nextPutAll: ' + ', 'O' italic, '('; print: 'P x ^ (n+1)'; nextPut: $)
]

{ #category : #arithmetic }
PowerSeries >> raisedTo: anInteger [
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

{ #category : #arithmetic }
PowerSeries >> reciprocal [
	| b1 a |
	self flag: #fix. "this is composition inverse, same as >>inverse"
	a := coefficients.
	b1 := (a at: 1) reciprocal.
	^ self class coefficients:
		(Sequence
			to: self scalars
			initialValues: {b1}
			recurrence:
				[:b :n|
				b1 negated * ((2 to: n) sum: [:i| (a at: i+1) * (b at: n-i+1)])])
]

{ #category : #accessing }
PowerSeries >> scalars [
	^ coefficients codomain
]

{ #category : #arithmetic }
PowerSeries >> squared [
	^ self * self
]

{ #category : #accessing }
PowerSeries >> terms [
	| P |
	P := self scalars polynomials.
	^ Sequence to: P evaluating: [:i| P coefficient: (coefficients at: i) degree: i-1]
]

{ #category : #operations }
PowerSeries >> value: anObject upTo: n [
	| answer |
	answer := anObject zero.
	self terms do: [:each| each degree > n ifTrue: [^ answer]. answer := answer + (each value: anObject)].
	^ answer
]
