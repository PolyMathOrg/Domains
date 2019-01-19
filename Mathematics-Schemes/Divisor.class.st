"
Weil divisors, i.e. formal sums (with integer coefficients) of prime divisors (integral closed subschemes of codimension 1) of an integral locally Noetherian scheme.
"
Class {
	#name : #Divisor,
	#superclass : #FormalSum,
	#category : #'Mathematics-Schemes-Divisors'
}

{ #category : #comparing }
Divisor >> <= aDivisor [
	^ (aDivisor - self) isEffective
]

{ #category : #comparing }
Divisor >> = anObject [
	^ (anObject isKindOf: Divisor) and: [self ~ anObject]
]

{ #category : #comparing }
Divisor >> >= aDivisor [
	^ (self - aDivisor) isEffective
]

{ #category : #accessing }
Divisor >> degree [
	| answer |
	answer := 0.
	self coefficientsDo: [:each| answer := answer + each].
	^ answer
]

{ #category : #operations }
Divisor >> gcd: aDivisor [
	| newCoefficients |
	newCoefficients := Dictionary new.
	self keysAndValuesDo: [:key :value|
		aDivisor at: key ifPresent: [:value2| newCoefficients at: key put: (value min: value2)]].
	^ (self class coefficients: newCoefficients) parent: parent
]

{ #category : #testing }
Divisor >> isEffective [
	^ self allSatisfy: [:each| each positive]
]

{ #category : #operations }
Divisor >> lcm: aDivisor [
	| answer |
	answer := self copy.
	aDivisor keysAndValuesDo: [:key :value|
		answer at: key put: ((self at: key) max: value)].
	^ answer
]

{ #category : #accessing }
Divisor >> support [
	| answer |
	answer := nil. "should start from the empty variety"
	self keysDo: [:each| answer := answer ifNil: [each] ifNotNil: [answer ñ each]].
	^ answer
]

{ #category : #comparing }
Divisor >> ~ aDivisor [
	"Answer true if the receiver and the argument are linearly equivalent."
	^ (self - aDivisor) isPrincipal
]
