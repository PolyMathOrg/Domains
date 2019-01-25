"
Quadratic number fields, i.e. number fields with defining quadratic polynomial of the form x^2 - d, with d a squarefree integer.
"
Class {
	#name : #QuadraticField,
	#superclass : #NumberField,
	#category : #'Mathematics-Fields-Number Fields'
}

{ #category : #examples }
QuadraticField class >> example [
	^ QuadraticField sqrt: -5
]

{ #category : #'instance creation' }
QuadraticField class >> sqrt: anInteger [
	^ self new sqrt: anInteger
]

{ #category : #private }
QuadraticField >> d [
	^ self polynomial independentCoefficient negated
]

{ #category : #accessing }
QuadraticField >> discriminant [
	| d |
	^ (d := self d) \\ 4 = 1 ifTrue: [d] ifFalse: [d*4]
]

{ #category : #accessing }
QuadraticField >> integers [
	"Answer the ring of integers of the receiver."
	^ QuadraticRing on: self
]

{ #category : #accessing }
QuadraticField >> integralBasis [
	| w |
	w := self x + (self embed: self discriminant) / (self embed: 2).
	^ {self one. w}
]

{ #category : #testing }
QuadraticField >> isMonogenic [
	^ true
]

{ #category : #testing }
QuadraticField >> isQuadratic [
	^ true
]

{ #category : #'accessing-private' }
QuadraticField >> polynomial: aPolynomial [
	(aPolynomial degree = 2 and: [aPolynomial terms size = 2 and: [aPolynomial independentCoefficient isZero not]])
		ifFalse: [self error: 'malformed polynomial'].
	super polynomial: aPolynomial
]

{ #category : #printing }
QuadraticField >> printOn: aStream [
	aStream print: self scalars; nextPut: $(; print: self x; nextPut: $)
]

{ #category : #private }
QuadraticField >> sqrt: anInteger [
	| P d |
	d := anInteger squareFree.
	(d == 0 or: [d == 1]) ifTrue: [DomainError signal: 'not a quadratic field'].
	P := QQ polynomialsIn: {d == -1 ifTrue: ['i' italic] ifFalse: ['sqrt ', d asString]}.
	self polynomial: P x squared - d
]
