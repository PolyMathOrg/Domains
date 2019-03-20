"
The singletion global instance QQ is the field of rational numbers.
"
Class {
	#name : #RationalField,
	#superclass : #FractionRing,
	#category : #'Mathematics-Fields'
}

{ #category : #'class initialization' }
RationalField class >> initialize [
	Smalltalk at: #QQ put: self new
]

{ #category : #elements }
RationalField >> ! anObject [
	(anObject isInteger or: [ anObject isFraction ])
		ifTrue: [ ^ anObject ].
	^ super ! anObject 
]

{ #category : #comparing }
RationalField >> <= aDomain [
	^ aDomain isField
		and: [ (aDomain includes: 1) and: [ aDomain includes: 0 ] ]
]

{ #category : #comparing }
RationalField >> = anObject [
	^ anObject class == self class
]

{ #category : #operations }
RationalField >> adic: aPrime [
	^ AdicField p: aPrime 
]

{ #category : #operations }
RationalField >> adjoin: anAlgebraicNumber [
	^ NumberField adjoint: anAlgebraicNumber
]

{ #category : #operations }
RationalField >> algebraicClosure [
	^ CC
]

{ #category : #morphisms }
RationalField >> automorphisms [
	^ TransformationGroup new elements: {self id}
]

{ #category : #accessing }
RationalField >> degree [
	"Answer the degree of the receiver as an algebraic extension (as a number field)."
	^ 1
]

{ #category : #enumerating }
RationalField >> do: aBlock [
	"Iterate over the rational numbers by breadth-first traversal of the Calkin-Wilf tree. This is an extension of the Calkin-Wilf sequence to include 0 and the negative numbers."

	aBlock value: 0.
	self
		positiveDo: [ :each | 
			aBlock
				value: each;
				value: each negated ]
]

{ #category : #morphisms }
RationalField >> embed: anInteger [
	^ anInteger	"because in Smalltalk Fractions of denominator 1 are always reduced to their Integer numerator" 
]

{ #category : #morphisms }
RationalField >> embedding [
	^ self
		propertyAt: #embedding
		ifAbsentPut: [ "because in Smalltalk Fractions of denominator 1 are always reduced to their Integer numerator" (self integers to: self evaluating: [ :x | x ]) name: 'i' ]
]

{ #category : #operations }
RationalField >> extension: aPolynomial [
	"Answer the algebraic extension of the receiver defined by the given irreducible polynomial."
	aPolynomial scalars = self ifFalse: [DomainError signal: 'polynomial coefficients not from this field'].
	aPolynomial parent isUnivariate ifFalse: [DomainError signal: 'not univariate poylnomial'].
"	aPolynomial degree = 2 ifTrue: [^ QuadraticField polynomial: aPolynomial]."
	^ NumberField polynomial: aPolynomial
]

{ #category : #accessing }
RationalField >> generators [
	^ #(1)
]

{ #category : #comparing }
RationalField >> hash [
	^ self class hash
]

{ #category : #accessing }
RationalField >> ideal [
	^ ZZ zeroIdeal
]

{ #category : #testing }
RationalField >> includes: anObject [
	^ anObject isNumber
		and: [ anObject isRational or: [ anObject isFloat ] ]
]

{ #category : #accessing }
RationalField >> integers [
	^ ZZ 
]

{ #category : #testing }
RationalField >> isField [
	^ true 
]

{ #category : #testing }
RationalField >> isFinite [
	^ false 
]

{ #category : #testing }
RationalField >> isPrime [
	"Q is a prime field (it has no proper subfields)."

	^ true 
]

{ #category : #testing }
RationalField >> isReal [
	^ true 
]

{ #category : #testing }
RationalField >> isUnit: anIntegerOrFraction [
	"Answer true if the argument is invertible."

	^ anIntegerOrFraction ~= 0
]

{ #category : #elements }
RationalField >> one [
	^ 1 
]

{ #category : #enumerating }
RationalField >> positiveDo: aBlock [
	"Iterate over the rational numbers by breadth-first traversal of the Calkin-Wilf tree.
	The nodes of the Calkin-Wilf tree of any given depth level have height strictly greater than the height of their parents."

	| q |
	q := 1.
	[ aBlock value: q.
	q := 1 / (2 * q floor - q + 1) ] repeat
]

{ #category : #printing }
RationalField >> printOn: aStream [
	aStream nextPutAll: 'ℚ'
]

{ #category : #operations }
RationalField >> realClosure [
	^ RR 
]

{ #category : #accessing }
RationalField >> size [
	^ Aleph new
]

{ #category : #accessing }
RationalField >> valuation [
	"Answer the absolute value valuation."
	^ Function from: self to: self evaluating: [:x| x abs]
]

{ #category : #accessing }
RationalField >> valuation: p [
	"Answer the p-adic valuation."
	^ Function from: self to: NN evaluating: [:x| p / ((x numerator factors occurrencesOf: p) - (x denominator factors occurrencesOf: p))]
]

{ #category : #elements }
RationalField >> zero [
	^ 0
]
