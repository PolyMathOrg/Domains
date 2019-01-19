"
Polynomials in one or more indeterminates, represented in sparse form.

Multivariate polynomials are internally stored as a list of associations 'monomial -> coefficient'. Zero coefficients are excluded, and the list is kept sorted according to the corresponding monomial ordering.
"
Class {
	#name : #MultivariatePolynomial,
	#superclass : #Polynomial,
	#instVars : [
		'parts'
	],
	#category : #'Mathematics-Polynomials'
}

{ #category : #'instance creation' }
MultivariatePolynomial class >> parts: aCollection [
	^ self basicNew parts: aCollection
]

{ #category : #arithmetic }
MultivariatePolynomial >> + anObject [
	(self parent includes: anObject)
		ifTrue: [^ self addedWithPolynomial: anObject].
	((self scalars includes: anObject) or: [anObject isInteger])
		ifTrue: [^ self + (self one * anObject)].
	(anObject isKindOf: RationalFunction)
		ifTrue: [^ anObject + self].
	^ DomainError signal
]

{ #category : #comparing }
MultivariatePolynomial >> = aPolynomial [
	self == aPolynomial ifTrue: [^ true].
	aPolynomial class = self class ifTrue: [^ parts = aPolynomial parts].
	^ super = aPolynomial
]

{ #category : #arithmetic }
MultivariatePolynomial >> addedWithPolynomial: aPolynomial [
	| newAssociations |
	newAssociations := OrderedCollection new: parts size + aPolynomial parts size.
	newAssociations resetTo: 1.
	self sum: parts with: aPolynomial parts into: newAssociations.
	^ parent parts: newAssociations
]

{ #category : #operations }
MultivariatePolynomial >> apply: aMorphism [
	"Answer a new polynomial with coefficients obtainted by applying aMorphism to the coefficients of the receiver. This morphism is a ring homomorphism from the scalars ring.
	If aMorphism is a block we assume the parent doesn't change, i.e. the block must evaluate to values within the scalars ring of the receiver."

	| newAssociations |
	newAssociations := OrderedCollection new: parts size.
	parts do: [:each| | newValue |
		(newValue := aMorphism value: each value) isZero
			ifFalse: [newAssociations add: (each copy value: newValue)]].
	^ (aMorphism isBlock ifTrue: [parent] ifFalse: [parent over: aMorphism codomain]) parts: newAssociations
]

{ #category : #'accessing coefficients' }
MultivariatePolynomial >> at: aMonomial [
	^ self at: aMonomial ifAbsent: [self scalars zero]
]

{ #category : #'accessing-private' }
MultivariatePolynomial >> at: aMonomial add: aNumber [
	parts isEmpty ifTrue: [aNumber isZero ifFalse: [parts add: aMonomial -> aNumber]. ^ self].
	parts
		findBinaryIndex: [:each| (each key compare: aMonomial) negated]
		do: [:index| | association newValue |
			association := parts at: index.
			(newValue := association value + aNumber) isZero
				ifTrue: [parts removeIndex: index]
				ifFalse: [association value: newValue "associations at: index put: aMonomial -> newValue"]]
		ifNone: [:low :high| aNumber isZero ifFalse: [parts add: aMonomial -> aNumber beforeIndex: high]]
]

{ #category : #'accessing-private' }
MultivariatePolynomial >> at: aMonomial ifAbsent: exceptionBlock [
	^ parts findBinary: [:each| (each key compare: aMonomial) negated] do: [:each| each value] ifNone: [:high :low| exceptionBlock value]
]

{ #category : #'accessing-private' }
MultivariatePolynomial >> at: key ifPresent: presentBlock [
	"Lookup the given key in the receiver. If it is present, answer the value of evaluating the given block with the value associated with the key. Otherwise, answer nil."

	| v |
	v := self at: key ifAbsent: [ ^ nil ].
	^ presentBlock value: v
]

{ #category : #'accessing-private' }
MultivariatePolynomial >> at: aMonomial put: aNumber [
	parts isEmpty ifTrue: [aNumber isZero ifFalse: [parts add: aMonomial -> aNumber]. ^ self].
	parts
		findBinaryIndex: [:each| (each key compare: aMonomial) negated]
		do: [:index| aNumber isZero ifTrue: [parts removeIndex: index] ifFalse: [(parts at: index) value: aNumber]]
		ifNone: [:low :high| aNumber isZero ifFalse: [parts add: aMonomial -> aNumber beforeIndex: high]].
	^ aNumber
]

{ #category : #accessing }
MultivariatePolynomial >> bitSize [
	self isZero ifTrue: [^ 0].
	^ parts sum: [:each| each key bitSize + each value bitSize]
]

{ #category : #deprecated }
MultivariatePolynomial >> coefficientAt: aMonomial [
	"Answer the coefficient of the monomial given by the argument."
	^ self at: aMonomial
]

{ #category : #deprecated }
MultivariatePolynomial >> coefficientAt: aMonomial put: value [
	^ self at: aMonomial put: value
]

{ #category : #enumerating }
MultivariatePolynomial >> coefficientsDo: aBlock [
	parts do: [:each| aBlock value: each value]
]

{ #category : #copying }
MultivariatePolynomial >> copy [
	^ parent parts: (parts collect: [:each| each copy])
]

{ #category : #arithmetic }
MultivariatePolynomial >> dividedByMonomial: aMonomial [
	"The monomial ordering is preserved by this operation."
	^ parent parts: (parts collect: [:each| each key / aMonomial -> each value])
]

{ #category : #arithmetic }
MultivariatePolynomial >> dividedByScalar: aNumber [
	^ parent parts: (parts collect: [:each| each copy value: each value / aNumber])
]

{ #category : #arithmetic }
MultivariatePolynomial >> exactlyDividedBy: aPolynomial [
	"Answer the exact division of the receiver by the argument."
	self isZero ifTrue: [^ self].
	aPolynomial isConstant ifTrue: [^ self dividedByScalar: aPolynomial leadingCoefficient].
	^ (MultivariatePolynomialDivision divide: self by: {aPolynomial}) exactQuotient
]

{ #category : #comparing }
MultivariatePolynomial >> hash [
	^ parts hash
]

{ #category : #testing }
MultivariatePolynomial >> isZero [
	^ parts isEmpty
]

{ #category : #'accessing coefficients' }
MultivariatePolynomial >> leadingCoefficient [
	^ parts isEmpty ifTrue: [self scalars zero] ifFalse: [parts last value]
	"^ self isZero ifTrue: [self scalars zero] ifFalse: [self at: self leadingMonomial]"
]

{ #category : #'accessing monomials' }
MultivariatePolynomial >> leadingMonomial [
	^ parts isEmpty ifFalse: [parts last key]
"
	| answer |
	self monomialsDo: [:each| (answer isNil or: [each > answer]) ifTrue: [answer := each]].
	^ answer"
]

{ #category : #'accessing terms' }
MultivariatePolynomial >> leadingTerm [
	"Answer the first term of the receiver."

	| leadingPart |
	self isZero ifTrue: [^ self].
	leadingPart := parts last.
	^ self parent coefficient: leadingPart value monomial: leadingPart key
]

{ #category : #enumerating }
MultivariatePolynomial >> monomialsApply: aBlock [
	| dictionary newParts |
	dictionary := Dictionary new: parts size.
	parts do: [:each|
		dictionary at: (aBlock value: each key) add: each value].
	newParts := OrderedCollection new: dictionary size.
	newParts resetTo: 1.
	dictionary associationsDo: [:each| each value isZero ifFalse: [newParts add: each]].
	newParts sort.
	^ self parent parts: newParts
]

{ #category : #enumerating }
MultivariatePolynomial >> monomialsDo: aBlock [
	"Iterate over the support of the receiver, i.e. the monomials with non-zero coefficient."
	parts do: [:each| aBlock value: each key]
]

{ #category : #arithmetic }
MultivariatePolynomial >> multipliedByMonomial: aMonomial [
	"The monomial ordering is preserved by this operation."
	^ parent parts: (parts collect: [:each| each key * aMonomial -> each value])
]

{ #category : #arithmetic }
MultivariatePolynomial >> multipliedByPolynomial: aPolynomial [
	| dictionary newAssociations |
	dictionary := Dictionary new: parts size + aPolynomial parts size.
	parts do: [:each|
		aPolynomial parts do: [:other|
			dictionary at: each key * other key add: each value * other value]].
	newAssociations := OrderedCollection new: dictionary size.
	newAssociations resetTo: 1.
	dictionary associationsDo: [:each| each value isZero ifFalse: [newAssociations add: each]].
	newAssociations sort.
	^ self parent parts: newAssociations
]

{ #category : #arithmetic }
MultivariatePolynomial >> multipliedByScalar: aNumber [
	| newAssociations |
	aNumber isZero ifTrue: [^ parent zero].
"	parent scalars isIntegralDomain ifTrue: [^ parent parts: (parts collect: [:each| each copy value: each value * aNumber])]."
	newAssociations := OrderedCollection new: parts size.
	newAssociations resetTo: 1.
	parts do: [:each| | newValue |
		(newValue := each value * aNumber) isZero
			ifFalse: [newAssociations add: (each copy value: newValue)]].
	^ parent parts: newAssociations
]

{ #category : #arithmetic }
MultivariatePolynomial >> negated [
	"Answer the additive inverse of the receiver."
	^ parent parts: (parts collect: [:each| each key -> each value negated])
]

{ #category : #converting }
MultivariatePolynomial >> over: aRing [
	| newParts |
	self scalars = aRing ifTrue: [^ self].
	newParts := OrderedCollection new: parts size.
	parts do: [:each| | newValue |
		(newValue := aRing ! each value) isZero
			ifFalse: [newParts add: (each copy value: newValue)]].
	^ (self parent over: aRing) parts: newParts
]

{ #category : #'accessing-private' }
MultivariatePolynomial >> parts [
	^ parts
]

{ #category : #'accessing-private' }
MultivariatePolynomial >> parts: aCollection [
	parts := aCollection
]

{ #category : #enumerating }
MultivariatePolynomial >> partsDo: aBlock [
	parts do: aBlock
]

{ #category : #private }
MultivariatePolynomial >> sum: someAssociations with: otherAssociations into: newAssociations [
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
