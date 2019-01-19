Class {
	#name : #PowerSeriesRing,
	#superclass : #Ring,
	#instVars : [
		'polynomials'
	],
	#category : #'Mathematics-Sequences'
}

{ #category : #'instance creation' }
PowerSeriesRing class >> new: anInteger over: aRing [
	^ self polynomials: (aRing polynomialsIn: anInteger ordering: #llex) "llex is a local ordering"
]

{ #category : #'instance creation' }
PowerSeriesRing class >> new: anInteger over: aRing ordering: aMonomialOrdering [
	^ self polynomials: (PolynomialRing new: anInteger over: aRing ordering: aMonomialOrdering)
]

{ #category : #'instance creation' }
PowerSeriesRing class >> over: aRing [
	^ self new scalars: aRing
]

{ #category : #'instance creation' }
PowerSeriesRing class >> polynomials: aPolynomialRing [
	^ self new polynomials: aPolynomialRing
]

{ #category : #accessing }
PowerSeriesRing >> characteristic [
	^ self scalars characteristic
]

{ #category : #morphisms }
PowerSeriesRing >> embed: aPolynomial [
	^ PowerSeries fromPolynomial: aPolynomial
]

{ #category : #morphisms }
PowerSeriesRing >> embedding [
	"Answer the embedding map from the polynomial ring into the receiver."
	^ self propertyAt: #embedding ifAbsentPut: [(self polynomials to: self evaluating: [:x| self embed: x]) name: 'i']
]

{ #category : #accessing }
PowerSeriesRing >> generators [
	^ self polynomials generators collect: [:each| self embed: each]
]

{ #category : #testing }
PowerSeriesRing >> isLocal [
	^ true
]

{ #category : #testing }
PowerSeriesRing >> isMultivariate [
	^ self polynomials isMultivariate
]

{ #category : #testing }
PowerSeriesRing >> isUnit: aPowerSeries [
	"Answer true if the argument is invertible."
	^ self scalars isUnit: aPowerSeries independentCoefficient
]

{ #category : #accessing }
PowerSeriesRing >> maximalIdeal [
	self notYetImplemented
]

{ #category : #accessing }
PowerSeriesRing >> one [
	^ PowerSeries fromPolynomial: self scalars polynomials one
]

{ #category : #accessing }
PowerSeriesRing >> polynomials [
	^ polynomials
]

{ #category : #'accessing-private' }
PowerSeriesRing >> polynomials: aPolynomialRing [
"	aPolynomialRing isUnivariate ifFalse: [self error: 'multivariate power series not yet supported']."
	polynomials := aPolynomialRing ordering isLocal
		ifTrue: [aPolynomialRing]
		ifFalse: [aPolynomialRing orderedBy: #llex]
]

{ #category : #printing }
PowerSeriesRing >> printOn: aStream [
	aStream print: self scalars; nextPutAll: '[['.
	self polynomials printIndeterminatesOn: aStream.
	aStream nextPutAll: ']]'
]

{ #category : #accessing }
PowerSeriesRing >> scalars [
	^ self polynomials scalars
]

{ #category : #accessing }
PowerSeriesRing >> zero [
	^ self fromPolynomial: self polynomials zero
]
