Class {
	#name : #RealRootIsolator,
	#superclass : #Object,
	#instVars : [
		'polynomial',
		'sturm',
		'fourier',
		'roots'
	],
	#category : #'Mathematics-Polynomials-Algorithms'
}

{ #category : #'instance creation' }
RealRootIsolator class >> on: aPolynomial [
	^ self new polynomial: aPolynomial
]

{ #category : #private }
RealRootIsolator >> bigBounds [
	"Compute and answer a first estimate of an interval containing all the real roots."
	| bound |
	bound := polynomial norm1 / polynomial leadingCoefficient asFloat.
	bound := bound max: 1.0.
	^ RealInterval closed: bound negated closed: bound
]

{ #category : #private }
RealRootIsolator >> computeFourier [
	"Compute the Budan-Fourier sequence for the polynomial of the receiver."
	| f |
	f := polynomial.
	fourier := (OrderedCollection new: f degree + 1) add: f; yourself.
	f degree timesRepeat: [fourier add: (f := f derivative)]
]

{ #category : #private }
RealRootIsolator >> computeSturm [
	"Compute a sturmian sequence for the receiver."
	| f g r |
	f := polynomial.
	g := f derivative.
	sturm := (OrderedCollection new: f degree + 1) add: f; add: g; yourself.
	[g degree > 0]
		whileTrue:
			[r := sturm add: (f \\ g) negated.
			f := g.
			g := r]
]

{ #category : #accessing }
RealRootIsolator >> fourier [
	"Answer the Budan-Fourier sequence for the polynomial of the receiver."

	fourier isNil ifTrue: [self computeFourier].
	^ fourier
]

{ #category : #private }
RealRootIsolator >> heuristicDetectOneRootBetween: leftBound and: rightBound [
	| first |
	first := polynomial value: leftBound.
	2 to: 10 do: [:each|
		first ~= (polynomial value: (rightBound - leftBound) / each) sign
			ifTrue: [^ true]].
	^ false
]

{ #category : #'couting roots' }
RealRootIsolator >> lowerBoundNumberOfRootsBetween: leftBound and: rightBound [
	"Answer a lower bound for the number of real roots in the open interval (leftBound, rightBound)."
	| answer last sign |
	answer := 0.
	last := 0.
	1 to: polynomial degree * 2 do: [:each|
		sign := (polynomial value: (rightBound - leftBound) / each) sign.
		(last ~= sign and: [sign ~= 0]) ifTrue: [answer := answer + 1].
		last := sign].
	^ answer
]

{ #category : #'couting roots' }
RealRootIsolator >> moreThanOneRootBetween: leftBound and: rightBound [
	"Answer true if there are only one root in the interval (leftBound, rightBound]."

	| upper lower |
	sturm isNil "if the Sturm chain was not yet computed, first try some bounds and heuristics"
		ifTrue:
			[(upper := self upperBoundNumberOfRootsBetween: leftBound and: rightBound) < 2
				ifTrue: [^ false].
			(upper even and: [self heuristicDetectOneRootBetween: leftBound and: rightBound])
				ifTrue: [^ true].
			lower := self lowerBoundNumberOfRootsBetween: leftBound and: rightBound.
			lower > 1 ifTrue: [^ true].
			(upper even and: [lower > 0]) ifTrue: [^ true]].

	^ (self numberOfRootsBetween: leftBound and: rightBound) > 1
]

{ #category : #'couting roots' }
RealRootIsolator >> numberOfNegativeRoots [
	"Answer the number of negative roots."
	| fix |
	fix := (polynomial value: 0) = 0 ifTrue: [1] ifFalse: [0].
	^ (self numberOfRootsBetween: self bigBounds min and: 0) - fix
]

{ #category : #'couting roots' }
RealRootIsolator >> numberOfPositiveRoots [
	"Answer the number of positive roots."
	^ self numberOfRootsBetween: 0 and: self bigBounds max
]

{ #category : #'couting roots' }
RealRootIsolator >> numberOfRoots [
	"Answer the number of real roots of the receiver."

	| interval |
	interval := self bigBounds.
	^ self numberOfRootsBetween: interval min and: interval max
]

{ #category : #'couting roots' }
RealRootIsolator >> numberOfRootsBetween: leftBound and: rightBound [
	"Answer the number of real roots in the left open interval (leftBound, rightBound]."

	| leftSignChanges rightSignChanges a b |
	a := leftBound asFraction.
	b := rightBound asFraction.
	leftSignChanges := 0.
	(self sturm collect: [ :each | (each value: a) sign])
		inject: 0 into: [ :lastSign :each |
			(lastSign ~= each and: [each ~= 0])
				ifTrue: [leftSignChanges := leftSignChanges + 1].
			each].

	rightSignChanges := 0.
	(self sturm collect: [ :each | (each value: b) sign])
		inject: 0 into: [ :lastSign :each |
			(lastSign ~= each and: [each ~= 0])
				ifTrue: [rightSignChanges := rightSignChanges + 1].
			each].

	^ leftSignChanges - rightSignChanges
]

{ #category : #accessing }
RealRootIsolator >> polynomial [
	^ polynomial
]

{ #category : #initialization }
RealRootIsolator >> polynomial: aPolynomial [
	polynomial := aPolynomial
]

{ #category : #accessing }
RealRootIsolator >> roots [
	"Answer a collection with the roots of the polynomial."
	roots isNil ifTrue: [self separateRoots].
	^ roots
]

{ #category : #operations }
RealRootIsolator >> separateRoots [
	"Separate the roots in intervals each of them including an isolated root."

	| bounds |
	roots := SortedCollection sortBlock: [ :one :other | one left <= other left].
	bounds := self bigBounds.
	self separateRootsBetween: bounds min and: bounds max
]

{ #category : #operations }
RealRootIsolator >> separateRootsBetween: leftBound and: rightBound [
	"Separate the roots in the real interval given by the arguments."
	| r mid |
	r := self numberOfRootsBetween: leftBound and: rightBound.
	r = 0 ifTrue: [^ self].
	r = 1 ifTrue: [^ roots add: (RealInterval closed: leftBound closed: rightBound)].

	mid := leftBound + rightBound / 2.0. "2 for exact rationals or 2.0 to use floats."
	self separateRootsBetween: leftBound and: mid.
	self separateRootsBetween: mid and: rightBound
]

{ #category : #accessing }
RealRootIsolator >> sturm [
	"Answer a sturm sequence for the polynomial of the receiver."

	sturm isNil ifTrue: [self computeSturm].
	^ sturm
]

{ #category : #'couting roots' }
RealRootIsolator >> upperBoundNumberOfRoots [
	"Answer an upper bound for the number of real roots of the receiver."
	| interval |
	interval := self bigBounds.
	^ self upperBoundNumberOfRootsBetween: interval min and: interval max
]

{ #category : #'couting roots' }
RealRootIsolator >> upperBoundNumberOfRootsBetween: leftBound and: rightBound [
	"Answer an upper bound for the number of real roots
	in the open interval (leftBound, rightBound)."

	| leftSignChanges rightSignChanges |

	leftSignChanges := 0.
	(self fourier collect: [ :each | (each value: leftBound) sign])
		inject: 0 into: [ :lastSign :each |
			(lastSign ~= each and: [each ~= 0])
				ifTrue: [leftSignChanges := leftSignChanges + 1].
			each].

	rightSignChanges := 0.
	(self fourier collect: [ :each | (each value: rightBound) sign])
		inject: 0 into: [ :lastSign :each |
			(lastSign ~= each and: [each ~= 0])
				ifTrue: [rightSignChanges := rightSignChanges + 1].
			each].

	^ leftSignChanges - rightSignChanges
]
