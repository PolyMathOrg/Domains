"
This is the CEVAL algorithm [1] for isolating the complex roots of a square-free polynomial.

[1] Michael Sagraloff, Chee K. Yap, ""An Efficient and Exact Subdivision Algorithm for Isolating Complex Roots of a Polynomial and its Complexity Analysis"" (2009)
"
Class {
	#name : #ComplexRootIsolator,
	#superclass : #Object,
	#instVars : [
		'polynomial',
		'derivatives'
	],
	#category : #'Mathematics-Polynomials-Algorithms'
}

{ #category : #'instance creation' }
ComplexRootIsolator class >> on: aPolynomial [
	^ self new polynomial: aPolynomial
]

{ #category : #'as yet unclassified' }
ComplexRootIsolator >> T2: K at: m radius: r [
	| t |
	t := 0.
	1 to: self derivatives size - 1 do: [:j|
		| f |
		f := derivatives at: j+1.
		t := (f value: m) abs * (r raisedTo: j) / j factorial + t].
	^ (derivatives first value: m) abs > (K * t)
]

{ #category : #'as yet unclassified' }
ComplexRootIsolator >> T: K at: m radius: r [
	| t |
	t := 0.
	1 to: self derivatives size do: [:j|
		| f |
		f := derivatives at: j.
		t := (f value: m) abs * (r raiseTo: j) / j factorial + t].
	^ (polynomial value: m) abs > (K * t)
]

{ #category : #'as yet unclassified' }
ComplexRootIsolator >> atMostOneRootAround: center radius: radius [
	"If this holds, there's at most one root in the givem disk."
	^ self T2: 3/2 at: center radius: radius
"	^ (self rootsIn: aBox) size > 1"
]

{ #category : #'as yet unclassified' }
ComplexRootIsolator >> bigBounds [
	"Compute and answer a first estimate of a box containing all the complex roots."
	| bound |
	bound := self polynomial norm1 / self polynomial leadingCoefficient.
	bound := bound max: 1.
	^ ComplexBox center: 0.0 radius: bound asFloat
]

{ #category : #'as yet unclassified' }
ComplexRootIsolator >> derivatives [
	| f |
	derivatives ifNotNil: [^ derivatives].
	f := polynomial.
	derivatives := OrderedCollection new: f degree.
	f degree timesRepeat: [derivatives add: (f := f derivative)].
	^ derivatives
]

{ #category : #'as yet unclassified' }
ComplexRootIsolator >> eightPointTest: m width: w [
	| N NE E SE S SW W NW points values imaginaryCrossings realCrossings |
	N := 1 i.
	NE := 20/29 + (21/29) i.
	E := 1.
	SE := 20/29 - (21/29) i.
	S := -1 i.
	SW := -20/29 - (21/29) i.
	W := -1.
	NW := -20/29 + (21/29) i.
	points := {N. NE. E. SE. S. SW. W. NW} collect: [:p| w*p + m].
	values := points collect: [:p| polynomial value: p].
	realCrossings := (1 to: values size) select: [:j| (values at: j) real isZero or: [(values at: j) real * (values atWrap: j+1) real < 0]].
	realCrossings size = 2 ifFalse: [^ false].
	imaginaryCrossings := (1 to: values size) select: [:j| (values at: j) imaginary isZero or: [(values at: j) imaginary * (values atWrap: j+1) imaginary < 0]].
	imaginaryCrossings size = 2 ifFalse: [^ false].
	realCrossings first < imaginaryCrossings first
		ifTrue: [^ realCrossings second < imaginaryCrossings second].
	^ realCrossings first > imaginaryCrossings first
		and: [realCrossings second > imaginaryCrossings second]
]

{ #category : #'as yet unclassified' }
ComplexRootIsolator >> polynomial [
	^ polynomial
]

{ #category : #'as yet unclassified' }
ComplexRootIsolator >> polynomial: aPolynomial [
	polynomial := aPolynomial integerPrimitive
]

{ #category : #'as yet unclassified' }
ComplexRootIsolator >> roots [
	"Separate the roots in disks each of them containing one isolated root."
	^ self rootsInBox: self bigBounds
]

{ #category : #'as yet unclassified' }
ComplexRootIsolator >> rootsInBox: aBox [
	"Separate the roots in disks each of them containing one isolated root."
	| queue disks |
	queue := OrderedCollection with: aBox.
	disks := OrderedCollection new.
	[queue isEmpty]
		whileFalse:
			[| B m delta |
			B := queue removeFirst.
			m := B midpoint.
			delta := B width * 3 / 4. "> B radius, and a dyadic fraction"
			(self T: 1 at: m radius: delta)
				"if holds, then D(m,delta) constains no roots"
				ifFalse:
					[((self T2: 6 at: m radius: 4*delta) and: [self T2: 3/2 at: m radius: 8*delta])
						"if the second holds, then D(m,8*delta) contains at most one root"
						"the first is required so that if two disks overlap, we can discard any one of them"
						ifTrue:
							[(self eightPointTest: m width: B width)
								ifTrue:
									[| D i D2 |
									D := ComplexDisk center: m radius: 4*delta.
									(i := (1 to: disks size) detect: [:j| (D2 := disks at: j) intersects: D] ifNone: [])
									 isNil
										ifTrue: [disks add: D]
										ifFalse: [D2 radius < D radius ifTrue: [disks at: i put: D]]]]
						ifFalse:
							[queue addAll: B quarters]]].
	^ disks
]
