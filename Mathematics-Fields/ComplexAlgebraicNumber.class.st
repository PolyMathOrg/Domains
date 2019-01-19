"
Complex algebraic numbers, i.e. zeros of polynomials with integer (or rational) coefficients, in 'minimal polynomial' representation. See also RealAlgebraicNumber.
"
Class {
	#name : #ComplexAlgebraicNumber,
	#superclass : #Object,
	#instVars : [
		'minimalPolynomial',
		'approximation',
		'radius'
	],
	#category : #'Mathematics-Fields'
}

{ #category : #'instance creation' }
ComplexAlgebraicNumber class >> approximation: approximateValue radius: approximationError maxDegree: n [
	"Answer an algebraic number with the given approximate value, approximation error, with minimal polynomial of degree at most n."
	^ self notYetImplemented
]

{ #category : #'instance creation' }
ComplexAlgebraicNumber class >> fromRational: anIntegerOrFraction [
	"Answer an instance of the receiver representing the rational number anIntegerOrFraction."
	| q x |
	q := anIntegerOrFraction asFraction.
	x := QQ polynomials x.
	^ self
		minimalPolynomial: x * q denominator - q numerator
 		approximation: anIntegerOrFraction
		radius: 0
]

{ #category : #examples }
ComplexAlgebraicNumber class >> i [
	| x |
	x := QQ polynomials x.
	^ self minimalPolynomial: (x raiseTo:2) + 1 approximation: 1 i radius: 0
]

{ #category : #'instance creation' }
ComplexAlgebraicNumber class >> minimalPolynomial: aPolynomial approximation: aComplex radius: aNumber [
	^ self new
		minimalPolynomial: aPolynomial;
		approximation: aComplex radius: aNumber
]

{ #category : #examples }
ComplexAlgebraicNumber class >> phi [
	"Answer the Phidias number or Golden Ratio."
	| x |
	x := QQ polynomials x.
	^ self minimalPolynomial: x raiseTo: 2 - x - 1 approximation: 2.0 radius: 1
]

{ #category : #'instance creation' }
ComplexAlgebraicNumber class >> polynomial: aPolynomial approximation: aComplex radius: aNumber [
	| minimalPolynomial |
	minimalPolynomial := aPolynomial factors argmin: [:f| (f value: aComplex) abs].
	minimalPolynomial degree = 1 ifTrue: [^ minimalPolynomial independentCoefficient negated / minimalPolynomial leadingCoefficient].
	^ self minimalPolynomial: minimalPolynomial approximation: aComplex radius: aNumber
]

{ #category : #examples }
ComplexAlgebraicNumber class >> sqrt2 [
	"Answer an instance of the receiver representing the square root of 2."

	^ self
		minimalPolynomial: QQ polynomials x squared - 2
 		approximation: 1.5
		radius: 0.1
]

{ #category : #examples }
ComplexAlgebraicNumber class >> sqrt: anIntegerOrFraction [
	"Answer a square root of the rational argument."
	^ self
		minimalPolynomial: QQ polynomials x squared - anIntegerOrFraction
 		approximation: (anIntegerOrFraction negative ifTrue: [anIntegerOrFraction negated sqrt i] ifFalse: [anIntegerOrFraction sqrt]) radius: 0.00001
]

{ #category : #arithmetic }
ComplexAlgebraicNumber >> * aNumber [
	| isolator x r |
	aNumber class = self class
		ifFalse: [^ aNumber adaptToAlgebraic: self andSend: #*].
	aNumber isZero ifTrue: [^ aNumber].
	self isZero ifTrue: [^ self].
	isolator := ComplexRootIsolator on: (minimalPolynomial zeroProduct: aNumber minimalPolynomial) squareFree.
	[x := approximation * aNumber approximation.
	r := self absoluteError * aNumber approximation norm2 + (approximation norm2 * aNumber absoluteError).
	isolator atMostOneRootAround: x radius: r]
		whileFalse:
			[self refineWith: aNumber].
	^ self class polynomial: isolator polynomial approximation: x radius: r
]

{ #category : #arithmetic }
ComplexAlgebraicNumber >> + aNumber [
	| isolator x r |
	aNumber class = self class
		ifFalse: [^ aNumber adaptToAlgebraic: self andSend: #+].
	aNumber isZero ifTrue: [^ self].
	self isZero ifTrue: [^ aNumber].
	isolator := ComplexRootIsolator on: (minimalPolynomial zeroAddition: aNumber minimalPolynomial) squareFree.
	[x := approximation + aNumber approximation.
	r := self absoluteError + aNumber absoluteError.
	isolator atMostOneRootAround: x radius: r]
		whileFalse:
			[self refineWith: aNumber].
	^ self class polynomial: isolator polynomial approximation: x radius: r
]

{ #category : #arithmetic }
ComplexAlgebraicNumber >> - anObject [
	^ self + anObject negated
]

{ #category : #arithmetic }
ComplexAlgebraicNumber >> / anObject [
	^ self * anObject reciprocal
]

{ #category : #comparing }
ComplexAlgebraicNumber >> = anObject [
	self == anObject ifTrue: [^ true].
	anObject isNumber ifFalse: [^ false].
	anObject class = self class
		ifFalse: [^ anObject adaptToAlgebraic: self andSend: #=].
	^ minimalPolynomial = anObject minimalPolynomial and: [self bounds intersects: anObject bounds]
]

{ #category : #approximating }
ComplexAlgebraicNumber >> absoluteError [
	^ radius
]

{ #category : #converting }
ComplexAlgebraicNumber >> adaptToFloat: rcvr andSend: selector [
	^ rcvr perform: selector with: self asFloat
]

{ #category : #converting }
ComplexAlgebraicNumber >> adaptToFraction: rcvr andSend: selector [
	^ (self class fromRational: rcvr) perform: selector with: self
]

{ #category : #converting }
ComplexAlgebraicNumber >> adaptToInteger: rcvr andSend: selector [
	^ (self class fromRational: rcvr) perform: selector with: self
]

{ #category : #approximating }
ComplexAlgebraicNumber >> approximation [
	"Answre a rational or float current approximation of the receiver."
	^ approximation
]

{ #category : #'accessing-private' }
ComplexAlgebraicNumber >> approximation: aNumber radius: anotherNumber [
	approximation := aNumber.
	radius := anotherNumber
]

{ #category : #converting }
ComplexAlgebraicNumber >> asComplexFloat [
	"Answer a Float approximation of the receiver."
	self refineTo: 0.000001.
	^ approximation asFloat
]

{ #category : #converting }
ComplexAlgebraicNumber >> asFloat [
	"Answer a Float approximation of the receiver."
	self refineTo: 0.000001.
	^ self approximation asFloat
]

{ #category : #converting }
ComplexAlgebraicNumber >> asRational [
	"Convert the receiver to Fraction or Integer."
	| alpha |
	radius = 0 ifTrue: [^ approximation]. "could be float!"
	minimalPolynomial degree < 2
		ifTrue:
			[alpha := minimalPolynomial independentCoefficient negated / minimalPolynomial leadingCoefficient.
			approximation := alpha. radius := 0.
			^ alpha].
	(minimalPolynomial rootsIn: QQ)
		do: [:each|
			(each - approximation) abs < radius
				ifTrue: [approximation := each. radius := 0. ^ each]].
	self error: 'the number is irrational'
]

{ #category : #approximating }
ComplexAlgebraicNumber >> bounds [
	"Answer a disk in the complex plane where the receiver is located, isolated from all other roots of its minimal polynomial."
	^ ComplexDisk center: approximation radius: radius
]

{ #category : #accessing }
ComplexAlgebraicNumber >> conjugates [
	"The conjugates of an algebraic number with minimal polynomial of degree n are all its n-th roots."
	^ (minimalPolynomial rootsIn: CC) "copyWithout: self"
]

{ #category : #accessing }
ComplexAlgebraicNumber >> degree [
	^ minimalPolynomial degree
]

{ #category : #accessing }
ComplexAlgebraicNumber >> denominator [
	"The denominator of an algebraic number is the smallest positive integer that multiplied by the algebraic number is an algebraic integer."
	^ minimalPolynomial coefficients inject: 1 into: [:result :each| result lcm: each denominator]
]

{ #category : #comparing }
ComplexAlgebraicNumber >> hash [
	^ minimalPolynomial hash
]

{ #category : #accessing }
ComplexAlgebraicNumber >> height [
	^ self minimalPolynomial height
]

{ #category : #arithmetic }
ComplexAlgebraicNumber >> i [
	^ self * self class i
]

{ #category : #testing }
ComplexAlgebraicNumber >> isAlgebraic [
	^ true
]

{ #category : #testing }
ComplexAlgebraicNumber >> isAlgebraicInteger [
	"An algebraic number is an 'algebraic integer' if it's the root of a monic polynomial in Z[x], in particular if it's minimal polynomial has integer coefficients."
	^ minimalPolynomial isMonic "<- defining the minimal polynomial as integer primitive"

"alternatively, defining the minimal polynomial as monic:
	^ minimalPolynomial coefficients allSatisfy: [:each| each isInteger]
"
]

{ #category : #testing }
ComplexAlgebraicNumber >> isImaginary [
	^ approximation real abs < radius
]

{ #category : #testing }
ComplexAlgebraicNumber >> isNumber [
	^ true
]

{ #category : #testing }
ComplexAlgebraicNumber >> isRational [
	minimalPolynomial degree < 2 ifTrue: [^ true].
	radius = 0 ifTrue: [^ true].
	(minimalPolynomial rootsIn: QQ)
		do: [:each|
			(each - approximation) abs < radius
				ifTrue: [approximation := each. radius := 0. ^ true]].
	^ false
]

{ #category : #testing }
ComplexAlgebraicNumber >> isReal [
	^ approximation imaginary abs < radius "and: [((RealRootIsolator on: minimalPolynomial) numberOfRootsBetween: approximation real - radius and: approximation real + radius) > 0]"
]

{ #category : #testing }
ComplexAlgebraicNumber >> isZero [
	^ approximation abs < radius and: [(minimalPolynomial value: 0) = 0]
]

{ #category : #accessing }
ComplexAlgebraicNumber >> minimalPolynomial [
	^ minimalPolynomial
]

{ #category : #'accessing-private' }
ComplexAlgebraicNumber >> minimalPolynomial: aPolynomial [
	minimalPolynomial := aPolynomial integerPrimitive "<- or should it be monic?"
]

{ #category : #arithmetic }
ComplexAlgebraicNumber >> negated [
	"Answer the additive inverse of the receiver."
	^ self class
		minimalPolynomial: minimalPolynomial zeroNegation
		approximation: approximation negated
		radius: radius
]

{ #category : #operations }
ComplexAlgebraicNumber >> norm [
	^ minimalPolynomial independentCoefficient / minimalPolynomial leadingCoefficient * (minimalPolynomial degree even ifTrue: [1] ifFalse: [-1])

"alternatively:
	^ self conjugates product"
]

{ #category : #constants }
ComplexAlgebraicNumber >> one [
	^ 1
]

{ #category : #printing }
ComplexAlgebraicNumber >> printOn: aStream [
	self printOn: aStream base: 10
]

{ #category : #printing }
ComplexAlgebraicNumber >> printOn: aStream base: base [
	| real imaginary isImaginary |
	minimalPolynomial degree = 2 ifTrue: [^ self printQuadraticOn: aStream base: base].
	self refineTo: self printPrecision.
	real := approximation real asFloat roundTo: self printPrecision.
	imaginary := approximation imaginary asFloat roundTo: self printPrecision.
	(isImaginary := self isImaginary)
		ifFalse: [real printOn: aStream base: base].
	self isReal
		ifFalse:
			[isImaginary ifFalse: [aStream nextPutAll: (0 <= imaginary ifTrue: [' + '] ifFalse: [imaginary := imaginary negated. ' - '])].
			imaginary printOn: aStream base: base.
			aStream nextPutAll: 'i' italic].
	aStream nextPutAll: '..'
]

{ #category : #printing }
ComplexAlgebraicNumber >> printPrecision [
"	self absoluteError < 1 ifTrue: [^ self absoluteError asFloat].
	^ 0.001"
	^ 0.00001
]

{ #category : #printing }
ComplexAlgebraicNumber >> printQuadraticOn: aStream base: base [
	| a b c discriminant z y x1 x2 sign |
	a := minimalPolynomial atDegree: 2.
	b := minimalPolynomial atDegree: 1.
	c := minimalPolynomial atDegree: 0.
	discriminant := b squared - (4*a*c).
	z := discriminant squareFree.
	y := (discriminant / z) sqrt.
	x1 := b negated + (discriminant negative ifTrue: [discriminant negated sqrt i] ifFalse: [discriminant sqrt]) / (2*a).
	x2 := b negated - (discriminant negative ifTrue: [discriminant negated sqrt i] ifFalse: [discriminant sqrt]) / (2*a).
	(x1 - approximation) abs <= radius
		ifTrue: [sign := ' + ']
		ifFalse: [(x2 - approximation) abs <= radius ifTrue: [sign := ' - '. y := y negated] ifFalse: [self halt]].
	b = 0 ifFalse:
		[b/(-2*a) printOn: aStream base: base.
		aStream nextPutAll: sign.
		y := y abs].
	y negative ifTrue: [aStream nextPut: $-. y := y abs].
	y/(2*a) = 1 ifFalse: [y/(2*a) printOn: aStream base: base].
	z abs = 1 ifFalse:
		[aStream nextPut: $ó.
		z abs printOn: aStream base: base].
	z negative ifTrue: [aStream nextPutAll: 'i' italic]
]

{ #category : #arithmetic }
ComplexAlgebraicNumber >> reciprocal [
	"Answer the multiplicative inverse of the receiver."
	| isolator x r |
	self isZero ifTrue: [^ ZeroDivide signal].
	isolator := ComplexRootIsolator on: minimalPolynomial zeroReciprocal.
	[x := approximation reciprocal.
	r := self absoluteError / approximation norm2 * x norm2.
	isolator atMostOneRootAround: x radius: r]
		whileFalse:
			[self refine].
	^ self class minimalPolynomial: isolator polynomial approximation: x radius: r
]

{ #category : #approximating }
ComplexAlgebraicNumber >> refine [
	| P Q P2 Q2 m x v c dx y v1 m1 |
	radius := radius / 2.0.
	P := minimalPolynomial. "should it be monic?"
	Q := P.
	P2 := P derivative.
	Q2 := P2.
	x := approximation.
	v := Q value: x.
	m := v norm2.
	c := 0. dx := v / (Q2 value: x).
	[dx abs >= radius]
		whileTrue:
			[y := x - dx.
			v1 := Q value: y.
			m1 := v1 norm2.
			m1 < m
				ifTrue: [x := y. v := v1. m := m1. c := 0. dx := v / (Q2 value: x)]
				ifFalse: [c := c + 1. dx := dx / 4. c > 20 ifTrue: [self error: 'failed']]].
	"Polish root:"
	2 timesRepeat: [x := x - ((P value: x) / (P2 value: x))].
	approximation := x
]

{ #category : #approximating }
ComplexAlgebraicNumber >> refineTo: aNumber [
	"Refine the receiver up to get an approximation error < aNumber."
	[self absoluteError > aNumber] whileTrue: [self refine]
]

{ #category : #approximating }
ComplexAlgebraicNumber >> refineWith: aComplexAlgebraicNumber [
	"Refine the rational interval approximation of either the receiver or the argument, depending on which is less precise at the moment."
	self relativeError > aComplexAlgebraicNumber relativeError
		ifTrue: [self refine]
		ifFalse: [aComplexAlgebraicNumber refine]
]

{ #category : #approximating }
ComplexAlgebraicNumber >> relativeError [
	"Answer the relative error in the current rational approximation."
	self isZero ifTrue: [^ 0].
	^ self absoluteError / self approximation abs
]

{ #category : #arithmetic }
ComplexAlgebraicNumber >> squareRoot [
	| isolator x r |
	self isZero ifTrue: [^ self].
	isolator := ComplexRootIsolator on: minimalPolynomial zeroSquareRoot squareFree.
	[x := approximation sqrt.
	r := self absoluteError sqrt.
	isolator atMostOneRootAround: x radius: r]
		whileFalse:
			[self refine].
	^ self class polynomial: isolator polynomial approximation: x radius: r
]

{ #category : #arithmetic }
ComplexAlgebraicNumber >> squared [
	| x odd even |
	x := minimalPolynomial parent x.
	odd := minimalPolynomial odd.
	even := minimalPolynomial even.
	^ self class
		polynomial: odd squared * x - even squared
		approximation: approximation squared
		radius: radius * approximation norm2 * 2
]

{ #category : #operations }
ComplexAlgebraicNumber >> trace [
	"Answer the absolute trace of the receiver."
	^ (minimalPolynomial atDegree: minimalPolynomial degree - 1) negated

"alternatively:
	^ self conjugates sum"
]

{ #category : #constants }
ComplexAlgebraicNumber >> zero [
	^ 0
]
