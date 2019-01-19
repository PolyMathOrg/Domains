"
Real algebraic numbers, i.e. real zeros of polynomials with integer (or rational) coefficients, in 'minimal polynomial' representation. See also ComplexAlgebraicNumber.
"
Class {
	#name : #RealAlgebraicNumber,
	#superclass : #Number,
	#instVars : [
		'minimalPolynomial',
		'bounds',
		'rightSign'
	],
	#category : #'Mathematics-Fields'
}

{ #category : #'instance creation' }
RealAlgebraicNumber class >> fromRational: anIntegerOrFraction [
	"Answer an instance of the receiver representing the rational number anIntegerOrFraction."
	| q x |
	q := anIntegerOrFraction asFraction.
	x := QQ polynomials x.
	^ self
		minimalPolynomial: x * q denominator - q numerator
 		bounds: (RealInterval open: anIntegerOrFraction closed: anIntegerOrFraction)
]

{ #category : #'instance creation' }
RealAlgebraicNumber class >> minimalPolynomial: aPolynomial bounds: aRealInterval [
	"Answer an instance of the receiver representing the unique zero of aPolynomial in the given rational interval."
	^ self new minimalPolynomial: aPolynomial bounds: aRealInterval
]

{ #category : #examples }
RealAlgebraicNumber class >> phi [
	"Answer the Phidias number or Golden Ratio."
	| x |
	x := QQ polynomials x.
	^ self minimalPolynomial: (x raisedTo: 2) - x - 1 bounds: (RealInterval open: 1.0 open: 2.0)
]

{ #category : #'instance creation' }
RealAlgebraicNumber class >> polynomial: aPolynomial bounds: aRealInterval [
	"Answer an instance of the receiver representing the unique zero of aPolynomial in the given interval."
	| approximation |
	approximation := aRealInterval midpoint.
	^ self minimalPolynomial: (aPolynomial factors argmin: [:f| (f value: approximation) abs]) bounds: aRealInterval
]

{ #category : #examples }
RealAlgebraicNumber class >> sqrt2 [
	"Answer an instance of the receiver representing the square root of 2."
	^ self
		minimalPolynomial: QQ polynomials x squared - 2
 		bounds: (RealInterval open: 1.0 open: 2.0)
]

{ #category : #examples }
RealAlgebraicNumber class >> sqrt: aNumber [
	"Answer a square root of the rational argument."
	aNumber positive ifFalse: [^ DomainError signal: 'negative square root'].
	^ self
		minimalPolynomial: QQ polynomials x squared - aNumber
 		bounds: (RealInterval open: 0.0 open: (aNumber max: 1.0))
]

{ #category : #arithmetic }
RealAlgebraicNumber >> * aNumber [
	| f b |
	aNumber class = self class
		ifFalse: [^ aNumber adaptToRealAlgebraic: self andSend: #*].
	aNumber isZero ifTrue: [^ aNumber].
	self isZero ifTrue: [^ self].
	f := RealRootIsolator on:
		(minimalPolynomial zeroProduct: aNumber minimalPolynomial) squareFree.
	[b := self bounds * aNumber bounds.
	f moreThanOneRootBetween: b left and: b right]
		whileTrue:
			[self refineWith: aNumber].
	^ self class polynomial: f polynomial bounds: b
]

{ #category : #arithmetic }
RealAlgebraicNumber >> + aNumber [
	| f b |
	aNumber class = self class
		ifFalse: [^ aNumber adaptToRealAlgebraic: self andSend: #+].
	aNumber isZero ifTrue: [^ self].
	self isZero ifTrue: [^ aNumber].
	f := RealRootIsolator on:
		(minimalPolynomial zeroAddition: aNumber minimalPolynomial) squareFree.
	[b := self bounds + aNumber bounds.
	f moreThanOneRootBetween: b left and: b right]
		whileTrue:
			[self refineWith: aNumber].
	^ self class polynomial: f polynomial bounds: b
]

{ #category : #arithmetic }
RealAlgebraicNumber >> - anObject [
	^ self + anObject negated
]

{ #category : #arithmetic }
RealAlgebraicNumber >> / anObject [
	^ self * anObject reciprocal
]

{ #category : #comparing }
RealAlgebraicNumber >> < anObject [
	"Answer whether the receiver is less than the argument."

	anObject class = self class ifFalse: [^ (self - anObject) sign = -1].
	(self = anObject) ifTrue: [^ false].
	[self bounds intersects: anObject bounds] whileTrue: [self refineWith: anObject].
	^ self rightBound < anObject leftBound
]

{ #category : #comparing }
RealAlgebraicNumber >> = anObject [
	anObject isNumber ifFalse: [^ false].
	self == anObject ifTrue: [^ true].
	anObject class = self class
		ifFalse: [^ anObject adaptToRealAlgebraic: self andSend: #=].
	^ minimalPolynomial = anObject minimalPolynomial and: [bounds intersects: anObject bounds]
]

{ #category : #approximating }
RealAlgebraicNumber >> absoluteError [
	"Answer the maximun current error in the rational approximation of the receiver."
	^ bounds length / 2
]

{ #category : #converting }
RealAlgebraicNumber >> adaptToAlgebraic: rcvr andSend: selector [
	^ rcvr perform: selector with: (ComplexAlgebraicNumber polynomial: minimalPolynomial approximation: bounds midpoint radius: bounds length / 2)
]

{ #category : #converting }
RealAlgebraicNumber >> adaptToFloat: rcvr andSend: selector [
	^ rcvr perform: selector with: self asFloat
]

{ #category : #converting }
RealAlgebraicNumber >> adaptToFraction: rcvr andSend: selector [
	^ (self class fromRational: rcvr) perform: selector with: self
]

{ #category : #converting }
RealAlgebraicNumber >> adaptToInteger: rcvr andSend: selector [
	^ (self class fromRational: rcvr) perform: selector with: self
]

{ #category : #approximating }
RealAlgebraicNumber >> approximation [
	"Answer the current rational approximation of the receiver."
	^ bounds midpoint
]

{ #category : #converting }
RealAlgebraicNumber >> asFloat [
	"Answer a Float approximation of the receiver."

	self refineTo: 0.000001.
	^ self approximation asFloat
]

{ #category : #converting }
RealAlgebraicNumber >> asRational [
	"Convert the receiver to Fraction or Integer."
	| alpha |
	self leftBound = self rightBound ifTrue: [^ self leftBound].
	minimalPolynomial degree < 2
		ifTrue:
			[alpha := minimalPolynomial independentCoefficient negated / minimalPolynomial leadingCoefficient.
			self bounds: (RealInterval open: alpha closed: alpha).
			^ alpha].
	(minimalPolynomial rootsIn: QQ)
		do: [:each|
			(each between: self leftBound and: self rightBound)
				ifTrue: [self bounds: (RealInterval open: each closed: each). ^ each]].
	self error: 'the number is irrational'
]

{ #category : #approximating }
RealAlgebraicNumber >> bounds [
	^ bounds
]

{ #category : #'accessing-private' }
RealAlgebraicNumber >> bounds: aRealInterval [
	bounds := aRealInterval.
	rightSign := nil
]

{ #category : #accessing }
RealAlgebraicNumber >> denominator [
	"The denominator of an algebraic number is the smallest positive integer that multiplied by the algebraic number is an algebraic integer."
	^ minimalPolynomial coefficients inject: 1 into: [:result :each| result lcm: each denominator]
]

{ #category : #comparing }
RealAlgebraicNumber >> hash [
	"Answer the hash value for the receiver."

	^ self truncated hash
]

{ #category : #testing }
RealAlgebraicNumber >> isAlgebraic [
	^ true
]

{ #category : #testing }
RealAlgebraicNumber >> isAlgebraicInteger [
	"An algebraic number is an 'algebraic integer' if it's the root of a monic polynomial in Z[x], in particular if it's minimal polynomial has integer coefficients."
	^ self minimalPolynomial coefficients allSatisfy: [:each| each isInteger]
]

{ #category : #testing }
RealAlgebraicNumber >> isRational [
	"Answer true if the receiver is a rational number."
	minimalPolynomial degree < 2 ifTrue: [^ true].
	self rightBound = self leftBound ifTrue: [^ true].
	(minimalPolynomial rootsIn: QQ)
		do: [:each|
			(self bounds includes: each)
				ifTrue: [self bounds: (RealInterval closed: each closed: each). ^ true]].
	^ false
]

{ #category : #testing }
RealAlgebraicNumber >> isZero [
	^ self leftBound = 0 and: [self rightBound = 0]
"	^ self isRational and: [self asRational = 0]"
]

{ #category : #'accessing-private' }
RealAlgebraicNumber >> leftBound [
	^ bounds left
]

{ #category : #'accessing-private' }
RealAlgebraicNumber >> leftBound: aFraction [
	bounds := RealInterval open: aFraction closed: bounds right
]

{ #category : #accessing }
RealAlgebraicNumber >> minimalPolynomial [
	^ minimalPolynomial
]

{ #category : #initialization }
RealAlgebraicNumber >> minimalPolynomial: aPolynomial bounds: aRealInterval [
	minimalPolynomial := aPolynomial monic.
	bounds := aRealInterval.
	self normalize.
	self reduce
]

{ #category : #arithmetic }
RealAlgebraicNumber >> negated [
	"Answer the additive inverse of the receiver."
	self isZero ifTrue: [^ self].
	^ self class
		minimalPolynomial: minimalPolynomial zeroNegation
		bounds: bounds negated
]

{ #category : #private }
RealAlgebraicNumber >> normalize [
	"Change the representation of the receiver such that if the receiver is not 0 then 0 is not in the rational approximation interval."
	| p sign |
	self leftBound sign = self rightBound sign ifTrue: [^ self].
	minimalPolynomial independentCoefficient isZero
		ifTrue: [^ self leftBound: 0; rightBound: 0].
	"for every real root r not 0: |r| > 1 / (1 + f normInfinite), from Cauchy and Landau inequalities"
	p := 1 / (1 + minimalPolynomial normInfinite).
	p negated < self leftBound
		ifTrue: [^ self leftBound: p].
	p > self rightBound
		ifTrue: [^ self rightBound: p negated].
	sign := (minimalPolynomial value: p negated) sign.
	sign ~= (minimalPolynomial value: self leftBound) sign
		ifTrue: [self rightBound: p negated; rightSign: sign]
		ifFalse: [(minimalPolynomial value: p) sign ~= self rightSign
				ifTrue: [self leftBound: p]
				ifFalse: [self leftBound: 0; rightBound: 0]].
	self leftBound > self rightBound ifTrue: [self error: 'interval normalization error']
]

{ #category : #printing }
RealAlgebraicNumber >> printOn: aStream base: base [
	minimalPolynomial degree < 4 "too slow" ifTrue: [self isRational ifTrue: [self asRational printOn: aStream base: base. ^ self]].
"	polynomial degree = 2 ifTrue: [^ self printQuadraticOn: aStream base: base]."
	(self asFloat roundTo: 0.00001) printOn: aStream base: base.
	aStream nextPutAll: '..'

	"aStream
		nextPutAll: self class name;
		space;
		nextPut: $(;
		print: self polynomial;
		nextPutAll: '; ~ ';
		print: self asFloat;
		nextPut: $)"
]

{ #category : #arithmetic }
RealAlgebraicNumber >> reciprocal [
	"Answer the multiplicative inverse of the receiver."
	self isZero ifTrue: [^ ZeroDivide signal].
	^ self class
		minimalPolynomial: minimalPolynomial zeroReciprocal
		bounds: bounds reciprocal
]

{ #category : #approximating }
RealAlgebraicNumber >> refine [
	"Refine the rational interval approximation of the receiver."
	self refineAt: self approximation
]

{ #category : #approximating }
RealAlgebraicNumber >> refineAt: aFraction [
	"Refine the rational interval approximation of the receiver to one of both (leftBound, aFraction] or (aFraction, rightBound]."
	| sign |
	self rightSign = (sign := (minimalPolynomial value: aFraction) sign)
		ifTrue: [self rightBound: aFraction; rightSign: sign]
		ifFalse: [self leftBound: aFraction].
	sign = 0 ifTrue: [self leftBound: aFraction. self rightBound: aFraction]
]

{ #category : #approximating }
RealAlgebraicNumber >> refineTo: aNumber [
	"Refine the receiver up to get an approximation error < aNumber."
	[self absoluteError >= aNumber] whileTrue: [self refine]
]

{ #category : #approximating }
RealAlgebraicNumber >> refineWith: aRealAlgebraicNumber [
	"Refine the rational interval approximation of either the receiver or the argument, depending on which is less precise at the moment."
	self relativeError > aRealAlgebraicNumber relativeError
		ifTrue: [self refine]
		ifFalse: [aRealAlgebraicNumber refine]
]

{ #category : #approximating }
RealAlgebraicNumber >> relativeError [
	"Answer the relative error in the current rational approximation."
	self isZero ifTrue: [^ 0].
	^ self absoluteError / self approximation abs
]

{ #category : #'accessing-private' }
RealAlgebraicNumber >> rightBound [
	^ bounds right
]

{ #category : #'accessing-private' }
RealAlgebraicNumber >> rightBound: aFraction [
	bounds := RealInterval open: bounds left closed: aFraction.
	rightSign := nil
]

{ #category : #'accessing-private' }
RealAlgebraicNumber >> rightSign [
	rightSign isNil ifTrue: [rightSign := (minimalPolynomial value: self rightBound) sign].
	^ rightSign
]

{ #category : #'accessing-private' }
RealAlgebraicNumber >> rightSign: anInteger [
	rightSign := anInteger
]

{ #category : #'mathematical functions' }
RealAlgebraicNumber >> sign [
	"Answer 1, -1 or 0, depending on the sign of the receiver."

	^ self leftBound sign
]

{ #category : #'mathematical functions' }
RealAlgebraicNumber >> squareRoot [
	self isRational ifFalse: [^ self notYetImplemented].
	self negative ifTrue: [^ self negated squareRoot i].
	self isZero ifTrue: [^ self].
	^ self class
		polynomial: minimalPolynomial zeroSquareRoot "is it minimal?"
 		bounds: (RealInterval open: 0 open: (self asRational max: 1))
]

{ #category : #'mathematical functions' }
RealAlgebraicNumber >> squared [
	| x odd even |
	x := minimalPolynomial parent x.
	odd := minimalPolynomial odd.
	even := minimalPolynomial even.
	self flag: #fix.
	^ self class "this could be rational"
		polynomial: odd squared * x - even squared
		bounds: self bounds squared
]

{ #category : #'truncation and round off' }
RealAlgebraicNumber >> truncated [
	"Answer the integer nearest the receiver toward zero."
	| t |
	self absoluteError truncated > 0 ifTrue: [self refineTo: 9/10].
	^ (t := self rightBound truncated) = self rightBound
		ifTrue: [self refineAt: t.
				self rightBound truncated]
		ifFalse: [t]
]
