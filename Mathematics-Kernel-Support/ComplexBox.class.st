"
Boxes in the complex plane, defined by two real intervals (for the real and imaginary parts).
"
Class {
	#name : #ComplexBox,
	#superclass : #Domain,
	#instVars : [
		'real',
		'imaginary'
	],
	#category : #'Mathematics-Kernel-Support'
}

{ #category : #'instance creation' }
ComplexBox class >> center: aComplex radius: aNumber [
	^ self
		real: (RealInterval closed: aComplex real - aNumber closed: aComplex real + aNumber)
		imaginary: (RealInterval closed: aComplex imaginary - aNumber closed: aComplex imaginary + aNumber)
]

{ #category : #'instance creation' }
ComplexBox class >> real: aRealInterval imaginary: anotherRealInterval [
	^ self new real: aRealInterval; imaginary: anotherRealInterval
]

{ #category : #'instance creation' }
ComplexBox class >> with: aComplex with: anotherComplex [
	^ self
		real: (RealInterval with: aComplex real with: anotherComplex real)
		imaginary: (RealInterval with: aComplex imaginary with: anotherComplex imaginary)
]

{ #category : #accessing }
ComplexBox >> area [
	^ self measure
]

{ #category : #accessing }
ComplexBox >> closure [
	^ self class real: real closure imaginary: imaginary closure
]

{ #category : #testing }
ComplexBox >> closureIncludes: aComplex [
	^ (real closureIncludes: aComplex real) and: [imaginary closureIncludes: aComplex imaginary]
]

{ #category : #accessing }
ComplexBox >> imaginary [
	^ imaginary
]

{ #category : #'accessing-private' }
ComplexBox >> imaginary: aRealInterval [
	imaginary := aRealInterval
]

{ #category : #testing }
ComplexBox >> includes: aComplex [
	^ (real includes: aComplex real) and: [imaginary includes: aComplex imaginary]
]

{ #category : #testing }
ComplexBox >> intersects: aComplexBox [
	^ (real intersects: aComplexBox real) and: [imaginary intersects: aComplexBox imaginary]
]

{ #category : #testing }
ComplexBox >> isBounded [
	^ real isBounded and: [imaginary isBounded]
]

{ #category : #testing }
ComplexBox >> isClosed [
	^ real isClosed and: [imaginary isClosed]
]

{ #category : #testing }
ComplexBox >> isOpen [
	^ real isOpen and: [imaginary isOpen]
]

{ #category : #accessing }
ComplexBox >> measure [
	^ real measure * imaginary measure
]

{ #category : #accessing }
ComplexBox >> midpoint [
	^ Complex real: real midpoint imaginary: imaginary midpoint
]

{ #category : #printing }
ComplexBox >> printOn: aStream [
	aStream print: real; nextPutAll: ' + '; print: imaginary; nextPut: $i
]

{ #category : #accessing }
ComplexBox >> quarters [
	| imaginaries reals |
	reals := self real halves.
	imaginaries := self imaginary halves.
	^ {self class real: (reals at: 1) imaginary: (imaginaries at: 1).
		self class real: (reals at: 1) imaginary: (imaginaries at: 2).
		self class real: (reals at: 2) imaginary: (imaginaries at: 1).
		self class real: (reals at: 2) imaginary: (imaginaries at: 2)}
]

{ #category : #accessing }
ComplexBox >> radius2 [
	^ real length squared + imaginary length squared / 4
]

{ #category : #accessing }
ComplexBox >> real [
	^ real
]

{ #category : #'accessing-private' }
ComplexBox >> real: aRealInterval [
	real := aRealInterval
]

{ #category : #accessing }
ComplexBox >> sample [
	"Answer a sample point in the receiver."
	| sampleImaginary sampleReal |
	sampleReal := real sample.
	sampleImaginary := imaginary sample.
	^ CC tuple: sampleReal size evaluating: [:i| Complex real: (sampleReal at: i) imaginary: (sampleImaginary at: i)]
]

{ #category : #accessing }
ComplexBox >> width [
	^ real length min: imaginary length
]
