"
Transformations of the form
	z |-> az + b / (cz + d)
where ad - cb ~= 0.
"
Class {
	#name : #LinearFractionalMap,
	#superclass : #RationalMap,
	#instVars : [
		'a',
		'b',
		'c',
		'd'
	],
	#category : #'Mathematics-Modular Forms'
}

{ #category : #'instance creation' }
LinearFractionalMap class >> I [
	^ self a: 1 b: 0 c: 0 d: 1
]

{ #category : #'instance creation' }
LinearFractionalMap class >> R [
	^ self a: 0 b: 1 c: -1 d: 1
]

{ #category : #'instance creation' }
LinearFractionalMap class >> S [
	^ self a: 0 b: -1 c: 1 d: 0
]

{ #category : #'instance creation' }
LinearFractionalMap class >> T [
	^ self a: 1 b: 1 c: 0 d: 1
]

{ #category : #'instance creation' }
LinearFractionalMap class >> a: a b: b c: c d: d [
	^ self new a: a; b: b; c: c; d: d
]

{ #category : #'instance creation' }
LinearFractionalMap class >> matrix: aMatrix [
	^ self a: (aMatrix at: 1@1) b: (aMatrix at: 1@2) c: (aMatrix at: 2@1) d: (aMatrix at: 2@2)
]

{ #category : #comparing }
LinearFractionalMap >> = aMoebiusMap [
	aMoebiusMap species = self species ifFalse: [^ super = aMoebiusMap].
	^ a = aMoebiusMap a and: [b = aMoebiusMap b and: [c = aMoebiusMap c and: [d = aMoebiusMap d]]]
]

{ #category : #accessing }
LinearFractionalMap >> a [
	^ a
]

{ #category : #'accessing-private' }
LinearFractionalMap >> a: aNumber [
	a := aNumber
]

{ #category : #converting }
LinearFractionalMap >> asMatrix [
	^ self domain scalars matrix: 2 coefficients: {a. b. c. d}
]

{ #category : #converting }
LinearFractionalMap >> asRationalFunction [
	| z |
	z := (self domain scalars polynomialsIn: #(z)) fractions x.
	^ z * a + b / (z * c + d)
]

{ #category : #accessing }
LinearFractionalMap >> b [
	^ b
]

{ #category : #'accessing-private' }
LinearFractionalMap >> b: aNumber [
	b := aNumber
]

{ #category : #accessing }
LinearFractionalMap >> c [
	^ c
]

{ #category : #'accessing-private' }
LinearFractionalMap >> c: aNumber [
	c := aNumber
]

{ #category : #accessing }
LinearFractionalMap >> codomain [
	^ CC
]

{ #category : #accessing }
LinearFractionalMap >> d [
	^ d
]

{ #category : #'accessing-private' }
LinearFractionalMap >> d: aNumber [
	d := aNumber
]

{ #category : #accessing }
LinearFractionalMap >> domain [
	^ CC
]

{ #category : #comparing }
LinearFractionalMap >> hash [
	^ ((a hash + b hash) hashMultiply + c hash) hashMultiply + d hash
]

{ #category : #accessing }
LinearFractionalMap >> identity [
	^ self class I
]

{ #category : #operations }
LinearFractionalMap >> inverse [
	^ self class a: d b: b negated c: c negated d: a
]

{ #category : #testing }
LinearFractionalMap >> isCircular [
	^ self trace = 0
]

{ #category : #testing }
LinearFractionalMap >> isElliptic [
	^ self traceSquared < 4
]

{ #category : #testing }
LinearFractionalMap >> isHyperbolic [
	^ self traceSquared > 4
]

{ #category : #testing }
LinearFractionalMap >> isIdentity [
	^ a = 1 and: [b = 0 and: [c = 0 and: [d = 1]]]
]

{ #category : #testing }
LinearFractionalMap >> isLoxodromic [
	| t |
	^ (t := self traceSquared) < 0 or: [t > 4]
]

{ #category : #testing }
LinearFractionalMap >> isParabolic [
	^ self traceSquared = 4
]

{ #category : #printing }
LinearFractionalMap >> printOn: aStream [
	| z denominator numerator |
	z := (CC polynomialsIn: #(z)) x.
	c isZero ifTrue: [aStream print: z * a + b / d. ^ self].
	numerator := z * a + b.
	(a = 0 or: [b = 0])
		ifTrue: [aStream print: numerator]
		ifFalse: [aStream nextPut: $(; print: numerator; nextPut: $)].
	aStream nextPut: $/.
	denominator := z * c + d.
	(c = 0 or: [d = 0])
		ifTrue: [aStream print: denominator]
		ifFalse: [aStream nextPut: $(; print: denominator; nextPut: $)]
]

{ #category : #operations }
LinearFractionalMap >> quotequote: aModularMap [ "î"
	^ self class
		a: a * aModularMap a + (b * aModularMap c)
		b: a * aModularMap b + (b * aModularMap d)
		c: c * aModularMap a + (d * aModularMap c)
		d: c * aModularMap b + (d * aModularMap d)
]

{ #category : #operations }
LinearFractionalMap >> trace [
	^ a + d
]

{ #category : #operations }
LinearFractionalMap >> traceSquared [
	^ (a + d) squared
]

{ #category : #operations }
LinearFractionalMap >> value: anObject [
	^ anObject * a + b / (anObject * c + d)
]
