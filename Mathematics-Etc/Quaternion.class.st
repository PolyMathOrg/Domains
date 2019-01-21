"
My instances are quaternions. Quaternions constitute an example of non-commutative field.

"
Class {
	#name : #Quaternion,
	#superclass : #Object,
	#instVars : [
		'a',
		'b',
		'c',
		'd'
	],
	#category : #'Mathematics-Etc'
}

{ #category : #'instance creation' }
Quaternion class >> a: aNumber b: bNumber c: cNumber d: dNumber [
	"Answer a new instance of the receiver with the given components."

	^ self new a: aNumber b: bNumber c: cNumber d: dNumber
]

{ #category : #examples }
Quaternion class >> i [
	^ Quaternion a: 0 b: 1 c: 0 d: 0
]

{ #category : #examples }
Quaternion class >> j [
	^ Quaternion a: 0 b: 0 c: 1 d: 0
]

{ #category : #examples }
Quaternion class >> k [
	^ Quaternion a: 0 b: 0 c: 0 d: 1
]

{ #category : #arithmetic }
Quaternion >> * anObject [
	| a0 a1 a2 a3 b0 b1 b2 b3 |
	(anObject isKindOf: Number)
		ifTrue: [^ self class a: a * anObject b: b * anObject c: c * anObject d: d * anObject].
	(anObject isKindOf: Quaternion)
		ifFalse: [^ anObject adaptToQuaternion: self andSend: #*].
	a0 := self a. a1 := self b. a2 := self c. a3 := self d.
	b0 := anObject a. b1 := anObject b. b2 := anObject c. b3 := anObject d.
	^ self class
		a: a0 * b0 - (a1 * b1) - (a2 * b2) - (a3 * b3)
		b: a0 * b1 + (a1 * b0) + (a2 * b3) - (a3 * b2)
		c: a0 * b2 + (a2 * b0) + (a3 * b1) - (a1 * b3)
		d: a0 * b3 + (a3 * b0) + (a1 * b2) - (a2 * b1)
]

{ #category : #arithmetic }
Quaternion >> + anObject [
	(anObject isKindOf: Number)
		ifTrue: [^ self class a: a + anObject b: b c: c d: d].
	(anObject isKindOf: Quaternion)
		ifFalse: [^ anObject adaptToQuaternion: self andSend: #+].
	^ self class
		a: self a + anObject a
		b: self b + anObject b
		c: self c + anObject c
		d: self d + anObject d
]

{ #category : #arithmetic }
Quaternion >> - anObject [
	^ self + anObject negated
]

{ #category : #arithmetic }
Quaternion >> / anObject [
	^ self * anObject reciprocal
]

{ #category : #comparing }
Quaternion >> = anObject [
	anObject isNumber ifFalse: [^ false].
	(anObject isKindOf: Number)
		ifTrue: [^ a = anObject and: [b = 0 and: [c = 0 and: [d = 0]]]].
	(anObject isKindOf: Quaternion)
		ifFalse: [^ anObject adaptToQuaternion: self andSend: #=].
	^ self a = anObject a
		and: [self b = anObject b
			and: [self c = anObject c
				and: [self d = anObject d]]]
]

{ #category : #accessing }
Quaternion >> a [
	"Answer the 'a' component of the receiver."

	^ a
]

{ #category : #'accessing-private' }
Quaternion >> a: aNumber b: bNumber c: cNumber d: dNumber [
	a := aNumber.
	b := bNumber.
	c := cNumber.
	d := dNumber
]

{ #category : #converting }
Quaternion >> adaptToNumber: rcvr andSend: selector [
	"If I am involved in arithmetic with a Number, convert it to a Quaternion."
	^ (Quaternion a: rcvr b: 0 c: 0 d: 0) perform: selector with: self
]

{ #category : #converting }
Quaternion >> asQuaternion [
	^ self
]

{ #category : #accessing }
Quaternion >> b [
	"Answer the 'b' component of the receiver."

	^ b
]

{ #category : #accessing }
Quaternion >> c [
	"Answer the 'c' component of the receiver."

	^ c
]

{ #category : #arithmetic }
Quaternion >> conjugated [
	"Answer the conjugate of the receiver."

	^ self class
		a: self a
		b: self b negated
		c: self c negated
		d: self d negated
]

{ #category : #accessing }
Quaternion >> d [
	"Answer the 'd' component of the receiver."

	^ d
]

{ #category : #comparing }
Quaternion >> hash [
	^ ((a hash hashMultiply + b hash) hashMultiply + c hash) hashMultiply + d hash
]

{ #category : #arithmetic }
Quaternion >> i [
	"Answer the receiver multiplicated by i."

	^ self class a: self b negated b: self a c: self d d: self c negated
]

{ #category : #testing }
Quaternion >> isNumber [
	^ true
]

{ #category : #testing }
Quaternion >> isZero [
	"Answer true if the receiver is null."
	^ self a isZero and: [self b isZero and: [self c isZero and: [self d isZero]]]
]

{ #category : #arithmetic }
Quaternion >> j [
	"Answer the receiver multiplicated by j."

	^ self class a: self c negated b: self d negated c: self a d: self b
]

{ #category : #arithmetic }
Quaternion >> k [
	"Answer the receiver multiplicated by k."

	^ self class a: self d negated b: self c c: self b negated d: self a
]

{ #category : #arithmetic }
Quaternion >> negated [
	"Answer the additive inverse of the receiver."

	^ self class
		a: self a negated
		b: self b negated
		c: self c negated
		d: self d negated
]

{ #category : #'mathematical functions' }
Quaternion >> norm2 [
	"Answer the square norm of the receiver."

	^ self a squared + self b squared + self c squared + self d squared
]

{ #category : #constants }
Quaternion >> one [
	| zero |
	zero := a zero.
	^ self class a: a one b: zero c: zero d: zero
]

{ #category : #printing }
Quaternion >> printOn: aStream [
	"Print a representation of the receiver on the stream aStream."

	| something number |
	self isZero ifTrue: [aStream print: 0. ^ self].
	something := false.
	a isZero ifFalse: [aStream print: a. something := true].
	b isZero ifFalse: [number := b.
						something
							ifTrue: [aStream nextPutAll: (number positive
								ifTrue: [' + ']
								ifFalse: [number := number negated. ' - '])]
							ifFalse: [number negative
								ifTrue: [aStream nextPut: $-.
										number := number negated]].
						number = number one ifFalse: [aStream print: number; space].
						aStream nextPut: $i. something := true].
	c isZero ifFalse: [number := c.
						something
							ifTrue: [aStream nextPutAll: (number positive
								ifTrue: [' + ']
								ifFalse: [number := number negated. ' - '])]
							ifFalse: [number negative
								ifTrue: [aStream nextPut: $-.
										number := number negated]].
						number = number one ifFalse: [aStream print: number; space].
						aStream nextPut: $j. something := true].
	d isZero ifFalse: [number := d.
						something
							ifTrue: [aStream nextPutAll: (number positive
								ifTrue: [' + ']
								ifFalse: [number := number negated. ' - '])]
							ifFalse: [number negative
								ifTrue: [aStream nextPut: $-.
										number := number negated]].
						number = number one ifFalse: [aStream print: number; space].
						aStream nextPut: $k. something := true]
]

{ #category : #arithmetic }
Quaternion >> raisedTo: anInteger [
	"Answer the receiver raised to the power anInteger."

	anInteger = 1
		ifTrue: [ ^ self ].
	anInteger = 0
		ifTrue: [ ^ self one ].
	anInteger < 0
		ifTrue: [ ^ '(self ^ anInteger negated) reciprocal' ].
	^ (self squared raisedTo: anInteger // 2)
		* (self raisedTo: anInteger \\ 2)
]

{ #category : #arithmetic }
Quaternion >> reciprocal [
	"Answer the multiplicative inverse of the receiver."

	^ self conjugated / self norm2
]

{ #category : #'mathematical functions' }
Quaternion >> squared [
	^ self * self
]

{ #category : #constants }
Quaternion >> zero [
	| zero |
	zero := a zero.
	^ self class a: zero one b: zero c: zero d: zero
]
