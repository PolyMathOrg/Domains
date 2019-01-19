Extension { #name : #Number }

{ #category : #'*mathematics' }
Number >> , anObject [
	^ (QQ tuple: {self}), anObject
]

{ #category : #'*mathematics' }
Number >> /// aNumber [
	^ self / aNumber
]

{ #category : #'*mathematics' }
Number >> adaptToQuaternion: rcvr andSend: selector [
	^ rcvr perform: selector with: self asQuaternion
]

{ #category : #'*mathematics' }
Number >> asQuaternion [
	^ Quaternion a: self b: self zero c: self zero d: self zero
]

{ #category : #'*mathematics' }
Number >> conjugated [
	"Answer the complex conjugate of the receiver."

	^ self
]

{ #category : #'*mathematics' }
Number >> imaginary [
	^ 0
]

{ #category : #'*mathematics' }
Number >> isAlgebraic [
	^ false
]

{ #category : #'*mathematics' }
Number >> isComplex [
	^ true "real numbers are also complex numbers"
]

{ #category : #'*mathematics' }
Number >> isRational [
	^ false
]

{ #category : #'*mathematics' }
Number >> isReal [
	^ true
]

{ #category : #'*mathematics' }
Number >> norm [
	^ self abs
]

{ #category : #'*mathematics' }
Number >> norm2 [
	^ self squared
]

{ #category : #'*mathematics' }
Number >> one [
	^ 1
]

{ #category : #'*mathematics' }
Number >> parent [
	^ RR
]

{ #category : #'*mathematics' }
Number >> real [
	^ self
]

{ #category : #'*mathematics' }
Number >> root: anInteger [
	anInteger = 2 ifTrue: [^ self squareRoot].
	anInteger = 1 ifTrue: [^ self].
	^ self notYetImplemented
]

{ #category : #'*mathematics' }
Number >> zero [
	^ 0
]
