Extension { #name : #Object }

{ #category : #'*mathematics' }
Object >> adaptToCollection: rcvr andSend: selector [
	"If I am involved in arithmetic with a Collection, return a Collection of
	the results of each element combined with me in that expression."

	^ rcvr collect: [:element | element perform: selector with: self]
]

{ #category : #'*mathematics' }
Object >> isEvaluable [
	^ self isBlock
]

{ #category : #'*mathematics' }
Object >> isFractional [
	"Answer true if this is an element of a localization, i.e. if it is some kind of fraction and understands #numerator and #denominator."
	^ false
]

{ #category : #'*mathematics' }
Object >> isInfinity [
	^ false
]

{ #category : #'*mathematics' }
Object >> isMatrix [
	^ false
]

{ #category : #'*mathematics' }
Object >> isReal [
	"Answer true if the receiver is a real number."
	^ false
]

{ #category : #'*mathematics' }
Object >> isSequenceable [
	"Answer true if the receiver is some sort of ordered tuple of objects, understands #at: and #size and it's indexed by integers starting at 1."
	^ false
]

{ #category : #'*mathematics' }
Object >> isTuple [
	^ false
]
