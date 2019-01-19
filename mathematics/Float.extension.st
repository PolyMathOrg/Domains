Extension { #name : #Float }

{ #category : #'*mathematics' }
Float >> adaptToAlgebraic: rcvr andSend: selector [
	^ rcvr asComplexFloat perform: selector with: self asComplex
]

{ #category : #'*mathematics' }
Float >> adaptToRealAlgebraic: rcvr andSend: selector [
	^ rcvr asFloat perform: selector with: self
]

{ #category : #'*mathematics' }
Float >> squareRoot [
	^ self sqrt
]
