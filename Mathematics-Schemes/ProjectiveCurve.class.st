"
Projective algebraic curves, i.e. projective schemes of dimension 1 over a projective space.
"
Class {
	#name : #ProjectiveCurve,
	#superclass : #ProjectiveVariety,
	#category : #'Mathematics-Schemes-Projective'
}

{ #category : #accessing }
ProjectiveCurve >> arithmeticGenus [
	self isIrreducible ifFalse: [^ self error: 'not irreducible'].
	^ 1 - (self ideal hilbertPolynomial value: 0)
]

{ #category : #accessing }
ProjectiveCurve >> dimension [
	^ 1
]

{ #category : #'as yet unclassified' }
ProjectiveCurve >> divisorOf: aRationalFunction [
	"Answer div(f), the divisor with coefficient ord(f,p) for each point p of its support, where ord(f,p) is the order of a point p as zero or pole of the rational function f."
	self notYetImplemented
]
