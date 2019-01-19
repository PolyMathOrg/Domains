"
Projective plane curves of genus 0 and degree 1. They are defined by linear polynomials.

Rational curves, together with Conics, are the only curves of genus 0.
"
Class {
	#name : #RationalCurve,
	#superclass : #ProjectivePlaneCurve,
	#category : #'Mathematics-Schemes-Projective'
}

{ #category : #'as yet unclassified' }
RationalCurve >> genus [
	"Answer the geometric genus of the receiver."
	^ 0
]

{ #category : #'as yet unclassified' }
RationalCurve >> pointsCountOver: aRing [
	"The number of Z/pZ-rational points of a curve of genus 0 is always p + 1."
	(aRing isKindOf: PrimeField) ifTrue: [^ aRing characteristic + 1].
	^ super pointsCountOver: aRing
]
