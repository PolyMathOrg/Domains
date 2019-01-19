"
This is the upper half complex plane H, i.e. the set of complex numbers with imaginary part > 0.

This serves as a model of the hyperbolic plane, defining lines as:
1. the intersection of the half-plane H and Euclidean lines orthogonal to the real axis, or
2. the intersection of the half-plane H and Euclidean half-circles with center on the real axis.

The group of hyperbolic isometries, as well as conformal automorphisms, is the general Moebius group. This is the group of Moebius transformations, i.e. transformations of the form z |-> (az + b) / (cz + d) with ad - cd ~= 0 (or without loss of generality ad - cd = 1).
"
Class {
	#name : #UpperHalfPlane,
	#superclass : #Domain,
	#category : #'Mathematics-Modular Forms'
}

{ #category : #initialization }
UpperHalfPlane class >> initialize [
	super initialize.
	Smalltalk at: #HH put: self new
]

{ #category : #testing }
UpperHalfPlane >> includes: anObject [
	^ anObject isComplex and: [anObject imaginary > 0]
]

{ #category : #printing }
UpperHalfPlane >> printOn: aStream [
	aStream nextPut: Character HH
]
