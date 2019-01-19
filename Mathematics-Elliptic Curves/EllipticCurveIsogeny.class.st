"
Scheme morphisms of elliptic curves E -> E' that send the origin of E to the origin of E'. They are homomorphisms of group schemes.
"
Class {
	#name : #EllipticCurveIsogeny,
	#superclass : #RationalMap,
	#category : #'Mathematics-Elliptic Curves'
}

{ #category : #'as yet unclassified' }
EllipticCurveIsogeny >> dual [
	"Answer the dual of the receiver. If the receiver is f:E->E' of degree n, its dual is an isogeny g:E'->E such that the compositions are [n] (multiplication by n)."
	^ self notYetImplemented
]

{ #category : #'as yet unclassified' }
EllipticCurveIsogeny >> isSurjective [
	^ self isZero not
]

{ #category : #'as yet unclassified' }
EllipticCurveIsogeny >> isZero [
	^ self degree = 0
]

{ #category : #'as yet unclassified' }
EllipticCurveIsogeny >> kernelPolynomial [
	^ self propertyAt: #kernelPolynomial ifAbsentPut: [self computeKernelPolynomial]
]
