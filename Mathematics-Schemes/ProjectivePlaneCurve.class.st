"
Projective plane algebraic curves, i.e. schemes of dimension 1 over a projective plane.
"
Class {
	#name : #ProjectivePlaneCurve,
	#superclass : #ProjectiveHypersurface,
	#category : #'Mathematics-Schemes-Projective'
}

{ #category : #accessing }
ProjectivePlaneCurve >> arithmeticGenus [
	| n |
	self isIrreducible ifFalse: [^ self notYetImplemented].
	n := self polynomial degree.
	^ n - 1 * (n - 2) / 2
]

{ #category : #operations }
ProjectivePlaneCurve >> flexes [
	"This is the subscheme of flexes of the receiver.
	In classic algebraic geometry, a point in a nonsingular plane curve over the complex numbers is a 'flex' if its tangent line has contact of order >= 3 with the curve."
	^ self ï self hessian
]

{ #category : #operations }
ProjectivePlaneCurve >> hessian [
	"Answer the Hessian curve associated to the receiver.
	Over an algebraically closed field, the intersection of a plane curve and its Hessian is the subvariety of flexes."
	^ self ambient subscheme: self polynomial hessian determinant
]

{ #category : #printing }
ProjectivePlaneCurve >> printOn: aStream [
	aStream print: self polynomial; nextPutAll: ' = 0'
]
