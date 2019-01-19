"
Abelian groups E(K) consisting of the K-rational points of an elliptic curve E.
"
Class {
	#name : #EllipticCurveGroup,
	#superclass : #AbelianGroup,
	#instVars : [
		'curve',
		'scalars'
	],
	#category : #'Mathematics-Elliptic Curves'
}

{ #category : #'instance creation' }
EllipticCurveGroup class >> on: anEllipticCurve over: aField [
	^ self new curve: anEllipticCurve; scalars: aField
]

{ #category : #random }
EllipticCurveGroup >> atRandom: aRandom [
	^ curve pointAtRandom: aRandom
]

{ #category : #accessing }
EllipticCurveGroup >> curve [
	^ curve
]

{ #category : #'accessing-private' }
EllipticCurveGroup >> curve: anEllipticCurve [
	curve := anEllipticCurve
]

{ #category : #enumerating }
EllipticCurveGroup >> do: aBlock [
	self curve pointsOver: self scalars do: aBlock
]

{ #category : #accessing }
EllipticCurveGroup >> identity [
	"This is the point at infinity."
	^ curve pointAt: (scalars tuple: {scalars zero. scalars one. scalars zero})
]

{ #category : #printing }
EllipticCurveGroup >> printOn: aStream [
	aStream nextPutAll: 'E('; print: self scalars; nextPut: $)
]

{ #category : #accessing }
EllipticCurveGroup >> scalars [
	^ scalars
]

{ #category : #'accessing-private' }
EllipticCurveGroup >> scalars: aField [
	scalars := aField
]

{ #category : #accessing }
EllipticCurveGroup >> torsion [
	"Answer the torsion subgroup of the receiver."
	"Henri Cohen, 'A Course in Computational Algebraic Number Theory', Algorithm 7.5.5."
"	| E b2 b4 b6 b8 discriminant |
	E := self curve equation.
	b2 := E b2.
	b4 := E b4.
	b6 := E b6.
	b8 := E b8.
	discriminant := E discriminant.
	points add: self identity.
	..."
	self notYetImplemented
]
