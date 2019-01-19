"
K-rational points on an affine variety X, seen as morphisms Spec(K) -> X.

See also AffineVariety.
"
Class {
	#name : #AffinePoint,
	#superclass : #RationalPoint,
	#instVars : [
		'coordinates'
	],
	#category : #'Mathematics-Schemes-Affine'
}

{ #category : #'instance creation' }
AffinePoint class >> on: anAffineVariety coordinates: aTuple [
	^ self new codomain: anAffineVariety; coordinates: aTuple
]

{ #category : #arithmetic }
AffinePoint >> + aTuple [
	"Answer the result of translating the receiver by a vector."
	^ self shallowCopy coordinates: self coordinates + aTuple
"	^ self shallowCopy coordinates: self coordinates + ((self codomain asLinearSpace over: self scalars) coordinatesOf: aVector)"
]

{ #category : #arithmetic }
AffinePoint >> - anAffinePoint [
	"The difference between two affine points is a vector (a tuple)."
	^ self coordinates - anAffinePoint coordinates
]

{ #category : #comparing }
AffinePoint >> = anAffinePoint [
	^ self coordinates = anAffinePoint coordinates
]

{ #category : #converting }
AffinePoint >> asRingHomomorphism [
	^ self codomain coordinateRing to: self domain coordinateRing evaluating: [:f| f value: self coordinates]
]

{ #category : #converting }
AffinePoint >> asTuple [
	^ coordinates
]

{ #category : #accessing }
AffinePoint >> coordinates [
	^ coordinates
]

{ #category : #'accessing-private' }
AffinePoint >> coordinates: aTuple [
	coordinates := aTuple
]

{ #category : #comparing }
AffinePoint >> hash [
	^ self coordinates hash
]

{ #category : #accessing }
AffinePoint >> height [
	^ coordinates height
]

{ #category : #converting }
AffinePoint >> homogenized [
	"Answer the corresponding point in the projective closure."
	^ self codomain projectiveEmbedding value: self
]

{ #category : #accessing }
AffinePoint >> ideal [
	"Answer the prime ideal defining the receiver."
	| R |
	self codomain scalars = self scalars ifFalse: [^ self notYetImplemented].
	R := self codomain ambient coordinateRing.
	^ R * (R generators - self coordinates)
]

{ #category : #testing }
AffinePoint >> isSmooth [
	^ (self codomain singular satisfies: self coordinates) not
]

{ #category : #accessing }
AffinePoint >> localRing [
	"Answer the local ring at this point."
	^ self neighborhood coordinateRing localization
]

{ #category : #accessing }
AffinePoint >> multiplicity [
	^ self codomain multiplicityAt: coordinates
	"^ self localRing multiplicity"
]

{ #category : #accessing }
AffinePoint >> neighborhood [
	"Answer a neighborhood centered at the receiver."
	^ self codomain - coordinates
]

{ #category : #printing }
AffinePoint >> printOn: aStream [
	aStream print: self coordinates
]

{ #category : #accessing }
AffinePoint >> scalars [
	^ coordinates scalars
]

{ #category : #accessing }
AffinePoint >> tangentCone [
	"Answer the affine tangent cone at this point."
	^ self codomain tangentConeAt: coordinates
]

{ #category : #accessing }
AffinePoint >> tangentSpace [
	"Answer the affine tangent space at this point."
	^ self codomain tangentSpaceAt: coordinates
]
