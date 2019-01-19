"
K-rational points on a projective variety X, seen as morphisms Spec(K) -> X.

See also ProjectiveVariety.
"
Class {
	#name : #ProjectivePoint,
	#superclass : #RationalPoint,
	#instVars : [
		'coordinates'
	],
	#category : #'Mathematics-Schemes-Projective'
}

{ #category : #'instance creation' }
ProjectivePoint class >> on: aProjectiveVariety coordinates: aTuple [
	^ self new codomain: aProjectiveVariety; coordinates: aTuple
]

{ #category : #comparing }
ProjectivePoint >> = aProjectivePoint [
	self class = aProjectivePoint class ifFalse: [^ super = aProjectivePoint].
	coordinates size = aProjectivePoint coordinates size ifFalse: [^ false].
	^ self coordinates ~ aProjectivePoint coordinates
]

{ #category : #converting }
ProjectivePoint >> asTuple [
	^ coordinates
]

{ #category : #accessing }
ProjectivePoint >> coordinates [
	^ coordinates
]

{ #category : #'accessing-private' }
ProjectivePoint >> coordinates: aTuple [
	coordinates := aTuple
]

{ #category : #converting }
ProjectivePoint >> dehomogenized [
	"Answer the dehomogenization of the receiver."
	^ self dehomogenizedIn: self coordinates lastNonZero
]

{ #category : #converting }
ProjectivePoint >> dehomogenizedIn: anInteger [
	"Answer the dehomogenization of the receiver with respect to the anInteger-th coordinate."
	| scalar |
	scalar := coordinates at: anInteger.
	^ (self codomain patch: anInteger) pointAt:
		(self scalars
			tuple: coordinates size - 1
			evaluating: [:i| (i < anInteger ifTrue: [coordinates at: i] ifFalse: [coordinates at: i + 1]) / scalar])
]

{ #category : #comparing }
ProjectivePoint >> hash [
	self scalars isField ifTrue: [^ self hashField].
	self scalars isIntegralDomain ifTrue: [^ self hashIntegralDomain].
	^ self scalars hash "hashMultiply + self coordinates lastNonZeroDivisor"
]

{ #category : #comparing }
ProjectivePoint >> hashField [
	| hash x |
	hash := 0.
	x := coordinates at: coordinates lastNonZero.
	1 to: coordinates size do: [:i | hash := (hash + ((coordinates at: i) / x) hash) hashMultiply].
	^hash
]

{ #category : #comparing }
ProjectivePoint >> hashIntegralDomain [
	| Q hash x |
	Q := self scalars fractions.
	hash := 0.
	x := Q embed: (coordinates at: coordinates lastNonZero).
	1 to: coordinates size do: [:i | hash := (hash + ((Q embed: (coordinates at: i)) / x) hash) hashMultiply].
	^ hash
]

{ #category : #accessing }
ProjectivePoint >> ideal [
	"Answer the prime ideal defining the receiver."
	| R m am xm ai generators |
	self codomain scalars = self scalars ifFalse: [^ self notYetImplemented].
	R := self codomain ambient coordinateRing.
	generators := OrderedCollection new: coordinates size.
	m := coordinates lastNonZero.
	am := coordinates at: m.
	xm := R x: m.
	1 to: m do: [:i|
		ai := coordinates at: i.
		ai isZero ifTrue: [generators add: (R x: i)] ifFalse: [generators add: (R x: i) * am - (xm*ai)]].
	m+1 to: coordinates size do: [:i|
		generators add: (R x: i)].
	^ R * generators
]

{ #category : #testing }
ProjectivePoint >> isSmooth [
	^ (self codomain singular satisfies: self coordinates) not
	
"OR:
	^ self dehomogenized isSmooth
but dehomogenizing requires it be be over a field"

]

{ #category : #accessing }
ProjectivePoint >> localRing [
	"Answer the local ring at this point."
	^ self dehomogenized localRing
]

{ #category : #accessing }
ProjectivePoint >> multiplicity [
	^ self dehomogenized multiplicity "assuming none of the components of the projective variety lies on the hyperplane at infinity"
]

{ #category : #accessing }
ProjectivePoint >> neighborhood [
	"Answer an affine neighborhood centered at this point."
	^ self dehomogenized neighborhood
]

{ #category : #printing }
ProjectivePoint >> printInsidesOn: aStream [
	| separator |
	separator := (self coordinates anySatisfy: [:any| any printString isAlphaNumeric not]) ifTrue: [' : '] ifFalse: [':'].
	self coordinates do: [:each| aStream print: each] separatedBy: [aStream nextPutAll: separator].

]

{ #category : #printing }
ProjectivePoint >> printOn: aStream [
	aStream nextPut: $[.
	self printInsidesOn: aStream.
	aStream nextPut: $]
]

{ #category : #accessing }
ProjectivePoint >> scalars [
	^ coordinates scalars
]

{ #category : #accessing }
ProjectivePoint >> tangentCone [
	"Answer the projective tangent cone at this point."
	^ self dehomogenized tangentCone projectiveClosure "this projective closure uses the embedding corresponding to the same affine patch index that was used for dehomogenization"
]
