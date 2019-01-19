"
Projective lines are P^1(R) for some commutative ring R. They are essentially the underlying ring R extended with an additional point at infinity. For example, the complex projective line is the Riemann sphere: the extended complex plane that includes the point at infinity. See also ProjectiveLinePoint.
"
Class {
	#name : #ProjectiveLine,
	#superclass : #ProjectiveSpace,
	#category : #'Mathematics-Schemes-Projective'
}

{ #category : #'instance creation' }
ProjectiveLine class >> over: aRing [
	^ self coordinateRing: (aRing polynomialsIn: #(x y))
]

{ #category : #elements }
ProjectiveLine >> ! anObject [
	(self scalars includes: anObject) ifTrue: [^ self embed: anObject].
	^ super ! anObject
]

{ #category : #morphisms }
ProjectiveLine >> embed: anElement [
	^ self pointAt: (self scalars tuple: {anElement. self scalars one})
]

{ #category : #morphisms }
ProjectiveLine >> embedding [
	^ Function from: self scalars to: self evaluating: [:each| self embed: each]
]

{ #category : #morphisms }
ProjectiveLine >> from: aDomain [
	aDomain = self scalars ifTrue: [^ self embedding].
	'aDomain  self scalars ifNotNil: [:aMorphism| ^ self embedding î aMorphism]'.
	^ super from: aDomain
]

{ #category : #accessing }
ProjectiveLine >> infinity [
	| R |
	R := self scalars.
	^ self pointAt: (R tuple: {R one. R zero})
]

{ #category : #accessing }
ProjectiveLine >> one [
	| R |
	R := self scalars.
	^ self pointAt: (R tuple: {R one. R one})
]

{ #category : #points }
ProjectiveLine >> pointAt: aTuple [
	^ ProjectiveLinePoint on: self coordinates: aTuple
]

{ #category : #accessing }
ProjectiveLine >> zero [
	| R |
	R := self scalars.
	^ self pointAt: (R tuple: {R zero. R one})
]
