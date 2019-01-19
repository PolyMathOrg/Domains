"
Abstract superclass for K-rational points on a scheme X, seen as morphisms Spec(K) -> X.

See also Scheme and PointSet.
"
Class {
	#name : #RationalPoint,
	#superclass : #Morphism,
	#instVars : [
		'codomain'
	],
	#category : #'Mathematics-Schemes'
}

{ #category : #accessing }
RationalPoint >> ambient [
	^ self codomain ambient
]

{ #category : #accessing }
RationalPoint >> codomain [
	^ codomain
]

{ #category : #'accessing-private' }
RationalPoint >> codomain: aScheme [
	codomain := aScheme
]

{ #category : #accessing }
RationalPoint >> domain [
	^ self scalars spec
]

{ #category : #testing }
RationalPoint >> isAffine [
	^ self codomain isAffine
]

{ #category : #testing }
RationalPoint >> isFlex [
	^ self multiplicity >= 3
]

{ #category : #testing }
RationalPoint >> isProjective [
	^ self codomain isProjective
]

{ #category : #testing }
RationalPoint >> isSingular [
	^ self isSmooth not
]

{ #category : #accessing }
RationalPoint >> scalars [
	^ self domain coordinateRing
]
