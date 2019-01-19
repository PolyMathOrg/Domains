Class {
	#name : #ProjectivePlane,
	#superclass : #ProjectiveSpace,
	#category : #'Mathematics-Schemes-Projective'
}

{ #category : #'instance creation' }
ProjectivePlane class >> over: aRing [
	^ self coordinateRing: (aRing polynomialsIn: #(x y z))
]

{ #category : #accessing }
ProjectivePlane >> order [
	self scalars isGaloisField ifTrue: [^ self scalars degree].
	^ self notYetImplemented
]
