"
A projective schemes is the projective (or homogeneous) spectrum Proj(R) of a graded commutative ring R, equipped with a sheaf of local rings (which makes it a locally ringed space). As a set, their elements are the relevant prime ideals of the associated homogeneous coordinate ring R.

Proj(R) is contained in its affine cone Spec(R).
"
Class {
	#name : #ProjectiveScheme,
	#superclass : #Scheme,
	#category : #'Mathematics-Schemes'
}

{ #category : #'as yet unclassified' }
ProjectiveScheme >> do: aBlock [
	self coordinateRing relevantPrimeIdealsDo: aBlock
]
