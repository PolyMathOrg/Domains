"
Cartesian products of projective spaces.

Example:
	ProductProjectiveSpace new: #((x y z) (a b)) over: QQ.

"
Class {
	#name : #ProductProjectiveSpace,
	#superclass : #ProductProjectiveVariety,
	#category : #'Mathematics-Schemes-Projective-Product'
}

{ #category : #'instance creation' }
ProductProjectiveSpace class >> components: anArray [
	^ self new components: anArray
]

{ #category : #'instance creation' }
ProductProjectiveSpace class >> new: anArray over: aRing [
	^ self components: (anArray collect: [:each| ProjectiveSpace new: each over: aRing])
]

{ #category : #accessing }
ProductProjectiveSpace >> arity [
	^ self components size
]

{ #category : #accessing }
ProductProjectiveSpace >> at: anInteger [
	^ self components at: anInteger
]

{ #category : #'accessing-private' }
ProductProjectiveSpace >> components [
	^ self propertyAt: #components
]

{ #category : #'accessing-private' }
ProductProjectiveSpace >> components: anArray [
	self propertyAt: #components put: anArray
]

{ #category : #accessing }
ProductProjectiveSpace >> coordinateRing [
	^ self
		propertyAt: #coordinateRing
		ifAbsentPut: [ self components
				fold: [ :A :B | A coordinateRing í B coordinateRing ] ]
]

{ #category : #testing }
ProductProjectiveSpace >> isProduct [
	^ true
]

{ #category : #printing }
ProductProjectiveSpace >> printOn: aStream [
	self components
		do: [ :each | aStream print: each ]
		separatedBy: [ aStream nextPut: $✖]
]

{ #category : #'as yet unclassified' }
ProductProjectiveSpace >> segreEmbedding [
	"Answer the Segre embedding into a projective space."
	self notYetImplemented
]
