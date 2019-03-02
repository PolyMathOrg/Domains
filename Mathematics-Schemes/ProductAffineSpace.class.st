"
Cartesian products of affine spaces.

"
Class {
	#name : #ProductAffineSpace,
	#superclass : #AffineSpace,
	#category : #'Mathematics-Schemes-Affine'
}

{ #category : #'instance creation' }
ProductAffineSpace class >> components: anArray [
	^ self new components: anArray
]

{ #category : #examples }
ProductAffineSpace class >> example1 [
	^ ProductAffineSpace new: #(#(x y z) #(a b)) over: QQ
]

{ #category : #examples }
ProductAffineSpace class >> example2 [
	^ '(AffineSpace new: #(x y z) over: QQ) ◊ (AffineSpace new: #(a b) over: QQ)'
]

{ #category : #examples }
ProductAffineSpace class >> example3 [
	^'((AffineSpace new: #(x y z) over: QQ) ◊ (AffineSpace new: #(a b) over: QQ)) coordinateRing'
]

{ #category : #'instance creation' }
ProductAffineSpace class >> new: anArray over: aRing [
	^ self
		components: (anArray collect: [ :each | AffineSpace new: each over: aRing ])
]

{ #category : #accessing }
ProductAffineSpace >> arity [
	^ self components size
]

{ #category : #accessing }
ProductAffineSpace >> at: anInteger [
	^ self components at: anInteger
]

{ #category : #'accessing-private' }
ProductAffineSpace >> components [
	^ self propertyAt: #components
]

{ #category : #'accessing-private' }
ProductAffineSpace >> components: anArray [
	self propertyAt: #components put: anArray
]

{ #category : #accessing }
ProductAffineSpace >> coordinateRing [
	^ self
		propertyAt: #coordinateRing
		ifAbsentPut: [ self components
				fold: [ :A :B | A coordinateRing tensorProduct: B coordinateRing ] ]
]

{ #category : #testing }
ProductAffineSpace >> isProduct [
	^ true
]

{ #category : #printing }
ProductAffineSpace >> printOn: aStream [
	self components do: [:each| aStream print: each] separatedBy: [aStream nextPut: Character times]
]

{ #category : #morphisms }
ProductAffineSpace >> projection: i [
	| shift |
	shift := 0.
	1 to: i-1 do: [:each| shift := shift + (self at: each) rank].
	^ RationalMap from: self to: (self at: i) polynomials: ((1 to: (self at: i) rank) collect: [:j| self coordinateRing x: j+shift])
]
