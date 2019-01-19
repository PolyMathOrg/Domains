"
Sets of S-points (or S-rational points) of a scheme X, noted X(S), where X and S are schemes over some base scheme or ring B. By definition, an S-point is a morphism from S to X over B. See also RationalPoint.
"
Class {
	#name : #PointSet,
	#superclass : #HomSet,
	#category : #'Mathematics-Schemes'
}

{ #category : #enumerating }
PointSet >> do: aBlock [
	self codomain pointsOver: self scalars do: aBlock
]

{ #category : #accessing }
PointSet >> scalars [
	^ self domain coordinateRing
]

{ #category : #accessing }
PointSet >> size [
	^ self propertyAt: #size ifAbsentPut: [self codomain pointsCountOver: self scalars]
]
