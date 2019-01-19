"
Groups of (invertible) affine maps acting on an affine space. They are subgroups of the general affine group GA(A).
"
Class {
	#name : #AffineGroup,
	#superclass : #TransformationGroup,
	#instVars : [
		'space'
	],
	#category : #'Mathematics-Groups-Affine'
}

{ #category : #'instance creation' }
AffineGroup class >> on: anAffineSpace [
	^ self new space: anAffineSpace
]

{ #category : #accessing }
AffineGroup >> action [
	"Answer the natural action that sends (f, x) to f(x)."
	^ GroupAction from: (self, space) to: space evaluatingWithArguments: [:f :x| f value: x]
]

{ #category : #accessing }
AffineGroup >> ambient [
	"Answer the ambient group."
	^ space automorphisms "the general affine group GA(A)"
]

{ #category : #operations }
AffineGroup >> asSemidirectProduct [
	self notYetImplemented
"	^ SemidirectProductGroup left: space direction right: self linear action: self linear id"
]

{ #category : #accessing }
AffineGroup >> identity [
	^ space id
]

{ #category : #testing }
AffineGroup >> includes: anAffineMap [
	^ self notYetImplemented
]

{ #category : #operations }
AffineGroup >> linear [
	^ self propertyAt: #linear
]

{ #category : #printing }
AffineGroup >> printOn: aStream [
	self class == AffineGroup ifTrue: [aStream nextPutAll: 'Aff('; print: self linear; nextPut: $). ^ self].
	aStream nextPutAll: self shortName.
	aStream nextPut: $(; print: space; nextPut: $)
]

{ #category : #accessing }
AffineGroup >> scalars [
	^ space scalars
]

{ #category : #printing }
AffineGroup >> shortName [
	^ self subclassResponsibility
]

{ #category : #accessing }
AffineGroup >> space [
	^ space
]

{ #category : #'accessing-private' }
AffineGroup >> space: anAffineSpace [
	space := anAffineSpace
]

{ #category : #private }
AffineGroup >> species [
	^ AffineGroup
]
