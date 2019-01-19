"
Groups of transformations on a given space. The elements are some kind of functions or morphisms (usually endomorphisms of the associated space), and the group operation is composition.

These groups act on the associated space (or G-set, or G-space) by the action g^v |-> g(v), i.e. by evaluation.
"
Class {
	#name : #TransformationGroup,
	#superclass : #Group,
	#category : #'Mathematics-Groups'
}

{ #category : #private }
TransformationGroup >> defaultInverseMap [
	^ self compositiveInverseMap
]

{ #category : #private }
TransformationGroup >> defaultOperation [
	^ self compositiveOperation
]
