"
Group homomorphisms. See Group.
"
Class {
	#name : #GroupMap,
	#superclass : #Function,
	#category : #'Mathematics-Groups'
}

{ #category : #'instance creation' }
GroupMap class >> from: aDomain to: anotherDomain map: aDictionary [
	^ self new domain: aDomain; codomain: anotherDomain; map: aDictionary
]

{ #category : #comparing }
GroupMap >> = anObject [
	(anObject isKindOf: GroupMap) ifFalse: [^ super = anObject].
	(anObject domain = self domain and: [anObject codomain = self codomain])
		ifFalse: [^ false].
	^ (self domain generators ifNil: [self domain]) allSatisfy: [:each| (self value: each) = (anObject value: each)]
]

{ #category : #accessing }
GroupMap >> fiberAt: anElement [
	"Answer the fiber (or inverse image) of anElement, a Coset.
	Answer nil if the element is not in the image of the receiver."
	^ self kernel * (self domain detect: [:one| (self value: one) = anElement] ifNone: [^ nil])
]

{ #category : #accessing }
GroupMap >> image [
	"Answer the image of the receiver."
	^ self domain collect: [:each| self value: each]
]

{ #category : #arithmetic }
GroupMap >> inverse [
	"Answer the compositional inverse of the receiver."
	^ self class
		from: self codomain to: self domain
		evaluating: [:each| self domain detect: [:one| (self value: one) = each]]
]

{ #category : #testing }
GroupMap >> is: aSymbol [
	^ aSymbol == #GroupHomomorphism or: [super is: aSymbol]
]

{ #category : #testing }
GroupMap >> isInjective [
	^ self kernel isTrivial
]

{ #category : #testing }
GroupMap >> isSurjective [
	^ self image = self codomain
]

{ #category : #accessing }
GroupMap >> kernel [
	"Answer the kernel of the receiver."
	^ self codomain select: [:each| (self value: each) = self codomain identity]
]

{ #category : #private }
GroupMap >> map [
	^ self propertyAt: #map ifAbsent: []
]

{ #category : #private }
GroupMap >> map: aDictionary [
	self propertyAt: #map put: aDictionary
]

{ #category : #private }
GroupMap >> species [
	^ GroupMap
]
