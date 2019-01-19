Extension { #name : #Set }

{ #category : #'*mathematics' }
Set >> add: newObject ifAbsent: aBlock [
	"Include newObject as one of the receiver's elements, but only if
	not already present. Answer newObject."

	| index |
	newObject ifNil: [self error: 'Sets cannot meaningfully contain nil as an element'].
	index := self findElementOrNil: newObject.
	(array at: index) ifNil: [self atNewIndex: index put: newObject. aBlock value].
	^ newObject
]

{ #category : #'*mathematics' }
Set >> add: newObject ifPresent: aBlock [
	"Include newObject as one of the receiver's elements, but only if
	not already present. Answer newObject."

	| index |
	newObject ifNil: [self error: 'Sets cannot meaningfully contain nil as an element'].
	index := self findElementOrNil: newObject.
	(array at: index) isNil
		ifTrue: [self atNewIndex: index put: newObject]
		ifFalse: [aBlock value].
	^ newObject
]

{ #category : #'*mathematics' }
Set >> powerset [
	"Answer all subsets of the receiver, including self and {}."
	| e answer |
	self isEmpty ifTrue: [^ OrderedCollection with: self].
	e := self anyOne.
	answer := (self copyWithout: e) powerset.
	answer copy do: [:each| answer add: (each copyWith: e)].
	^ answer
]

{ #category : #'*mathematics' }
Set >> printOn: aStream [
	(self isMemberOf: Set)
		ifFalse: [^ super printOn: aStream].
	aStream nextPut: ${.
	self do: [:each| aStream print: each] separatedBy: [aStream nextPutAll: ', '].
	aStream nextPut: $}
]
