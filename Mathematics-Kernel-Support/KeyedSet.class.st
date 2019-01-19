Class {
	#name : #KeyedSet,
	#superclass : #Set,
	#category : #'Mathematics-Kernel-Support'
}

{ #category : #accessing }
KeyedSet >> at: anObject [
	"Answer an object in the receiver that is equal to anObject,
	nil if no such object is found. Relies heavily on hash properties"
	| index |
	^(index := self scanFor: anObject) = 0 ifFalse: [array at: index]
]

{ #category : #accessing }
KeyedSet >> at: anObject ifAbsent: exceptionBlock [
	| index |
	^ ((index := self scanFor: anObject) = 0 ifFalse: [array at: index]) ifNil: exceptionBlock
]

{ #category : #accessing }
KeyedSet >> at: anObject ifAbsentPut: aBlock [
	"Answer an object in the receiver that is equal to anObject, or evaluate aBlock to get one and add it to the receiver,
	Relies heavily on hash properties, it is important that the following holds: aBlock value = anObject."
	| index |
	anObject ifNil: [self error: 'Sets cannot meaningfully contain nil as an element'].
	index := self findElementOrNil: anObject.
	^ (array at: index) ifNil: [self atNewIndex: index put: aBlock value]
]
