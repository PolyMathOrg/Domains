Class {
	#name : #Benchmark,
	#superclass : #Object,
	#category : #MathematicsTests
}

{ #category : #'as yet unclassified' }
Benchmark >> run [
	| output |
	output := WriteStream on: (String new: 1000).
	(self class selectors asArray select: [:each|
		(each beginsWith: 'test') and: [each numArgs isZero]]) sort
		do: [:each|
			output nextPutAll: each; tab.
			self setUp.
			Smalltalk garbageCollect.
			[output nextPutAll: [self perform: each] bench] on: Error do: [output nextPutAll: 'FAILED'].
			self tearDown]
		separatedBy: [output newLine].
	^ output contents
]

{ #category : #'as yet unclassified' }
Benchmark >> setUp [
	^ self
]

{ #category : #'as yet unclassified' }
Benchmark >> tearDown [
	^ self
]
