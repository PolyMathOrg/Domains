Class {
	#name : #OEIS,
	#superclass : #Object,
	#instVars : [
		'entries'
	],
	#classVars : [
		'Default'
	],
	#category : #'Mathematics-Etc'
}

{ #category : #'as yet unclassified' }
OEIS class >> default [
	^ Default ifNil: [Default := self new]
]

{ #category : #'as yet unclassified' }
OEIS >> initialize [
	entries := OrderedCollection new.
	'oeis.txt' asFileEntry readStream: [:aStream|
		[aStream atEnd]
			whileFalse:
				[| line |
				line := aStream nextLine.
				line first = $#
					ifFalse:
						[| name tokens |
						tokens := line findTokens: ','.
						name := tokens first allButLast.
						entries add: name -> (tokens allButFirst collect: [:each| each asInteger]) asArray]]].
	entries := entries asArray sort: [:a :b| a value size >= b value size]
]

{ #category : #'as yet unclassified' }
OEIS >> longestEntrySize [
	^ entries first value size
]

{ #category : #'as yet unclassified' }
OEIS >> lookup2: anArray [
	'oeis.txt' asFileEntry readStream: [:aStream|
		[aStream atEnd]
			whileFalse:
				[| line |
				line := aStream nextLine.
				line first = $#
					ifFalse:
						[| name tokens |
						tokens := line findTokens: ','.
						name := tokens first allButLast.
						((1 to: (tokens size - 1 min: anArray size))
							allSatisfy: [:i| (tokens at: i+1) asInteger = (anArray at: i)])
								ifTrue: [^ name]]]].
		^ nil
]

{ #category : #'as yet unclassified' }
OEIS >> lookup: anArray [
	| array |
	array := (anArray is: #Sequence) ifTrue: [anArray copyFrom: 1 to: self longestEntrySize] ifFalse: [anArray].
	entries do: [:each|
		each value size = 0 ifTrue: [^ nil].
		((1 to: (each value size min: array size))
			allSatisfy: [:i| (each value at: i) = (array at: i)])
				ifTrue: [^ each key]].			
	^ nil
]
