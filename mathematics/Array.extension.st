Extension { #name : #Array }

{ #category : #'*mathematics' }
Array >> printOn: aStream [
	self == Smalltalk specialObjectsArray
		ifTrue: [aStream nextPutAll: 'Smalltalk specialObjectsArray' ]
		ifFalse:
			[aStream nextPut: $(.
			self do: [:each| aStream print: each] separatedBy: [aStream nextPutAll: ', '].
			aStream nextPut: $)]
]
