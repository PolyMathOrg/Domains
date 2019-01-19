Class {
	#name : #YoungTableau,
	#superclass : #Collection,
	#instVars : [
		'rows'
	],
	#category : #'Mathematics-Tableaux'
}

{ #category : #'instance creation' }
YoungTableau class >> rows: anArray [
	^ self basicNew rows: anArray
]

{ #category : #'instance creation' }
YoungTableau class >> shape: anArray [
	^ self rows: (anArray collect: [:each| Array new: each])
]

{ #category : #accessing }
YoungTableau >> at: aPoint [
	^ (rows at: aPoint x) at: aPoint y
]

{ #category : #accessing }
YoungTableau >> at: aPoint put: anObject [
	^ (rows at: aPoint x) at: aPoint y put: anObject
]

{ #category : #copying }
YoungTableau >> copy [
	^ self class rows: (rows collect: [:each| each copy])
]

{ #category : #accessing }
YoungTableau >> diagram [
	^ YoungDiagram shape: self shape
]

{ #category : #enumerating }
YoungTableau >> do: aBlock [
	rows do: [:each| each do: aBlock]
]

{ #category : #accessing }
YoungTableau >> height [
	^ rows size
]

{ #category : #testing }
YoungTableau >> isSemistandard [
	self withIndexDo: [:each :index|
		(index x > 1 and: [each < (self at: index x - 1 @ index y)])
			ifTrue: [^ false].
		(index y > 1 and: [each < (self at: index x @ (index y - 1))])
			ifTrue: [^ false]].
	^ true
]

{ #category : #testing }
YoungTableau >> isStandard [
	"if it is semistandard and content = (1,1,..,1)"
	self withIndexDo: [:each :index|
		(index x > 1 and: [each <= (self at: index x - 1 @ index y)])
			ifTrue: [^ false].
		(index y > 1 and: [each <= (self at: index x @ (index y - 1))])
			ifTrue: [^ false]].
	^ true
]

{ #category : #arithmetic }
YoungTableau >> negated [
	self height = 1 ifTrue: [^ self].
	^ self copy at: 1@1 put: (self at: 1@2); at: 1@2 put: (self at: 1@1); yourself
]

{ #category : #printing }
YoungTableau >> printOn: aStream [
	self rows do: [:row|
		aStream nextPut: $[.
		row do: [:each| aStream print: each] separatedBy: [aStream nextPut: $|].
		aStream nextPut: $]] separatedBy: [aStream lf; space]
]

{ #category : #accessing }
YoungTableau >> rank [
	^ rows sum: [:each| each size]
]

{ #category : #accessing }
YoungTableau >> rows [
	^ rows
]

{ #category : #initialization }
YoungTableau >> rows: anArray [
	rows := anArray
]

{ #category : #accessing }
YoungTableau >> shape [
	^ rows collect: [:each| each size]
]

{ #category : #arithmetic }
YoungTableau >> sign [
	self notYetImplemented
]

{ #category : #accessing }
YoungTableau >> weight [
	| answer |
	answer := Array new: self rank.
	answer atAllPut: 0.
	self do: [:each| answer at: each put: (answer at: each) + 1].
	^ answer
]

{ #category : #accessing }
YoungTableau >> width [
	^ rows first size
]

{ #category : #enumerating }
YoungTableau >> withIndexDo: aBlock [
	rows withIndexDo: [:row :i| row withIndexDo: [:each :j| aBlock value: each value: i@j]]
]
