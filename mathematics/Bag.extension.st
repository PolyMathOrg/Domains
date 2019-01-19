Extension { #name : #Bag }

{ #category : #'*Mathematics' }
Bag >> apply: aFunction [
	| answer |
	answer := self species new.
	self withOccurrencesDo: [:each :times| answer add: (aFunction value: each) withOccurrences: times].
	^ answer
]

{ #category : #'*Mathematics' }
Bag >> withOccurrencesDo: aBlock [
	contents associationsDo: [:each| aBlock value: each key value: each value]
]
