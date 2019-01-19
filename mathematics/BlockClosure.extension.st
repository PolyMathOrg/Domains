Extension { #name : #BlockClosure }

{ #category : #'*mathematics' }
BlockClosure >> count [
	| count |
	count := 0.
	self whileTrue: [count := count + 1].
	^ count
]

{ #category : #'*mathematics' }
BlockClosure >> times: anInteger histogram: binCount [
	^ HistogramMorph new: binCount samples: ((1 to: anInteger) collect: [:each| self value])
]
