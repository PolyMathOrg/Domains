Extension { #name : #SequenceableCollection }

{ #category : #'*mathematics' }
SequenceableCollection >> <= aCollection [
	"Answer true if the receiver is a subcollection of aCollection."
	(aCollection isKindOf: self species) ifFalse: [^ false].
	self size <= aCollection size ifFalse: [^ false].
	^ (aCollection indexOfSubCollection: self startingAt: 1) > 0
]

{ #category : #'*mathematics' }
SequenceableCollection >> at: anInteger add: anObject [
	^ self at: anInteger put: (self at: anInteger) + anObject
]

{ #category : #'*mathematics' }
SequenceableCollection >> combinations: r [
	^ Iterator on: [:aBlock| self combinations: r atATimeDo: [:each| aBlock value: each copy]]
]

{ #category : #'*mathematics' }
SequenceableCollection >> convolution: aCollection [
	| answer |
	self isEmpty ifTrue: [^ self].
	aCollection isEmpty ifTrue: [^ aCollection].
	answer := self species new: self size + aCollection size - 1.
	answer atAllPut: (self at: 1) - (self at: 1).
	1 to: self size do: [:i|
		1 to: aCollection size do: [:k|
			answer at: i+k-1 add: (self at: i) * (aCollection at: k)]].
	^ answer
]

{ #category : #'*mathematics' }
SequenceableCollection >> isZero [
	self do: [:each| each isZero ifFalse: [^ false]].
	^ true
]

{ #category : #'*mathematics' }
SequenceableCollection >> permutations [
	^ Iterator on: [:aBlock| self permutationsDo: [:each| aBlock value: each copy]]
]

{ #category : #'*mathematics' }
SequenceableCollection >> permutedBy: aPermutation [
	| answer |
	answer := Array new: self size.
	1 to: self size do: [:i| answer at: (aPermutation at: i) put: (self at: i)].
	^ answer
]

{ #category : #'*mathematics' }
SequenceableCollection >> plot [
	^ FunctionPlotMorph new evaluationPoints: (1 to: self size); function: (Function evaluating: [:n| self at: n])
]

{ #category : #'*mathematics' }
SequenceableCollection >> sum [
	| answer |
	answer := self at: 1.
	2 to: self size do: [:i| answer := answer + (self at: i)].
	^ answer
]
