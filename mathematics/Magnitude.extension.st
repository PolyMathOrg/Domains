Extension { #name : #Magnitude }

{ #category : #'*mathematics' }
Magnitude >> isFinite [
	^ self isInfinite not
]

{ #category : #'*mathematics' }
Magnitude >> isInfinite [
	^ false
]
