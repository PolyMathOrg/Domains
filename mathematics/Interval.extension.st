Extension { #name : #Interval }

{ #category : #'*mathematics' }
Interval >> isStandard [
	"Answer true if the receiver is an interval [1..n]."
	^ start = 1 and: [stop isInteger and: [stop >= 1 and: [stop - start + 1 = count]]]
]

{ #category : #'*mathematics' }
Interval >> printOn: aStream [
	self increment = 1
		ifTrue: [aStream nextPut: $[; print: start; nextPutAll: '..'; print: stop; nextPut: $]]
		ifFalse: [self storeOn: aStream]
]

{ #category : #'*mathematics' }
Interval >> storeOn: aStream [
	aStream nextPut: $(; print: start; nextPutAll: ' to: '; print: stop.
	self increment ~= 1 ifTrue: [aStream nextPutAll: ' by: '; print: self increment].
	aStream nextPut: $)
]
