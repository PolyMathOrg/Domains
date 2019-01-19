Extension { #name : #Point }

{ #category : #'*mathematics' }
Point >> norm [
	^ (x*x + (y*y)) sqrt
]

{ #category : #'*mathematics' }
Point >> norm2 [
	^ x*x + (y*y)
]
