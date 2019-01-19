Extension { #name : #Dictionary }

{ #category : #'*mathematics' }
Dictionary >> at: key add: value [
	| index assoc |
	index := self findElementOrNil: key.
	assoc := array at: index.
	assoc
		ifNil:
			[value isZero ifFalse: [self atNewIndex: index put: (Association key: key value: value)]]
		ifNotNil:
			[|newValue|
			newValue := assoc value + value.
			assoc value: newValue.
			^ newValue].
	^ value
]

{ #category : #'*mathematics' }
Dictionary >> at: key addAndRemoveIfZero: value [
	| index assoc |
	index := self findElementOrNil: key.
	assoc := array at: index.
	assoc
		ifNil:
			[value isZero ifFalse: [self atNewIndex: index put: (Association key: key value: value)]]
		ifNotNil:
			[|newValue|
			newValue := assoc value + value.
			newValue isZero
				ifTrue:
					[array at: index put: nil.
					tally := tally - 1.
					self fixCollisionsFrom: index]
				ifFalse: [assoc value: newValue].
			^ newValue].
	^ value
]
