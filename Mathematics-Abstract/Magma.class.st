"
Magmas consist of a set and a binary operation, with no other requirements.
"
Class {
	#name : #Magma,
	#superclass : #Domain,
	#category : #'Mathematics-Abstract'
}

{ #category : #copying }
Magma >> copyEmpty [
	^ super copyEmpty operation: self operation
]

{ #category : #testing }
Magma >> isCommutative [
	| op X |
	self propertyAt: #isCommutative ifPresent: [ :aBoolean | ^ aBoolean ].
	op := self operation.
	X := self generators ifNil: [ self ].
	X
		do: [ :x | 
			X
				do: [ :y | 
					(op
						value:
							{x.
							y})
						=
							(op
								value:
									{y.
									x})
						ifFalse: [ ^ false ] ] ].
	^ true
]

{ #category : #morphic }
Magma >> multiplicationTable [
	| elements |
	elements := self elements asArray
		asSortedCollection: [ :a :b |
			| str |
			str := a printString.
			({'id' . '0' . '1'} includes: str) or: [ str <= b printString ] ].
	^ MultiplicationTableMorph
		elements: elements
		operation: self operation
]

{ #category : #morphic }
Magma >> multiplicationTable2 [
	| elements op table palette p |
	op := self operation.
	palette := DiscretePalette default.
	table := LayoutMorph newRow color: Color red.
	table morphExtent: 150@150.
	elements := self elements asArray asSortedCollection: [:a :b|
		| str |
		str := a printString.
		({'id'. '0'. '1'} includes: str) or: [str <= b printString]].
	p := 1 / elements size.
	elements do: [:x| | column |
		column := LayoutMorph newColumn color: Color green.
		elements do: [:y| | cell xy |
			xy := op value: {x. y}.
			cell := RectangleLikeMorph new color: (palette at: xy).
			cell setBalloonText: xy printString.
			column addMorph: cell proportionalHeight: p].
		table addMorph: column proportionalWidth: p].
	^ table
]

{ #category : #accessing }
Magma >> operation [
	^ self
		propertyAt: #operation
		ifAbsentPut: [ (self , self to: self evaluatingWithArguments: [ :x :y | x * y ])
				name: '*' ]
]

{ #category : #'accessing-private' }
Magma >> operation: aFunction [
	self propertyAt: #operation put: (self , self hom: self) ! aFunction
]
