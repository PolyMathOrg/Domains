"
Free R-modules of formal sums of elements in a finite set with coefficients over R. See FormalSum.
"
Class {
	#name : #FormalSumsModule,
	#superclass : #FreeModule,
	#category : #'Mathematics-Modules-Tuples'
}

{ #category : #examples }
FormalSumsModule class >> example [
	"The free Q-vector space over the set of symbols #a, #b, #c."
	^ FormalSumsModule on: #(a b c) over: QQ
]

{ #category : #'instance creation' }
FormalSumsModule class >> new: anInteger over: aRing [
	^ self on: (1 to: anInteger) over: aRing
]

{ #category : #'instance creation' }
FormalSumsModule class >> on: aCollection over: aRing [
	^ self new scalars: aRing; symbols: aCollection
]

{ #category : #elements }
FormalSumsModule >> ! anObject [
	(self symbols includes: anObject) ifTrue: [^ self x: anObject].
	^ super ! anObject
]

{ #category : #accessing }
FormalSumsModule >> coordinateNames [
	^ self propertyAt: #coordinateNames ifAbsentPut: [self symbols collect: [:each| 'x', each printString sub]]
]

{ #category : #basis }
FormalSumsModule >> coordinatesOf: anElement [
	^ self scalars tuple: self rank evaluating: [:i| anElement at: (self symbols at: i)]
]

{ #category : #basis }
FormalSumsModule >> e: anInteger [
	^ self x: (self symbols at: anInteger)
]

{ #category : #testing }
FormalSumsModule >> includes: anObject [
	(anObject isKindOf: FormalSum) ifFalse: [^ false].
	anObject parent == self ifTrue: [^ true].
	anObject keysDo: [:each| (self symbols includes: each) ifFalse: [^ false]].
	^ true
]

{ #category : #accessing }
FormalSumsModule >> names [
	"Answer a list of names for use instead of the elements of the basis when printing linear maps."
	^ self propertyAt: #names ifAbsentPut: [(1 to: self rank) collect: [:i| (self e: i) printText]]
]

{ #category : #converting }
FormalSumsModule >> over: aRing [
	^ self copy scalars: aRing
]

{ #category : #basis }
FormalSumsModule >> rank [
	^ self symbols size
]

{ #category : #accessing }
FormalSumsModule >> symbols [
	^ self propertyAt: #symbols
]

{ #category : #accessing }
FormalSumsModule >> symbols: aCollection [
	self propertyAt: #symbols put: aCollection asArray
]

{ #category : #basis }
FormalSumsModule >> x: anObject [
	"Answer the embedding of anObject, assuming it is on the symbols of the receiver."
	^ (FormalSum coefficients: ((Dictionary new: 1) at: anObject put: self scalars one; yourself)) parent: self
]
