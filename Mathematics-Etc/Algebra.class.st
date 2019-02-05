"
R-algebras seen as R-modules together with a binary operation of multiplication.
"
Class {
	#name : #Algebra,
	#superclass : #FreeModule,
	#category : #'Mathematics-Etc-Algebras'
}

{ #category : #testing }
Algebra >> isAlgebra [
	^ true
]

{ #category : #testing }
Algebra >> isCommutative [
	| op X |
	self propertyAt: #isCommutative ifPresent: [ :aBoolean | ^ aBoolean ].
	op := self multiplication.
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

{ #category : #accessing }
Algebra >> multiplication [
	^ (self , self to: self evaluatingWithArguments: [ :x :y | x * y ])
		name: '*'
]

{ #category : #accessing }
Algebra >> multiplicationInverseMap [
	^ (self to: self evaluating: [ :each | each reciprocal ])
		name: 'x^-1'
]

{ #category : #accessing }
Algebra >> one [
	^ self propertyAt: #one ifAbsentPut: [ self generators anyOne one ]
]
