"
Semirings are like rings, but without the requirement that each element must have an additive inverse. This is, addition yields only a commutative monoid, not necessarily a commutative group as with rings.

Examples of semirings are the non-negative rational numbers and the non-negative real numbers. Another example is the set of all ideals of a given ring under addition and multiplication of ideals.
"
Class {
	#name : #Semiring,
	#superclass : #Domain,
	#category : #'Mathematics-Rings'
}

{ #category : #accessing }
Semiring >> addition [
	^ ((self, self) to: self evaluatingWithArguments: [:x :y| x + y]) name: '+'
]

{ #category : #accessing }
Semiring >> additionInverseMap [
	^ (self to: self evaluating: [:each| each negated]) name: '-id'
]

{ #category : #morphic }
Semiring >> additionTable [
	^ MultiplicationTableMorph elements: self elements asArray operation: self addition
]

{ #category : #accessing }
Semiring >> characteristic [
	^ self propertyAt: #characteristic
]

{ #category : #accessing }
Semiring >> multiplication [
	^ ((self, self) to: self evaluatingWithArguments: [:x :y| x * y]) name: '*'
]

{ #category : #accessing }
Semiring >> multiplicationInverseMap [
	^ (self to: self evaluating: [:each| each reciprocal]) name: 'x^-1'
]

{ #category : #morphic }
Semiring >> multiplicationTable [
	^ MultiplicationTableMorph elements: self elements asArray operation: self multiplication
]

{ #category : #accessing }
Semiring >> one [
	^ self propertyAt: #one ifAbsentPut: [self generators anyOne one]
]

{ #category : #accessing }
Semiring >> scalars [
	"Because the ring of rational integers is the initial object in the category of rings.
	Subclasses can override."
	^ ZZ
]

{ #category : #accessing }
Semiring >> zero [
	^ self propertyAt: #zero ifAbsentPut: [self one - self one]
]
