"
Maps from a set (domain) to another set (codomain). Evaluated at elements of the domain (>>#value:) they produce elements of the codomain. See Domain and HomSet.

Example:
	Function from: ZZ to: ZZ evaluating: [:x| x squared + 1].

A Function is a morphism of sets. If the function preserves some mathematical structure, it is called a morphism of some category corresponding to the preserved structure. For example linear maps are morphisms of vector spaces or modules, continuous functions are morphisms of topological spaces, and group homomorphisms are morphisms of groups.

Example (three equivalent ways to construct homomorphisms):
	""These constructions are similar to the explicit construction above, but they return not arbitrary functions but homomorphisms of the corresponding category (in this case linear maps, i.e. morphisms of vector spaces):""
	QQ^3 to: QQ^3 evaluating: [:v| (v x - v y, v x, v z)].
	(QQ^3 hom: QQ^3) evaluating: [:v| (v x - v y, v x, v z)].
	(QQ^3) endomorphisms evaluating: [:v| (v x - v y, v x, v z)].

In general, functions are defined by specifying a domain, a codomain, and an expression that can be evaluated at elements of the domain and produces elements of the codomain. One such expression can be a Smalltalk block, another Function, or more generally any Smalltalk object that admits evaluation (#value:), such as polynomials:

Example (two ways to define the Frobenius endomorphism):
	(ZZ/6) endomorphisms evaluating: [:x| x^6].
	(ZZ/6) endomorphisms evaluating: (ZZ/6) polynomials x ^ 6.

Note that functions defined by polynomials or other symbolic expressions, as opposed to functions defined by Smalltalk blocks, are printed more explicitly (as a formula).

References:
	https://en.wikipedia.org/wiki/Function_(set_theory)
	https://en.wikipedia.org/wiki/Morphism

"
Class {
	#name : #Function,
	#superclass : #Morphism,
	#instVars : [
		'properties'
	],
	#category : #'Mathematics-Kernel'
}

{ #category : #'instance creation' }
Function class >> evaluating: anExpression [
	^ self new expression: anExpression
]

{ #category : #examples }
Function class >> example1Function [
	"The function 'x^2 + 1' with domain the ring of rational integers
	and codomain the set of natural numbers."
	^ Function from: ZZ to: NN evaluating: [:x| x squared + 1]
]

{ #category : #examples }
Function class >> example2Morphism1 [
	"This is the most common way to define morphisms.
	QQ^3 is the vector space of 3-tuples with rational coefficients,
	and this defines a linear map on it (an endomorphism)
	by sending the message #to:evaluating: to the vector space."
	^ 'QQ^3 to: QQ^3 evaluating: [:v| (v x - v y, v x, v z)]'
]

{ #category : #examples }
Function class >> example2Morphism2 [
	"Here's another way to define the same morphism,
	by creating Hom(Q^3, Q^3) and sending the message #evaluating: to it."
	^ '(QQ^3 hom: QQ^3) evaluating: [:v| (v x - v y, v x, v z)]'
]

{ #category : #examples }
Function class >> example2Morphism3 [
	"And yet a third way. Here Hom(Q^3, Q^3) is created
	by sending the message #endomorphisms to the vector space."
	^ '(QQ^3) endomorphisms evaluating: [:v| (v x - v y, v x, v z)]'
]

{ #category : #examples }
Function class >> example3Frobenius1 [
	"One way to define the Frobenius ring homomorphism."
	^ (ZZ / 6) endomorphisms evaluating: [:x| x raiseTo: 6]
]

{ #category : #examples }
Function class >> example3Frobenius2 [
	"The Frobenius ring homomorphism defined by a polynomial."

	| R x |
	R := ZZ / 6.
	x := R polynomials x.
	^ R endomorphisms evaluating: (x raisedTo: 6)
]

{ #category : #'instance creation' }
Function class >> from: aDomain to: anotherDomain evaluating: anExpression [
	^ self new domain: aDomain; codomain: anotherDomain; expression: anExpression
]

{ #category : #'instance creation' }
Function class >> from: aDomain to: anotherDomain evaluating: anExpression inverseEvaluating: anotherExpression [
	| answer inverse |
	answer := self from: aDomain to: anotherDomain evaluating: anExpression.
	inverse := self from: anotherDomain to: aDomain evaluating: anotherExpression.
	answer propertyAt: #leftInverse put: inverse.
	inverse propertyAt: #rightInverse put: answer.
	^ answer
]

{ #category : #'instance creation' }
Function class >> from: aDomain to: aCodomain evaluatingWithArguments: aBlock [
	^ self from: aDomain to: aCodomain evaluating: [:each| aBlock valueWithArguments: each asArray]
]

{ #category : #'instance creation' }
Function class >> newFrom: aFunction [
	^ self from: aFunction domain to: aFunction codomain evaluating: aFunction
]

{ #category : #operations }
Function >> * anObject [
	^ (self codomain includes: anObject)
		ifTrue: [ self species
				from: self domain
				to: self codomain 
				evaluating: [ :each | (self value: each) * anObject ] ]
		ifFalse: [ self species
				from: self domain
				to: self codomain
				evaluating: [ :each | (self value: each) * (anObject value: each) ] ]
]

{ #category : #operations }
Function >> + anObject [
	^ (self codomain includes: anObject)
		ifTrue: [ self species
				from: self domain
				to: self codomain
				evaluating: [ :each | (self value: each) + anObject ] ]
		ifFalse: [ self species
				from: self domain
				to: self codomain
				evaluating: [ :each | (self value: each) + (anObject value: each) ] ]
]

{ #category : #operations }
Function >> , aFunction [
	"Answer the cartesian product of the receiver with the argument."
	^ Function
		from: (self domain, aFunction domain)
		to: (self codomain, aFunction codomain)
		evaluating: [:each| {self value: (each at: 1). aFunction value: (each at: 2)}]
]

{ #category : #operations }
Function >> - aFunction [
	^ self + aFunction negated
]

{ #category : #operations }
Function >> / aFunction [
	^ self * aFunction reciprocal
]

{ #category : #comparing }
Function >> = aFunction [
	self == aFunction ifTrue: [^ true].
	(self domain = aFunction domain and: [self codomain = aFunction codomain])
		ifFalse: [^ false].
	self domain isFinite ifFalse: [^ self error: 'unable to check equality'].
	self domain do: [:each| (self value: each) = (aFunction value: each) ifFalse: [^ false]].
	^ true
]

{ #category : #operations }
Function >> backwardDifference: n at: h [
^ self species
		from: self domain
		to: self codomain
		evaluating: [ :x | 
			(0 to: n)
				sum: [ :i | (-1 raisedTo: i) * (n choose: i) * (self value: x + (i * h)) ] ]
]

{ #category : #operations }
Function >> centralDifference: n at: h [
	^ self species
		from: self domain
		to: self codomain
		evaluating: [ :x | 
			(0 to: n)
				sum:
					[ :i | (-1 raisedTo: i) * (n choose: i) * (self value: x + ((n / 2 - i) * h)) ] ]
]

{ #category : #accessing }
Function >> codomain [
	^ self propertyAt: #codomain
]

{ #category : #'accessing-private' }
Function >> codomain: aDomain [
	self propertyAt: #codomain put: aDomain
]

{ #category : #operations }
Function >> corestrictedTo: aCodomain [
	^ self species from: self domain to: aCodomain evaluating: [:x| self value: x]
]

{ #category : #accessing }
Function >> domain [
	^ self propertyAt: #domain
]

{ #category : #'accessing-private' }
Function >> domain: aDomain [
	self propertyAt: #domain put: aDomain
]

{ #category : #private }
Function >> expression [
	^ self propertyAt: #expression ifAbsent: [self]
]

{ #category : #private }
Function >> expression: anExpression [
	self propertyAt: #expression put: ((anExpression isKindOf: Function) ifTrue: [anExpression expression] ifFalse: [anExpression])
]

{ #category : #operations }
Function >> forwardDifference: n at: h [
	^ self species
		from: self domain
		to: self codomain
		evaluating: [ :x | 
			(0 to: n)
				sum:
					[ :i | (-1 raisedTo: n - i) * (n choose: i) * (self value: x + ((n - i) * h)) ] ]
]

{ #category : #properties }
Function >> hasProperty: aSymbol [
	^ (properties ifNil: [ ^ false ]) includesKey: aSymbol 
]

{ #category : #comparing }
Function >> hash [
	^ self domain hash hashMultiply + self codomain hash
]

{ #category : #operations }
Function >> image [
	^ self propertyAt: #image ifAbsent: [self domain apply: self]
]

{ #category : #testing }
Function >> is: aSymbol [
	^ aSymbol == #Function or: [super is: aSymbol]
]

{ #category : #testing }
Function >> isBiyective [
	^ self isInjective and: [ self isSurjective ]
]

{ #category : #testing }
Function >> isEpimorphism [
	^ self isSurjective
]

{ #category : #testing }
Function >> isEvaluable [
	^ true
]

{ #category : #testing }
Function >> isIdentity [
	^ self propertyAt: #isIdentity ifAbsentPut: [self = self domain id]
]

{ #category : #testing }
Function >> isInjective [
	^ self hasLeftInverse
]

{ #category : #testing }
Function >> isMonomorphism [
	^ self isInjective
]

{ #category : #testing }
Function >> isSurjective [
	^ self hasRightInverse
]

{ #category : #operations }
Function >> leftInverse [
^ self propertyAt: #leftInverse
]

{ #category : #printing }
Function >> name [
	^ self propertyAt: #name ifAbsent: [ super name ]
]

{ #category : #printing }
Function >> name: aString [
	self propertyAt: #name put: aString
]

{ #category : #operations }
Function >> negated [
	^ self species
		from: self domain
		to: self codomain
		evaluating: [ :each | (self value: each) negated ]
]

{ #category : #morphic }
Function >> plot: aCollection [
	^ FunctionPlotMorph new evaluationPoints: aCollection; function: self
]

{ #category : #printing }
Function >> printOn: aStream [
	(self expression isBlock not and: [(self expression isKindOf: Function) not])
		ifTrue: [aStream print: self expression]
		ifFalse: [super printOn: aStream]
]

{ #category : #operations }
Function >> prod: aFunction [ "◊ "
	"Answer the product of the receiver with the argument."
	^ self, aFunction
]

{ #category : #properties }
Function >> properties [
	^ properties ifNil: [properties := IdentityDictionary new]
]

{ #category : #properties }
Function >> propertyAt: aSymbol [
	^ self propertyAt: aSymbol ifAbsent: [self error: 'no such property']
]

{ #category : #properties }
Function >> propertyAt: aSymbol ifAbsent: exceptionBlock [
	^ (properties ifNil: [^ exceptionBlock value]) at: aSymbol ifAbsent: exceptionBlock
]

{ #category : #properties }
Function >> propertyAt: aSymbol ifAbsentPut: aBlock [
	^ self properties at: aSymbol ifAbsentPut: aBlock
]

{ #category : #properties }
Function >> propertyAt: aSymbol ifPresent: aBlock [
	^ (properties ifNil: [^ nil]) at: aSymbol ifPresent: aBlock
]

{ #category : #properties }
Function >> propertyAt: aSymbol put: anObject [
	^ self properties at: aSymbol put: anObject
]

{ #category : #operations }
Function >> raisedTo: anObject [
	^ 'anObject isEvaluable
			ifTrue: [self species from: self domain to: self codomain evaluating: [:each| (self value: each) ^ (anObject value: each)]]
			ifFalse: [self species from: self domain to: self codomain evaluating: [:each| (self value: each) ^ anObject]]'
]

{ #category : #operations }
Function >> reciprocal [
	^ self species from: self domain to: self codomain evaluating: [:each| (self value: each) reciprocal]
]

{ #category : #operations }
Function >> restrictedTo: aDomain [
	^ self species
		from: aDomain
		to: self codomain
		evaluating: [ :x | self value: x ]
]

{ #category : #operations }
Function >> restrictedTo: aDomain corestrictedTo: aCodomain [
	^ self species from: aDomain to: aCodomain evaluating: [:x| self value: x]
]

{ #category : #operations }
Function >> rightInverse [
	^ self propertyAt: #rightInverse
]

{ #category : #private }
Function >> species [
	^ Function
]

{ #category : #operations }
Function >> squared [
	^ self * self
]

{ #category : #operations }
Function >> value: anObject [
"	(self domain includes: anObject) ifFalse: [^ anObject apply: self]."
	self flag: #fix. "check argument"
	^ (self propertyAt: #expression) value: anObject
]

{ #category : #operations }
Function >> valueWithArguments: anArray [
	^ self value: (self domain scalars tuple: anArray)
]

{ #category : #operations }
Function >> î [ aFunction
	"Answer the composition of the receiver with the argument.
	Given the argument f:X -> Y and the receiver g:Y -> Z, answer gîf:X -> Z.
	This is, (gîf)(x) = g(f(x))."
	self domain >= aFunction codomain ifFalse: [DomainError signal: 'domains don''t match'].
	^ self species from: aFunction domain to: self codomain evaluating: [:x| self value: (aFunction value: x)]
]
