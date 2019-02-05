"
Hom(A,B), Hom-Set objects for domain A and codomain B, i.e. sets of all morphisms from A to B. When A = B, this is noted End(A), the set of endomorphisms.
"
Class {
	#name : #HomSet,
	#superclass : #Domain,
	#category : #'Mathematics-Kernel'
}

{ #category : #examples }
HomSet class >> example1 [
	"The object Hom(N,Z), the functions from the natural numbers to the integers.
	This is the space of sequences. (See class Sequence)."
	^ NN hom: ZZ
]

{ #category : #examples }
HomSet class >> example2 [
	"The endomorphisms of the rational integers Z.
	This is Hom(Z,Z), the set of ring homomorphisms from Z to itself."
	^ ZZ endomorphisms
]

{ #category : #'instance creation' }
HomSet class >> from: aDomain to: anotherDomain [
	^ self new domain: aDomain; codomain: anotherDomain
]

{ #category : #elements }
HomSet >> ! anObject [
	anObject isEvaluable 
		ifTrue: [ ^ self evaluating: anObject ].
	^ super ! anObject
]

{ #category : #accessing }
HomSet >> codomain [
	^ self propertyAt: #codomain
]

{ #category : #'accessing-private' }
HomSet >> codomain: aDomain [
	self propertyAt: #codomain put: aDomain
]

{ #category : #accessing }
HomSet >> domain [
	^ self propertyAt: #domain
]

{ #category : #'accessing-private' }
HomSet >> domain: aDomain [
	self propertyAt: #domain put: aDomain
]

{ #category : #elements }
HomSet >> evaluating: aBlock [
	^ self domain to: self codomain evaluating: aBlock
]

{ #category : #elements }
HomSet >> evaluatingWithArguments: aBlock [
	^ self domain to: self codomain evaluatingWithArguments: aBlock
]

{ #category : #elements }
HomSet >> identity [
	^ self isEndomorphisms
		ifTrue: [ self domain id ] 
]

{ #category : #testing }
HomSet >> includes: aMorphism [
	^ (aMorphism isKindOf: Morphism)
		and: [ aMorphism domain = self domain
				and: [ aMorphism codomain = self codomain ] ] 
]

{ #category : #testing }
HomSet >> isEndomorphisms [
	^ self domain = self codomain
]

{ #category : #operations }
HomSet >> opposite [
	^ self class from: self codomain to: self domain
]

{ #category : #printing }
HomSet >> printOn: aStream [
	self isEndomorphisms
		ifTrue: [ aStream
				nextPutAll: 'End';
				nextPut: $(;
				print: self domain;
				nextPut: $) ]
		ifFalse: [ aStream
				nextPutAll: 'Hom';
				nextPut: $(;
				print: self domain;
				nextPut: $,;
				print: self codomain;
				nextPut: $) ]
]
