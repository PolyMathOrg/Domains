"
Direct products of rings. Elements are tuples where the i-th component corresponds to an element in the i-th ring of the product (see ProductRingElement), and multiplication and addition are defined component wise.
"
Class {
	#name : #ProductRing,
	#superclass : #Ring,
	#instVars : [
		'components'
	],
	#category : #'Mathematics-Rings'
}

{ #category : #'instance creation' }
ProductRing class >> components: anArray [
	^ self new components: anArray
]

{ #category : #examples }
ProductRing class >> example1 [
	"The product ring of two finite rings. This is a ring of order 4,
	with 3 zero-divisors and 1 unit, characteristic 2, and two maximal
	(and principal) ideals (so it's not a local ring)."
	^ 'ZZ/2 ◊ (ZZ/2)'
]

{ #category : #examples }
ProductRing class >> example2 [
	"The canonical projection to the second component:"
	^ 'ZZ/2 ◊ (ZZ/2) projection: 2'
]

{ #category : #elements }
ProductRing >> ! anObject [
	(anObject isSequenceable and: [anObject size = self arity])
		ifTrue: [^ self compose: (components with: anObject collect: [:eachRing :eachElement| eachRing ! eachElement])].
	^ super ! anObject
]

{ #category : #comparing }
ProductRing >> = anObject [
	^ (anObject isKindOf: ProductRing) and: [components = anObject components]
]

{ #category : #accessing }
ProductRing >> arity [
	^ components size
]

{ #category : #converting }
ProductRing >> asCartesianProduct [
	^ CartesianProduct components: components
]

{ #category : #accessing }
ProductRing >> at: anInteger [
	^ components at: anInteger
]

{ #category : #random }
ProductRing >> atRandom: aRandom [
	^ self compose: (self asCartesianProduct atRandom: aRandom)
]

{ #category : #random }
ProductRing >> atRandom: aRandom bits: bits [
	^ self compose: (self asCartesianProduct atRandom: aRandom bits: bits)
]

{ #category : #accessing }
ProductRing >> characteristic [
	^ components inject: 1 into: [:result :each| result lcm: each characteristic]
]

{ #category : #'accessing-private' }
ProductRing >> components [
	^ components
]

{ #category : #'accessing-private' }
ProductRing >> components: anArray [
	components := anArray
]

{ #category : #morphisms }
ProductRing >> compose: anArray [
	^ ProductRingElement components: anArray
]

{ #category : #morphisms }
ProductRing >> composition [
	^ (Function from: self asCartesianProduct to: self evaluating: [:each| self compose: each]) name: Character times asString
]

{ #category : #enumerating }
ProductRing >> do: aBlock [
	self asCartesianProduct do: [:each| aBlock value: (self compose: each)]
]

{ #category : #morphisms }
ProductRing >> embedding: i [
	^ ((self at: i) to: self evaluating: [:x| self compose: (components withIndexCollect: [:each :k| k = i ifTrue: [x] ifFalse: [each zero]])]) name: 'i', i printText sub
]

{ #category : #comparing }
ProductRing >> hash [
	^ components hash
]

{ #category : #testing }
ProductRing >> includes: anObject [
	(anObject isKindOf: ProductRingElement) ifFalse: [^ false].
	anObject size = components size ifFalse: [^ false].
	components with: anObject do: [:R :x| (R includes: x) ifFalse: [^ false]].
	^ true
]

{ #category : #testing }
ProductRing >> isCommutative [
	^ components allSatisfy: [:each| each isCommutative]
]

{ #category : #testing }
ProductRing >> isEuclidean [
	"Answer true if the receiver is an Euclidean ring, i.e. it has division with remainder."
	(components allSatisfy: [:each| each isEuclidean]) ifTrue: [^ true]. "but how can it be, more than 2 components and it's not an integral domain"
	^ super isEuclidean
]

{ #category : #testing }
ProductRing >> isIntegralDomain [
	"The product of two or more non-trivial rings always has non-trivial zero divisors."
	| count |
	count := 0.
	components do: [:each| each isTrivial ifFalse: [(count := count + 1) > 1 ifTrue: [^ false]]].
	self halt.
	^ true
]

{ #category : #testing }
ProductRing >> isProduct [
	^ true
]

{ #category : #testing }
ProductRing >> isReduced [
	"Answer true if the receiver has no non-zero nilpotent elements, or equivalently if it has no non-zero elements with square zero, i.e. x^2 = 0 implies x = 0."
	(components allSatisfy: [:each| each isReduced]) ifTrue: [^ true]. "is it iff?"
	^ super isReduced
]

{ #category : #testing }
ProductRing >> isUnit: anElement [
	"Answer true if the argument is invertible."
	components with: anElement do: [:each :x| (each isUnit: x) ifFalse: [^ false]].
	^ true
]

{ #category : #testing }
ProductRing >> isZeroDivisor: anElement [
	"Answer true if there exists a nonzero element that multiplied by the argument is zero."
	components with: anElement do: [:each :x| (each isZeroDivisor: x) ifTrue: [^ true]].
	^ false
]

{ #category : #elements }
ProductRing >> one [
	^ self compose: (components collect: [:each| each one])
]

{ #category : #printing }
ProductRing >> printOn: aStream [
	components do: [:each| aStream print: each] separatedBy: [aStream nextPut: Character times]
]

{ #category : #morphisms }
ProductRing >> projection: i [
	"Answer the canonical projection to the i-th component."
	^ (self to: (self at: i) evaluating: [:x| x at: i]) name: Character pi asText, i printText sub
]

{ #category : #accessing }
ProductRing >> size [
	^ components product: [:each| each size]
]

{ #category : #elements }
ProductRing >> zero [
	^ self compose: (components collect: [:each| each zero])
]
