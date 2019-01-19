"
Homomorphisms of commutative rings. See Ring.
"
Class {
	#name : #RingMap,
	#superclass : #Function,
	#category : #'Mathematics-Rings'
}

{ #category : #examples }
RingMap class >> example1 [
	"The ring of rational integers is the initial object in the category of rings.
	There's always a unique ring homomorphism from the integers to any given ring:"
	^ 'ZZ  (ZZ/6) polynomials'
]

{ #category : #comparing }
RingMap >> = aRingMap [
	(aRingMap isKindOf: RingMap) ifFalse: [^ super = aRingMap].
	(self domain = aRingMap domain and: [self codomain = aRingMap codomain]) ifFalse: [^ false].
	^ self domain generators allSatisfy: [:each| (self value: each) = (aRingMap value: each)]
]

{ #category : #converting }
RingMap >> asAbelianGroupHomomorphism [
	^ self domain asAbelianGroup to: self codomain asAbelianGroup evaluating: self
]

{ #category : #converting }
RingMap >> asModuleHomomorphism [
	^ self domain asModule to: self codomain asModule evaluating: self
]

{ #category : #testing }
RingMap >> is: aSymbol [
	^ aSymbol == #RingHomomorphism or: [super is: aSymbol]
]

{ #category : #testing }
RingMap >> isInjective [
	(self domain isField and: [self codomain isTrivial not]) ifTrue: [^ true]. "a ring homomorphism from a field to a nontrivial ring is injective."
	^ self kernel isZero
]

{ #category : #testing }
RingMap >> isLocal [
	"A ring homomorphism called 'local' if it is a homomorphism of local rings and carries the maximal ideal to the maximal ideal."
	^ self domain isLocal and: [self codomain isLocal and: [(self domain maximalIdeal apply: self) <= self codomain maximalIdeal]]
]

{ #category : #testing }
RingMap >> isZero [
	"A ring homomorphism to a non-trivial ring cannot be zero, because 1 maps to 1."
	^ (self value: self domain one) = self codomain zero
"	^ self codomain isTrivial"
]

{ #category : #operations }
RingMap >> spec [
	"This is the Spec functor. Answer the affine scheme homomorphism induced by the receiver, i.e. given a ring homomorphism f:R->S, Spec(f) is a scheme homomorphism Spec(S)->Spec(R)."
	^ self codomain spec to: self domain spec evaluating: [:anIdeal| self preimage: anIdeal]
]

{ #category : #private }
RingMap >> species [
	^ RingMap
]
