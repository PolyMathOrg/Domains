"
Finitely presented R-modules, for a commutative ring R.
"
Class {
	#name : #Module,
	#superclass : #Domain,
	#category : #'Mathematics-Modules'
}

{ #category : #operations }
Module >> * aNumber [
	"Answer the receiver scaled by aNumber."
	(self scalars includes: aNumber) ifFalse: [^ DomainError signal].
	aNumber isZero
		ifTrue: [^ self null].
	self isVectorSpace
		ifTrue: [^ self].
	(aNumber = self scalars one or: [aNumber = self scalars one negated])
		ifTrue: [^ self].
	self scalars isPID "must it be a PID?"
		ifTrue: [^ self ambient span: (self generators collect: [:each| each * aNumber])].
	^ DomainError signal
]

{ #category : #operations }
Module >> + anObject [
	(self ambient includes: anObject) ifTrue: [^ AffineSubspace representative: anObject direction: self].
	(anObject isModule and: [self ambient = anObject ambient])
		ifFalse: [^ super + anObject].
	self isTrivial ifTrue: [^ anObject].
	anObject isTrivial ifTrue: [^ self].
	^ self ambient span: self generators, anObject generators
]

{ #category : #operations }
Module >> / aSubmodule [
	^ self notYetImplemented
]

{ #category : #comparing }
Module >> = anObject [
	self == anObject ifTrue: [^ true].
	(anObject isKindOf: Module) ifFalse: [^ false].
	self scalars = anObject scalars ifFalse: [^ false].
	^ (self generators allSatisfy: [:each| anObject includes: each])
		and: [anObject generators allSatisfy: [:each| self includes: each]]
]

{ #category : #accessing }
Module >> addition [
	^ ((self, self) to: self evaluatingWithArguments: [:x :y| x + y]) name: '+'
]

{ #category : #accessing }
Module >> additionInverseMap [
	^ (self to: self evaluating: [:each| each negated]) name: '-id'
]

{ #category : #operations }
Module >> annihilator [
	^ self null quot: self
]

{ #category : #converting }
Module >> asAbelianGroup [
	^ self as: AbelianGroup
]

{ #category : #accessing }
Module >> characteristic [
	^ self scalars characteristic
]

{ #category : #operations }
Module >> dual [
	^ self hom: self scalars asSelfModule
]

{ #category : #'accessing-private' }
Module >> generators: aCollection [
	super generators: (aCollection asSet reject: [:each| each isZero])
]

{ #category : #comparing }
Module >> hash [
	^ self scalars hash
]

{ #category : #testing }
Module >> isInitial [
	^ self isTrivial
]

{ #category : #testing }
Module >> isLocal [
	^ self scalars isLocal
]

{ #category : #testing }
Module >> isModule [
	^ true
]

{ #category : #testing }
Module >> isNoetherian [
	"A module is called Noetherian if every submodule is finitely generated."
	(self isEmbedded and: [self ambient isNoetherian]) ifTrue: [^ true].
	self scalars isNoetherian ifTrue: [^ true]. "because the receiver is finitely generated"
	^ false "it means we don't know"
]

{ #category : #testing }
Module >> isTerminal [
	^ self isTrivial
]

{ #category : #testing }
Module >> isTorsion [
	"Answer true if the receiver is a torsion module."
	^ self torsion = self
]

{ #category : #testing }
Module >> isTorsionFree [
	"Answer true if the receiver is a torsion-free module."
	^ self torsion isTrivial
]

{ #category : #testing }
Module >> isTrivial [
	"Answer true if the receiver is the trivial submodule {0}."
	^ self generators allSatisfy: [:each| each isZero]
]

{ #category : #accessing }
Module >> null [
	"Answer the trivial submodule, i.e. the zero object in the category of R-modules."
	^ self ambient span: #()
]

{ #category : #converting }
Module >> over: aRing [
	"Answer the change of base ring of the receiver."
	self notYetImplemented
]

{ #category : #accessing }
Module >> presentationMap [
	"Answer a presentation map of the receiver, the map R^n -> R^m from the presentation exact sequence R^n -> R^m -> M -> 0."
	^ self propertyAt: #presentationMap
]

{ #category : #printing }
Module >> printOn: aStream [
	self isTrivial ifTrue: [aStream nextPut: ${; print: self zero; nextPut: $}. ^ self].
	aStream nextPut: $<.
	self generators do: [:each| aStream print: each] separatedBy: [aStream nextPutAll: '; '].
	aStream nextPut: $>.
	self scalars ~= self ambient scalars ifTrue: [aStream nextPutAll: '_', self scalars printString]
]

{ #category : #operations }
Module >> quot: aModuleOrIdeal [ "˜ "
	"For the receiver N and the argument P two submodules of an R-module M, answer the quotient N : P defined by {a in R | aP is contained in N}.
	For the receiver N, a submodule of an R-module M, and the argument I, an ideal of R, answer the quotient N : I defined by {m in M | I * m is containted in N}."
	self notYetImplemented
]

{ #category : #accessing }
Module >> scalarAction [
	^ (self, self scalars) to: self evaluatingWithArguments: [:x :y| x * y]
]

{ #category : #accessing }
Module >> scalars [
	^ self propertyAt: #scalars ifAbsentPut: [self ambient scalars]
]

{ #category : #'accessing-private' }
Module >> scalars: aRing [
	self propertyAt: #scalars put: aRing
]

{ #category : #morphisms }
Module >> to: aCodomain [
	(aCodomain isModule and: [self isTrivial or: [aCodomain isTrivial]])
		ifTrue: [^ self to: aCodomain evaluating: [:x| aCodomain zero]].
	^ super to: aCodomain
]

{ #category : #morphisms }
Module >> to: aModule evaluating: aBlock [
	aModule isModule ifFalse: [^ super to: aModule evaluating: aBlock].
	aModule scalars = self scalars ifFalse: [DomainError signal].
	^ ModuleMap from: self to: aModule evaluating: aBlock
]

{ #category : #accessing }
Module >> torsion [
	"Answer the torsion submodule of the receiver, i.e. the set of elements e such that exists nonzero integer m with e*m = 0."
	^ self propertyAt: #torsion
]

{ #category : #accessing }
Module >> zero [
	^ self propertyAt: #zero ifAbsentPut: [self == self ambient ifTrue: [self generators anyOne * self scalars zero] ifFalse: [self ambient zero]]
]
