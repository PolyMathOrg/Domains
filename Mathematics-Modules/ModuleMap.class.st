"
Homomorphisms of modules. See Module.
"
Class {
	#name : #ModuleMap,
	#superclass : #Function,
	#category : #'Mathematics-Modules'
}

{ #category : #comparing }
ModuleMap >> = anObject [
	(anObject isKindOf: ModuleMap) ifFalse: [^ super = anObject].
	(anObject domain = self domain and: [anObject codomain = self codomain])
		ifFalse: [^ false].
	^ (self domain generators ifNil: [self domain]) allSatisfy: [:each| (self value: each) = (anObject value: each)]
]

{ #category : #converting }
ModuleMap >> asAbelianGroupHomomorphism [
	^ self domain asAbelianGroup to: self codomain asAbelianGroup evaluating: self
]

{ #category : #operations }
ModuleMap >> directSum: aModuleMap [
	"Answer the direct sum of the receiver and the argument."
	^ self class
		from: self domain directSum: aModuleMap domain
		to: self codomain directSum: aModuleMap codomain
		evaluating: [:x| {self value: (x at: 1). aModuleMap value: (x at: 2)}]
]

{ #category : #operations }
ModuleMap >> image [
	^ self propertyAt: #image ifAbsentPut: [self codomain span: (self domain generators collect: [:each| self value: each])]
]

{ #category : #testing }
ModuleMap >> is: aSymbol [
	^ aSymbol == #ModuleHomomorphism or: [super is: aSymbol]
]

{ #category : #testing }
ModuleMap >> isIdempotent [
	^ self isEndomorphism and: [self î self = self]
]

{ #category : #testing }
ModuleMap >> isIdentity [
	self isEndomorphism ifFalse: [^ false].
	^ (self domain generators ifNil: [self domain]) allSatisfy: [:each| (self value: each) = each]
]

{ #category : #testing }
ModuleMap >> isProjection [
	^ self isIdempotent
]

{ #category : #testing }
ModuleMap >> isTrivial [
	^ self isZero
]

{ #category : #testing }
ModuleMap >> isZero [
	^ self domain generators allSatisfy: [:each| (self value: each) isZero]
]

{ #category : #printing }
ModuleMap >> printOn: aStream [
	self isIdentity ifTrue: [aStream nextPutAll: 'id'. ^ self].
	self negated isIdentity ifTrue: [aStream nextPutAll: '-id'. ^ self].
	self isZero ifTrue: [aStream nextPut: $0. ^ self].
	super printOn: aStream
]

{ #category : #private }
ModuleMap >> species [
	^ ModuleMap
]
