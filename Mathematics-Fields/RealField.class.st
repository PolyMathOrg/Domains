"
The singletion global instance RR is the field of real numbers.
"
Class {
	#name : #RealField,
	#superclass : #Ring,
	#category : #'Mathematics-Fields'
}

{ #category : #initialization }
RealField class >> initialize [
	super initialize.
	Smalltalk at: #RR put: self new
]

{ #category : #comparing }
RealField >> < aDomain [
	^ ((aDomain isKindOf: RationalField) or: [aDomain isKindOf: RationalIntegerRing]) or: [super < aDomain]
]

{ #category : #comparing }
RealField >> = anObject [
	^ anObject class == self class
]

{ #category : #comparing }
RealField >> > aDomain [
	^ (aDomain isKindOf: RationalField) or: [aDomain isKindOf: RationalIntegerRing]
]

{ #category : #operations }
RealField >> algebraicClosure [
	^ CC
]

{ #category : #accessing }
RealField >> characteristic [
	^ 0
]

{ #category : #enumerating }
RealField >> do: aBlock [
	^ self shouldNotImplement
]

{ #category : #morphisms }
RealField >> embed: anObject [
	(anObject isInteger or: [anObject isFraction]) ifTrue: [^ anObject].
	^ super embed: anObject
]

{ #category : #comparing }
RealField >> hash [
	^ self class hash
]

{ #category : #testing }
RealField >> includes: anObject [
	^ anObject isReal
]

{ #category : #testing }
RealField >> isField [
	^ true
]

{ #category : #testing }
RealField >> isFinite [
	^ false
]

{ #category : #testing }
RealField >> isLocalField [
	^ true
]

{ #category : #testing }
RealField >> isReal [
	^ true
]

{ #category : #accessing }
RealField >> one [
	^ 1
]

{ #category : #printing }
RealField >> printOn: aStream [
	aStream nextPut: $ℝ
]

{ #category : #accessing }
RealField >> size [
	^ Aleph new: 0
]

{ #category : #accessing }
RealField >> zero [
	^ 0
]
