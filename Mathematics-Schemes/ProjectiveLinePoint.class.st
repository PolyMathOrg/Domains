"
Points on the projective line P^1(R) for some ring R. See also ProjectiveLine.
"
Class {
	#name : #ProjectiveLinePoint,
	#superclass : #ProjectivePoint,
	#category : #'Mathematics-Schemes-Projective'
}

{ #category : #arithmetic }
ProjectiveLinePoint >> * aCusp [
	self isInfinity ifTrue: [aCusp isZero ifTrue: [DomainError signal: 'undefined'] ifFalse: [^ self]].
	aCusp isInfinity ifTrue: [self isZero ifTrue: [DomainError signal: 'undefined'] ifFalse: [^ aCusp]].
	^ self shallowCopy coordinates: (self scalars tuple: {self value * aCusp value. self scalars one})
]

{ #category : #arithmetic }
ProjectiveLinePoint >> + aCusp [
	self isInfinity ifTrue: [^ self].
	aCusp isInfinity ifTrue: [^ aCusp].
	^ self shallowCopy coordinates: (self scalars tuple: {self value + aCusp value. self scalars one})
]

{ #category : #arithmetic }
ProjectiveLinePoint >> - aCusp [
	^ self + aCusp negated
]

{ #category : #arithmetic }
ProjectiveLinePoint >> / aCusp [
	^ self * aCusp reciprocal
]

{ #category : #accessing }
ProjectiveLinePoint >> denominator [
	self isInfinity ifTrue: [^ 0].
	^ self value denominator
]

{ #category : #accessing }
ProjectiveLinePoint >> infinity [
	^ self shallowCopy coordinates: (self scalars tuple: {self scalars one. self scalars zero})
]

{ #category : #testing }
ProjectiveLinePoint >> isInfinity [
	^ (self coordinates at: 2) isZero
]

{ #category : #arithmetic }
ProjectiveLinePoint >> isZero [
	^ self isInfinity not and: [self value isZero]
]

{ #category : #arithmetic }
ProjectiveLinePoint >> negated [
	self isInfinity ifTrue: [^ self].
	^ self shallowCopy coordinates: (self scalars tuple: {self value negated. self scalars one})
]

{ #category : #accessing }
ProjectiveLinePoint >> numerator [
	self isInfinity ifTrue: [^ Infinity projective].
	^ self value numerator
]

{ #category : #accessing }
ProjectiveLinePoint >> one [
	^ self shallowCopy coordinates: (self scalars tuple: {self scalars one. self scalars one})
]

{ #category : #printing }
ProjectiveLinePoint >> printOn: aStream [
	self isInfinity
		ifTrue: [aStream nextPut: Character infinity]
		ifFalse: [aStream print: self value]
]

{ #category : #arithmetic }
ProjectiveLinePoint >> raiseTo: anInteger [
	"Answer the receiver raised to the power anInteger."
	anInteger = 1 ifTrue: [^ self].
	anInteger = 0 ifTrue: [^ self one].
	anInteger < 0 ifTrue: [^ 'self reciprocal ^ anInteger negated'].
	^ '(self squared ^ (anInteger // 2)) * (self ^ (anInteger \\ 2))'
]

{ #category : #arithmetic }
ProjectiveLinePoint >> reciprocal [
	self isInfinity ifTrue: [^ self zero].
	self isZero ifTrue: [^ self infinity].
	^ self shallowCopy coordinates: (self scalars tuple: {self value reciprocal. self scalars one})
]

{ #category : #accessing }
ProjectiveLinePoint >> value [
	^ self coordinates at: 1
]

{ #category : #accessing }
ProjectiveLinePoint >> zero [
	^ self shallowCopy coordinates: (self scalars tuple: {self scalars zero. self scalars one})
]
