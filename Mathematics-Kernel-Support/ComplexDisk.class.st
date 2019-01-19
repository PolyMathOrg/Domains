"
Closed disks in the complex plane, defined by a center point and a radius.
"
Class {
	#name : #ComplexDisk,
	#superclass : #Domain,
	#instVars : [
		'center',
		'radius'
	],
	#category : #'Mathematics-Kernel-Support'
}

{ #category : #'instance creation' }
ComplexDisk class >> center: aComplex radius: aNumber [
	^ self new center: aComplex; radius: aNumber
]

{ #category : #arithmetic }
ComplexDisk >> * aDisk [
	^ self class center: aDisk center * self center radius: self radius * aDisk radius
]

{ #category : #arithmetic }
ComplexDisk >> + aDisk [
	^ self class center: aDisk center + self center radius: self radius + aDisk radius
]

{ #category : #accessing }
ComplexDisk >> center [
	^ center
]

{ #category : #'accessing-private' }
ComplexDisk >> center: aComplex [
	center := aComplex
]

{ #category : #accessing }
ComplexDisk >> enclosingBox [
	"Answer a ComplexBox that encloses the receiver."
	^ ComplexBox center: self center radius: self radius
]

{ #category : #testing }
ComplexDisk >> includes: anObject [
	^ (anObject - center) norm2 <= radius squared
]

{ #category : #testing }
ComplexDisk >> intersects: aBall [
	self flag: #fix.
	^ (aBall center - center) norm2 <= (self radius + aBall radius) squared
]

{ #category : #accessing }
ComplexDisk >> midpoint [
	^ self center
]

{ #category : #printing }
ComplexDisk >> printOn: aStream [
	aStream nextPutAll: 'D('; print: self center; nextPut: $,; print: self radius; nextPut: $)
]

{ #category : #accessing }
ComplexDisk >> radius [
	^ radius
]

{ #category : #'accessing-private' }
ComplexDisk >> radius: aNumber [
	radius := aNumber
]
