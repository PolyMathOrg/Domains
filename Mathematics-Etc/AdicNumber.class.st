Class {
	#name : #AdicNumber,
	#superclass : #Number,
	#instVars : [
		'numerator',
		'valuation'
	],
	#category : #'Mathematics-Etc-Fields-PAdics'
}

{ #category : #accessing }
AdicNumber >> denominator [
	^ numerator parent embed: ((self p) raisedTo: valuation)
]

{ #category : #'as yet unclassified' }
AdicNumber >> embed: aNumber [
	aNumber isInteger ifTrue: [^ self integers embed: aNumber].
	aNumber isFraction ifFalse: [self notYetImplemented].
	self notYetImplemented
]

{ #category : #accessing }
AdicNumber >> norm [
	^ self isZero ifTrue: [0] ifFalse: [(self p) raisedTo: (self valuation negated)]
]

{ #category : #accessing }
AdicNumber >> numerator [
	^ numerator
]

{ #category : #accessing }
AdicNumber >> p [
	^ numerator p
]

{ #category : #accessing }
AdicNumber >> valuation [
	"Answer the p-adic absolute value of the receiver."
	^ valuation
]
