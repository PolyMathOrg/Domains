Class {
	#name : #CoxeterDiagram,
	#superclass : #Object,
	#instVars : [
		'matrix'
	],
	#category : #'Mathematics-Etc-Lie'
}

{ #category : #'as yet unclassified' }
CoxeterDiagram >> gramMatrix [
	^ matrix collect: [:x| -2 * (Float pi / x) cos]
]

{ #category : #'as yet unclassified' }
CoxeterDiagram >> isConnected [
	^ self notYetImplemented
]

{ #category : #'as yet unclassified' }
CoxeterDiagram >> isElliptic [
	^ self notYetImplemented
]

{ #category : #'as yet unclassified' }
CoxeterDiagram >> isHyperbolic [
	^ (self gramMatrix spectrum count: [:each| each negative]) = 1
]

{ #category : #'as yet unclassified' }
CoxeterDiagram >> isLannerDiagram [
	^ self isConnected and: [self isElliptic not and: [self gramMatrix determinant < 0]]
]

{ #category : #'as yet unclassified' }
CoxeterDiagram >> isParabolic [
	| spectrum |
	spectrum := self gramMatrix spectrum.
	^ (spectrum occurrencesOf: 0) = 1 and: [spectrum allSatisfy: [:each| each >= 0]]
]
