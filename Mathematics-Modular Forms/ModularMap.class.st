Class {
	#name : #ModularMap,
	#superclass : #LinearFractionalMap,
	#category : #'Mathematics-Modular Forms'
}

{ #category : #'as yet unclassified' }
ModularMap >> asMatrix [
	^ ZZ matrix: 2 coefficients: {a. b. c. d}
]

{ #category : #'as yet unclassified' }
ModularMap >> isElliptic [
	^ self trace abs < 2
]

{ #category : #'as yet unclassified' }
ModularMap >> isHyperbolic [
	^ self trace abs > 2
]

{ #category : #'as yet unclassified' }
ModularMap >> isParabolic [
	^ self trace abs = 2
]
