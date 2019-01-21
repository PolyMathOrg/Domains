"
Finite index subgroups of the modular group.
"
Class {
	#name : #ArithmeticGroup,
	#superclass : #TransformationGroup,
	#category : #'Mathematics-Modular Group'
}

{ #category : #'as yet unclassified' }
ArithmeticGroup >> action [
	^ GroupAction
		from: self , CC
		to: CC
		evaluating: [ :f :z | f value: z ]
]

{ #category : #'as yet unclassified' }
ArithmeticGroup >> ambient [
	^ ModularGroup new
]

{ #category : #'as yet unclassified' }
ArithmeticGroup >> identity [
	^ ModularMap I
]

{ #category : #'as yet unclassified' }
ArithmeticGroup >> orderOf: aModularMap [
	| trace |
	aModularMap isIdentity ifTrue: [^ 1].
	"aModularMap negated isIdentity ifTrue: [^ 2]."
	trace := aModularMap trace.
	(trace <= -2 or: [trace >= 2]) ifTrue: [^ Infinity positive].
	trace == 1 ifTrue: [^ 6].
	trace == -1 ifTrue: [^ 3].
	"trace == 0"
	^ 4
]

{ #category : #'as yet unclassified' }
ArithmeticGroup >> size [
	^ Aleph new
]

{ #category : #'as yet unclassified' }
ArithmeticGroup >> upperHalfPlaneAction [
	^ GroupAction
		from: self , HH
		to: HH
		evaluating: [ :f :z | f value: z ]
]
