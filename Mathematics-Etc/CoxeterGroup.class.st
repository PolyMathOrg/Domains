Class {
	#name : #CoxeterGroup,
	#superclass : #Group,
	#instVars : [
		'diagram'
	],
	#category : #'Mathematics-Etc-Lie'
}

{ #category : #'as yet unclassified' }
CoxeterGroup class >> diagram: aGraph [
	^ self new diagram: aGraph
]

{ #category : #'as yet unclassified' }
CoxeterGroup class >> matrix: aMatrix [
	| n graph |
	n := aMatrix width.
	graph := Graph unorderedLabeled.
	graph addAll: (1 to: n).
	1 to: n do: [:i|
		1 to: n do: [:j|
			| m |
			m := aMatrix at: i@j.
			m = 3 ifTrue: [graph addEdgeFrom: i to: j label: nil].
			m > 3 ifTrue: [graph addEdgeFrom: i to: j label: m]]].
	^ self diagram: graph
]

{ #category : #'as yet unclassified' }
CoxeterGroup >> diagram [
	^ diagram
]

{ #category : #'as yet unclassified' }
CoxeterGroup >> diagram: aGraph [
	diagram := aGraph
]

{ #category : #'as yet unclassified' }
CoxeterGroup >> gramMatrix [
	^ self matrix collect: [:x| -2 * (Float pi / x) cos]
]

{ #category : #'as yet unclassified' }
CoxeterGroup >> isHyperbolic [
	^ (self gramMatrix spectrum count: [:each| each negative]) = 1
]

{ #category : #'as yet unclassified' }
CoxeterGroup >> presentation [
	| generators relators |
	generators := diagram values collect: [:each| Word x: each].
	relators := OrderedCollection new.
	'diagram edgesAndLabelsDo: [:each :label|
			label isInfinity
				ifFalse: [relators add: (Word x: each key) * (Word x: each value) ^ (label ifNil: [3])]]'.
	^ GroupPresentation generators: generators relators: relators
]
