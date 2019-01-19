Class {
	#name : #CoxeterSystem,
	#superclass : #Domain,
	#instVars : [
		'group',
		'generators',
		'matrix',
		'diagram'
	],
	#category : #'Mathematics-Etc-Lie'
}

{ #category : #'as yet unclassified' }
CoxeterSystem >> computeDiagram [
	| n graph |
	n := matrix width.
	graph := Graph unorderedLabeled.
	graph addAll: (1 to: n).
	1 to: n do: [:i|
		1 to: n do: [:j|
			| m |
			m := matrix at: i@j.
			m = 3 ifTrue: [graph addEdgeFrom: i to: j label: nil].
			m > 3 ifTrue: [graph addEdgeFrom: i to: j label: m]]].
	^ graph
]

{ #category : #'as yet unclassified' }
CoxeterSystem >> diagram [
	^ diagram ifNil: [diagram := self computeDiagram]
]

{ #category : #'as yet unclassified' }
CoxeterSystem >> diagram: aGraph [
	diagram := aGraph
]

{ #category : #'as yet unclassified' }
CoxeterSystem >> matrix [
	^ matrix ifNil: [matrix := self computeMatrix]
]

{ #category : #'as yet unclassified' }
CoxeterSystem >> matrix: aMatrix [
	matrix := aMatrix
]

{ #category : #'as yet unclassified' }
CoxeterSystem >> presentation [
	| generators relators |
	generators := self diagram values collect: [:each| Word x: each].
	relators := OrderedCollection new.
	'self diagram edgesAndLabelsDo: [:each :label|
			label isInfinity
				ifFalse: [relators add: (Word x: each key) * (Word x: each value) ^ (label ifNil: [3])]]'.
	^ GroupPresentation generators: generators relators: relators
]

{ #category : #'as yet unclassified' }
CoxeterSystem >> reflections [
	"Answer the conjugates of the generators."
	^ self notYetImplemented
]

{ #category : #'as yet unclassified' }
CoxeterSystem >> schlafliMatrix [
	^ self matrix collect: [:x| -2 * (Float pi / x) cos]
]

{ #category : #'as yet unclassified' }
CoxeterSystem >> simpleReflections [
	^ generators
]
