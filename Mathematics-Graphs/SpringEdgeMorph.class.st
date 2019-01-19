Class {
	#name : #SpringEdgeMorph,
	#superclass : #GraphEdgeMorph,
	#instVars : [
		'desiredDistance'
	],
	#category : #'Mathematics-Graphs-Morphic'
}

{ #category : #moving }
SpringEdgeMorph >> approachNodes [
	"Connected nodes are tied with a rubber band."
	| f currentDistance diff delta |
	(currentDistance := (diff := source x + source dx - target x - target dx) norm) > desiredDistance
		ifTrue:
			[f := (desiredDistance - currentDistance) asFloat / (currentDistance * 4).
			delta := diff * f / 2.
			target dx: target dx - delta.
			source dx: source dx + delta]
]

{ #category : #moving }
SpringEdgeMorph >> desiredDistance [
	^ desiredDistance
]

{ #category : #moving }
SpringEdgeMorph >> desiredDistance: anInteger [
	"Set the distance I want between my vertices."
	desiredDistance := anInteger
]

{ #category : #initialization }
SpringEdgeMorph >> initialize [
	super initialize.
	desiredDistance := 100
]

{ #category : #stepping }
SpringEdgeMorph >> step [
	(source owner isNil or: [target owner isNil]) ifTrue: [^ self delete].
"	self approachNodes."
	self adjustBounds
]

{ #category : #stepping }
SpringEdgeMorph >> wantsSteps [
	^ false
]
