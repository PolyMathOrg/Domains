Class {
	#name : #SchreierSims,
	#superclass : #Object,
	#instVars : [
		'action',
		'generators',
		'base',
		'strongGeneratingSet',
		'trees',
		'order'
	],
	#category : #'Mathematics-Groups-Algorithms'
}

{ #category : #'accessing-private' }
SchreierSims >> action: aGroupAction [
	action := aGroupAction
]

{ #category : #accessing }
SchreierSims >> base [
	"A base of a group G acting on X is a finite sequence of distinct points B={x1,..,xn} such that the stabilizer of B is {id}, i.e. the only element that fixes all xi is the identity."
	base ifNil: [self run].
	^ base
]

{ #category : #'computing-private' }
SchreierSims >> buildBSGS [
	base := OrderedCollection new.
	strongGeneratingSet := OrderedCollection new.
	self buildPartialBSGS.
	base size to: 1 by: -1 do: [:i| self schreierSimsStep: i]
]

{ #category : #'computing-private' }
SchreierSims >> buildPartialBSGS [
	| id |
	id := action group identity.
	generators do: [:each| each = id ifFalse: [strongGeneratingSet add: each]].
	strongGeneratingSet copy do: [:s|
		(base allSatisfy: [:b| (s value: b) = b])
			ifTrue: [base add: (action space detect: [:one| action isFixedPoint: one])].
			s squared = id ifFalse: [base add: s inverse]]
]

{ #category : #computing }
SchreierSims >> elementFromImage: anArray [
	| image g |
	image := anArray copy.
	g := action group identity.
	trees withIndexDo: [:each :i|
		g := (each trace: (image at: i)) * g.
		i to: base size do: [:j| image at: j put: (action value: {each traceInverse: (image at: i). image at: j})]].
	^ g
]

{ #category : #'accessing-private' }
SchreierSims >> generators: aCollection [
	generators := aCollection asArray
]

{ #category : #computing }
SchreierSims >> imageOf: anElement [
	^ base collect: [:each| action value: {anElement. each}]
]

{ #category : #computing }
SchreierSims >> includes: anElement [
	"Answer true if the group includes anElement."
	^ (self strip: anElement) = action group identity
]

{ #category : #accessing }
SchreierSims >> order [
	"Answer the order of the group."
	order ifNil: [self run].
	^ order
]

{ #category : #'computing-private' }
SchreierSims >> run [
	| G |
	G := action group.
	order := 1.
	base := OrderedCollection new.
	strongGeneratingSet := OrderedCollection new.
	trees := OrderedCollection new.
	G action space do: [:b| | tree |
		G isTrivial ifTrue: [^ order].
		tree := SchreierTree root: b generators: G generators action: G action.
		trees add: tree.
		order := order * tree orbit size.
		G := tree stabilizer].
	self error: 'what?'.
	^ order
]

{ #category : #computing }
SchreierSims >> strip: anElement [
	| g |
	g := anElement.
	trees withIndexDo: [:each :i| | b b2 |
		b := each root.
		b2 := action value: {g. b}.
		(each orbits includes: b2)
			ifFalse: [^ {g. i}].
		g := g * (each traceInverse: b2)].
	^ {g. trees size + 1}
]

{ #category : #accessing }
SchreierSims >> strongGeneratingSet [
	strongGeneratingSet ifNil: [self run].
	^ strongGeneratingSet
]
