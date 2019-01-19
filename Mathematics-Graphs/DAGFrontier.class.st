"
A DAGFrontier is used to iterate a directed acyclic graph (DAG) respecting the dependencies between nodes.  A client does not create it directly, but sends the message ""frontier"" to the DAG in question.

At any moment it holds a ""frontier"" of nodes that can be accessed.  When any node in the frontier has been processed, it can be removed from the frontier, and the frontier will be updated if necessary (in situ).

Instance variables:
frontier		<Set> of nodes on the frontier, empty if the whole DAG has been enumerated.
bag		<Bag> of nodes, used to calculate updates to the frontier.

Clients of this class must *not* modify the frontier set, only access it.

"
Class {
	#name : #DAGFrontier,
	#superclass : #Object,
	#instVars : [
		'frontier',
		'bag'
	],
	#category : #'Mathematics-Graphs-Algorithms'
}

{ #category : #'instance creation' }
DAGFrontier class >> on: rootedGraph [
	"Create a frontier object to enumerate the graph."
	| remaining frontier |
	"Build a Bag of non-root nodes, each node once in the Bag for every predecessor."
	frontier := rootedGraph rootNodes asOrderedCollection.
	remaining := Bag new.
	rootedGraph nodesDo: [:node| node neighborsDo: [:n| remaining add: n]].
	^ self new frontier: frontier bag: remaining
]

{ #category : #accessing }
DAGFrontier >> frontier [
	^frontier
]

{ #category : #initialization }
DAGFrontier >> frontier: f bag: remaining [
	frontier := f.
	bag := remaining
]

{ #category : #advancing }
DAGFrontier >> remove: frontierObject [
	frontier remove: frontierObject.
	frontierObject neighborsDo:
		[ :neighbor |
			(bag remove: neighbor) = 0
				ifTrue: [frontier add: neighbor]].
	^frontierObject
]

{ #category : #advancing }
DAGFrontier >> removeAll: collection [
	collection do: [ :n | self remove: n]
]
