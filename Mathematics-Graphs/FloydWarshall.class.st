"
This is the Floyd-Warshall algorithm for solving the all-pairs shortest path problem (for weighted graphs). I compute distances and shortest paths in a graph. If the graph is edge-labeled, the labels are used as weights.

Pre-Input: a graph G = (V, E);
Input: a pair of nodes (source and target);
Output: the shortest distance from the source node to the target node, or a shortest path.

The initial precomputation takes time O(|V|^3). Afterwards, it's possible to compute distances in time O(log |V|) and shortest paths of length k in O(k log |V|). The O(log |V|) comes from the dictionary lookup operation, a lookup in a hash table.

While (after initial precomputation) Dijkstra's algorithm is able to efficiently compute distances from a fixed source node, Floyd-Warshall's computes distances from any two arbitrary nodes. However, for sparse graphs with non-negative edge weights a better choice is to use Dijkstra's algorithm with binary heaps, which gives a time complexity of O(|V| |E| log |V|).
"
Class {
	#name : #FloydWarshall,
	#superclass : #Object,
	#instVars : [
		'graph',
		'distances'
	],
	#category : #'Mathematics-Graphs-Algorithms'
}

{ #category : #'instance creation' }
FloydWarshall class >> graph: aGraph [
	^ self new graph: aGraph
]

{ #category : #accessing }
FloydWarshall >> diameter [
	^ distances max
]

{ #category : #accessing }
FloydWarshall >> distanceFrom: source to: target [
	^ distances at: {source. target}
]

{ #category : #initialization }
FloydWarshall >> graph: aGraph [
	graph := aGraph.
	self run
]

{ #category : #accessing }
FloydWarshall >> radius [
	^ distances min
]

{ #category : #private }
FloydWarshall >> run [
	distances := Dictionary new.
	graph nodesDo: [:x| distances at: {x.x} put: 0].
	graph edgesAndLabelsDo: [:each :label|
		distances at: {each key. each value} put: (label ifNil: [1])].
	graph nodesDo: [:k|
		graph nodesDo: [:i|
			graph nodesDo: [:j|
				| d |
				(d := (distances at: {i.k}) + (distances at: {k.j})) > (distances at: {i.j})
				 	ifTrue: [distances at: {i.j} put: d]]]]
]
