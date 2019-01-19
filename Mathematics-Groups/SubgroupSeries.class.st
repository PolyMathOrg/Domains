Class {
	#name : #SubgroupSeries,
	#superclass : #Object,
	#instVars : [
		'subgroups'
	],
	#category : #'Mathematics-Groups'
}

{ #category : #accessing }
SubgroupSeries >> add: aSubgroup [
	^ self subgroups add: aSubgroup
]

{ #category : #accessing }
SubgroupSeries >> at: anInteger [
	^ self subgroups at: anInteger
]

{ #category : #enumerating }
SubgroupSeries >> do: aBlock [
	self subgroups do: aBlock
]

{ #category : #initialization }
SubgroupSeries >> initialize [
	self subgroups: OrderedCollection new
]

{ #category : #testing }
SubgroupSeries >> isAbelian [
	"Answer true if the receiver is an abelian tower of subgroups."
	self isNormal ifFalse: [^ false].
	2 to: self size do: [ :each | ((self at: each - 1) / (self at: each)) isAbelian ifFalse: [^ false]].
	^ true
]

{ #category : #testing }
SubgroupSeries >> isCyclic [
	"Answer true if the receiver is a cyclic tower of subgroups."
	self isNormal ifFalse: [^ false].
	2 to: self size do: [ :each | ((self at: each - 1) / (self at: each)) isCyclic ifFalse: [^ false]].
	^ true
]

{ #category : #testing }
SubgroupSeries >> isNormal [
	"Answer true if the receiver is a normal tower of subgroups."
	2 to: self size do: [ :each | ((self at: each) isNormalIn: (self at: each - 1)) ifFalse: [^ false]].
	^ true
]

{ #category : #accessing }
SubgroupSeries >> objects [
	^ subgroups
]

{ #category : #accessing }
SubgroupSeries >> size [
	^ subgroups size
]

{ #category : #accessing }
SubgroupSeries >> subgroups [
	^ subgroups
]

{ #category : #'accessing-private' }
SubgroupSeries >> subgroups: aCollection [
	subgroups := aCollection
]
