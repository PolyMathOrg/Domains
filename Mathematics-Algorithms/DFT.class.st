Class {
	#name : #DFT,
	#superclass : #Object,
	#instVars : [
		'ring',
		'n',
		'alpha'
	],
	#category : #'Mathematics-Algorithms'
}

{ #category : #'as yet unclassified' }
DFT >> value: aTuple [
	^ ring tuple: n evaluating: [:k| (1 to: n) sum: [:j| (aTuple at: j) * (alpha  raiseTo: (j*k))]]
]
