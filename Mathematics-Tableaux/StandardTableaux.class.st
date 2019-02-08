Class {
	#name : #StandardTableaux,
	#superclass : #SemistandardTableaux,
	#category : #'Mathematics-Tableaux'
}

{ #category : #'as yet unclassified' }
StandardTableaux >> size [
	| answer Y |
	answer := alphabet size factorial.
	Y := self diagram.
	Y do: [ :each | answer := answer / (Y hookLengthAt: each) ].
	^ answer 
]
